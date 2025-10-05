% Predicados para fatos atômicos (FOL: ∀ Bloco, Pos, etc.)
on(Bloco, Sobre).  % Ex.: on(a, table) ou on(b, a)
position(Bloco, Pos).  % Pos in 0..6
level(Bloco, Nivel).  % Nivel in 0..10
clear(Bloco).  % Nada sobre o Bloco
occupied(Pos).  % Pos ocupada por algum bloco na mesa
size(Bloco, Tam).  % Tam fixo: size(a,1), etc.

% Estado é uma lista de fatos
estado(S) :- is_list(S).

% Exemplo de estado inicial (do INIT no SMV)
initial_state([on(a, table), position(a, 2), level(a, 0),
               on(b, d), position(b, 3), level(b, 2),
               on(c, table), position(c, 0), level(c, 0),
               on(d, a), position(d, 2), level(d, 1),
               size(a,1), size(b,1), size(c,1), size(d,2)]).

% Definições computadas (como DEFINE no SMV)
clear(Bloco, S) :- \+ member(on(_, Bloco), S).  % FOL: ¬∃ X on(X, Bloco)

occupied(Pos, S) :- 
    member(on(Bloco, table), S),
    member(position(Bloco, BPos), S),
    member(size(Bloco, Tam), S),
    BPos =< Pos, Pos =< BPos + Tam - 1.

% Objetivo (goal no SMV)
goal_state([on(a, table), position(a, 0),
            on(c, a), position(c, 0),
            on(d, c), position(d, 0),
            on(b, d), position(b, 1)]).
			
% Ações possíveis (enum move no SMV)
action(move(Bloco, De, Para)) :- bloco(Bloco), pos_ou_bloco(De), pos_ou_bloco(Para), De \= Para.

bloco(B) :- member(B, [a,b,c,d]).
pos_ou_bloco(table_Pos) :- between(0,6,Pos); bloco(Pos).

% Pré-condições: can(Acao, Estado) - com vacância e estabilidade
can(move(Bloco, De, Para), S) :-
    member(on(Bloco, De), S),
    clear(Bloco, S),
    clear_destino(Para, S),
    vacant_horizontal(Bloco, Para, S),
    stable(Bloco, Para, S).

clear_destino(table_Pos, S) :- \+ occupied(Pos, S).  % Para table_Pos
clear_destino(DestBloco, S) :- clear(DestBloco, S).  % Para outro bloco

vacant_horizontal(Bloco, Para, S) :-
    member(size(Bloco, Tam), S),
    (Para = table_Pos ->  % Move para mesa
        forall(between(0, Tam-1, Offset), \+ occupied(Pos + Offset, S))
    ; Para = DestBloco ->  % Move para bloco (vacância horizontal implícita via position)
        member(position(DestBloco, DPos), S),
        member(size(DestBloco, DTam), S),
        member(position(Bloco, BPos), S),
        BPos >= DPos, BPos + Tam -1 =< DPos + DTam -1
    ).

stable(Bloco, Para, S) :- 
    Para = DestBloco,  % Só para pilhas
    member(size(Bloco, BTam), S),
    member(size(DestBloco, DTam), S),
    BTam =< DTam,  % Bloco menor ou igual sobre maior
    member(position(DestBloco, DPos), S),
    Delta = DTam - BTam,
    Offset = case(Delta >= 0, Delta / 2, (Delta -1) / 2),  % Centro de massa (como no SMV)
    Offset >= 0, Offset + BTam -1 =< DTam -1.  % Estável se centro alinhado

% Adições e Deleções (adds/deletes no SMV via next)
adds(move(Bloco, De, Para), [on(Bloco, Para), clear(De), position(Bloco, NewPos), level(Bloco, NewLevel)]) :-
    % Calcula NewPos e NewLevel baseado em Para (similar a next no SMV)
    (Para = table_Pos -> NewPos = Pos, NewLevel = 0
    ; Para = DestBloco -> member(position(DestBloco, DPos), S), NewPos = DPos + Offset, member(level(DestBloco, DLevel), S), NewLevel = DLevel +1).

deletes(move(Bloco, De, Para), [on(Bloco, De), clear(Para), position(Bloco, OldPos), level(Bloco, OldLevel)]).

% Aplica ação: apply(Acao, Estado, NovoEstado)
apply(A, S, S1) :- deletes(A, D), subtract(S, D, S2), adds(A, A1), append(S2, A1, S1).

% Invariante: Sem colisões em mesmo nível e posição sobreposta
valid_state(S) :-
    forall((bloco(B1), bloco(B2), B1 \= B2),
           (member(level(B1, L), S), member(level(B2, L), S) -> 
            \+ (member(position(B1, P1), S), member(size(B1, S1), S), 
                member(position(B2, P2), S), member(size(B2, S2), S),
                P1 =< P2 + S2 -1, P2 =< P1 + S1 -1))),
    % Sem ciclos (exemplos do INVAR)
    \+ (member(on(a,b), S), member(on(b,a), S)),
    \+ (member(on(a,c), S), member(on(c,a), S)),
    % ... (todos os ! ciclos do SMV)
    % Limites de posição e nível
    forall(bloco(B), (member(position(B, P), S), member(size(B, Tam), S), P >= 0, P + Tam -1 =< 6)),
    forall(bloco(B), (member(level(B, N), S), N =< 10)).
	
% Planejador recursivo (plano(Estado, Goal, Plano))
plano(S, Goal, []) :- subset(Goal, S), valid_state(S).  % Base: goal satisfeito e estado válido

plano(S, Goal, [A|Plan]) :-
    action(A),
    can(A, S),
    apply(A, S, S1),
    valid_state(S1),  % Checa invariantes no novo estado
    plano(S1, Goal, Plan).

% Consulta exemplo: encontre plano do inicial ao goal
consulta_plan :- initial_state(Init), goal_state(Goal), plano(Init, Goal, Plan), write(Plan), nl.
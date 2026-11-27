% Six two-literal disjuncts exceed the hybrid estimate of 32 distributive
% clauses, so the standard hybrid CNF introduces auxiliary predicates here.
fof(choice,axiom,((p1 & q1) | (p2 & q2) | (p3 & q3) | (p4 & q4) | (p5 & q5) | (p6 & q6))).
fof(n1,axiom,~p1).
fof(n2,axiom,~p2).
fof(n3,axiom,~p3).
fof(n4,axiom,~p4).
fof(n5,axiom,~p5).
fof(n6,axiom,~p6).

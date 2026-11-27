% A single instance, for comparison with external ATPs. The fuzzer itself
% enumerates the predicate rather than reading this fixture.
fof(comprehension,axiom,(?[R]: (![X]: (member(X,R) <=> ~member(X,X))))).

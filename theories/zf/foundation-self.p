fof(pairing,axiom,(![A,B]: (?[P]: (![X]: (member(X,P) <=> ((X = A) | (X = B))))))).
fof(foundation,axiom,(![A]: ((?[X]: member(X,A)) => (?[Y]: (member(Y,A) & (![Z]: (member(Z,A) => ~member(Z,Y)))))))).
fof(self_member,axiom,(?[X]: member(X,X))).

% The unit equation f(Y)=Y follows from rule and r only after a resolution
% step, when p(f(X),X) is already Active. Activating the equation rewrites
% that Active clause to p(X,X) by backward demodulation.
fof(old,axiom,(![X]:p(f(X),X))).
fof(rule,axiom,(![Y]:((?[W]:r(Y,W)) => f(Y)=Y))).
fof(r,axiom,(![Z]:r(Z,b))).
fof(n,axiom,~p(a,a)).

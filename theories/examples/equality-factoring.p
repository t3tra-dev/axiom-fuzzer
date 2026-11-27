% Any X and Y satisfy X=a or Y=b, so the domain has a single element and
% p(c) conflicts with ~p(d). The standard search closes it through equality
% factoring of the first axiom.
fof(single,axiom,(![X,Y]:(X=a | Y=b))).
fof(positive,axiom,p(c)).
fof(negative,axiom,~p(d)).

edge(1,2).
edge(2,3).
edge(3,4).
edge(3,5).
path(X,X).
path(X,Y) :- edge(X,Z), path(Z,Y).
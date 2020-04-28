loves(john, wine).
loves(mary, wine).
loves(john, X) :- loves(X, wine).
% ∀X( loves(X, wine) → loves(john, X))
% john, mary, wine

% z, s(z), s(s(z)), s(s(s(z))), ...
% data N = Z | S N

add(z, X, X).
add(s(X), Y, s(Z)) :- add(X, Y, Z).

% add(+X, +Y, -Z)
% add(-X, +Y, +Z)
% add(+X, -Y, +Z)
% add(-X, -Y, +Z)

% []
% [H | T]
% [1,2,3,4] = [1|[2|[3|[4|[]]]]]

mem(X, [X | _]).
mem(X, [_ | T]) :- mem(X, T).

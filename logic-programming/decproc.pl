% Lists
reify(concat(cons(X, XS), L2), cons(X, L)) :- reify(concat(XS, L2), L).
reify(concat(nil, L2), L2).
reify(cons(X, XS), cons(X, L)) :- reify(XS, L).
reify(nil, nil).

% Type constants
constant(nat).

% Types
type(N, const(C)) :- constant(C).
type(N, arrow(T1, T2)).


% Subtyping
% true is for +k, false is for -k

subtype(K, true, type(N, const(C)), type(M, const(C)), cons(lte(N, pl(K, M)), nil), natcoe(N, M, K)).
subtype(K, false, type(N, const(C)), type(M, const(C)), cons(lte(pl(K, N), M), nil), natcoe(N, M, K)).

subtype(K, true, type(N, arrow(T1, T2)), type(M, arrow(T1p, T2p)), cons(lte(N, pl(J, pl(K, M))), concat(L1, L2)), arrowcoe(N, M, K, J, Coe1, Coe2))
  :- subtype(J, true, T1p, T1, L1, Coe1),
     subtype(J, false, T2, T2p, L2, Coe2).

subtype(K, false, type(N, arrow(T1, T2)), type(M, arrow(T1p, T2p)), cons(lte(pl(K, N), pl(M, J)), concat(L1, L2)), arrowcoe(N, M, K, J, Coe1, Coe2))
  :- subtype(J, true, T1p, T1, L1, Coe1),
     subtype(J, false, T2, T2p, L2, Coe2).



% Queries

% :- subtype(0,
%            true,
%            type(1, arrow(type(0, const(nat)), type(0, const(nat)))),
%            type(0, arrow(type(0, const(nat)), type(2, const(nat)))),
%            Constraints,
%            Coercion
%    ),
%    reify(Constraints, SimplifiedConstraints),
%    (
%        nl,
%        write("Coercion: "),
%        writeln(Coercion),
%        write("Constraints: "),
%        writeln(SimplifiedConstraints),
%        nl
%    ).


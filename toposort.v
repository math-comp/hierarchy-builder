From elpi Require Import elpi.

Elpi Program toposort lp:{{

pred toposorted i: list (pair A A), i: list A.
toposorted _ [].
toposorted ES [X|XS] :-
  if (std.exists XS (y\ std.mem ES (pr y X))) fail (toposorted E XS).

%              list of edges       node(s)    visited    progress   visited'   output
pred topovisit i: list (pair A A), i: A,      i: list A, i: list A, o: list A, o: list A.
pred toporec   i: list (pair A A), i: list A, i: list A, i: list A, o: list A, o: list A.
topovisit _ X VS PS VS PS :- std.mem PS X, !.
topovisit _ X VS _ _ _ :- std.mem VS X, !, coq.say "cycle detected.", fail.
topovisit ES X VS PS VS' [X|PS'] :-
  toporec ES {std.map {std.filter ES (e\ fst e X)} snd} [X|VS] PS VS' PS'.
toporec _ [] VS PS VS PS.
toporec ES [X|XS] VS PS VS'' PS'' :-
  topovisit ES X VS PS VS' PS', toporec ES XS VS' PS' VS'' PS''.

pred toposort i: list (pair A A), i: list A, o: list A.
toposort ES XS XS' :- toporec ES XS [] [] _ XS'.

pred run-toposort i: list (pair A A), i: list A.
run-toposort ES XS :-
  toposort ES XS XS', toposorted ES XS', coq.say XS'.

}}.

Elpi Typecheck.

Elpi Query lp:{{
  ES = [pr 7 11, pr 7 8, pr 5 11, pr 3 8, pr 3 10, pr 11 2, pr 11 9, pr 11 10, pr 8 9],
  run-toposort ES [2, 3, 5, 7, 8, 9, 10, 11]
}}.

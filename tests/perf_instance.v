From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_solvable all_field.

Elpi Accumulate HB.instance lp:{{


pred topovisit i: coq.gref.map coq.gref.set, i: classname,      i: coq.gref.set, i: list classname, i: coq.gref.set, o: coq.gref.set, o: list classname, o: coq.gref.set.
topovisit _ X VS PS PSS VS PS PSS :- coq.gref.set.mem X PSS, !.
topovisit _ X VS _ _ _ _ _ :- coq.gref.set.mem X VS, !, halt "cycle detected.".
topovisit ES X VS PS PSS VS' [X|PS'] PSS'' :-
  (coq.gref.map.find X ES M ; coq.gref.set.empty M),
  toporec ES {coq.gref.set.elements M} {coq.gref.set.add X VS} PS PSS VS' PS' PSS',
  coq.gref.set.add X PSS' PSS''.
pred toporec   i: coq.gref.map coq.gref.set, i: list classname, i: coq.gref.set, i: list classname, i: coq.gref.set, o: coq.gref.set, o: list classname, o: coq.gref.set.
toporec _ [] VS PS PSS VS PS PSS.
toporec ES [X|XS] VS PS PSS VS'' PS'' PSS'' :-
  topovisit ES X VS PS PSS VS' PS' PSS', toporec ES XS VS' PS' PSS' VS'' PS'' PSS''.

pred add-to-neighbours i:coq.gref.set, i:pair gref gref, i:coq.gref.map coq.gref.set, o:coq.gref.map coq.gref.set.
add-to-neighbours VS (pr _ V) A A :- not(coq.gref.set.mem V VS), !.
add-to-neighbours _ (pr K V) A A1 :- coq.gref.map.find K A L, !, coq.gref.map.add K {coq.gref.set.add V L} A A1.
add-to-neighbours _ (pr K V) A A1 :- coq.gref.map.add K {coq.gref.set.add V {coq.gref.set.empty} } A A1.

:before "stop:begin"
std.toposort ES XS XS'' :- !, std.do! [
  std.fold XS {coq.gref.set.empty} coq.gref.set.add VS,
  std.fold ES {coq.gref.map.empty} (add-to-neighbours VS) EM,
  toporec EM XS {coq.gref.set.empty} [] {coq.gref.set.empty} _ XS'' _
].


% :before "stop:begin"
% classname ML CLSortedDef :- !, std.do! [
%   classname.unsorted ML [] CL,
%   std.map CL classname->def CLSortedDef,
% ].

% :before "stop:begin"
% std.toposort ES XS XS'' :- !, XS'' = XS.
/*
pred smaller i:classname, i:classname.

:before "stop:begin"
toposort-classes In Out :- !, std.do! [
  std.findall (sub-class C1_ C2_ _ _) SubClasses,
  std.map SubClasses (x\r\ sigma C1 C2 A B\ x = (sub-class C1 C2 A B), r = smaller C1 C2) ES,
  ES => std.time (toposort smaller {std.rev In} [] Out) Time, coq.say "topo" Time
].

pred partition i:list A, i:(A -> prop), o:list A, o:list A.
partition []    _ [] [].
partition [X|L] P R S :- if (P X) (R = X :: L1, S = S1) (R = L1, S = X :: S1), partition L P L1 S1.

:index (_ 1)
pred toposort i:(A -> A -> prop), i:list A, i:list A, o:list A.
toposort _  [] A A.
toposort R [X|Rest] Acc Out :-
  partition Rest (R X) LeX GtX,
  toposort R GtX Acc Right,
  toposort R LeX [X|Right] Out.
/*
pred reversed-kahn i:list (pair A (list A)), i:list A, o:option (list A).
reversed-kahn Bindings Stack SortedNodes :-
  std.map-filter Bindings (p\ n\ p = pr n []) ExitNodes,
  if (ExitNodes = []) (
    if (Bindings = [])
      (SortedNodes = some Stack)
      (SortedNodes = none)
  ) (
    std.map-filter Bindings (p\ p'\ sigma Node Successors Successors'\
      p = pr Node Successors,
      not (std.mem! ExitNodes Node),
      std.filter Successors (s\ not (std.mem! ExitNodes s)) Successors',
      p' = pr Node Successors'
    ) Bindings',
    reversed-kahn Bindings' {std.append ExitNodes Stack} SortedNodes
  ).
*/
*/
}}.
Elpi Typecheck HB.instance.



Axiom T : Type.
Axiom f : T -> T -> bool.
Axiom p : forall x y : T, reflect (x = y) (f x y).

Time HB.instance Definition _ := hasDecEq.Build T p.
Time HB.instance Definition _ := hasDecEq.Build T p.

(*
Finished transaction in 0.816 secs (0.81u,0.s) (successful)


Finished transaction in 0.188 secs (0.188u,0.s) (successful)
time sort 0.014739
time map 0.012572
time set 0.000554
*)



HB.mixin Record M0 T := { f0 : T }.
HB.structure Definition S0 := { T of M0 T }.
HB.mixin Record M1 T of S0 T := { f1 : T }.
HB.structure Definition S1 := { T of M1 T }.
HB.mixin Record M2 T of S1 T := { f2 : T }.
HB.structure Definition S2 := { T of M2 T }.
HB.mixin Record M3 T of S2 T := { f3 : T }.
HB.structure Definition S3 := { T of M3 T }.
HB.mixin Record M4 T of S3 T := { f4 : T }.
HB.structure Definition S4 := { T of M4 T }.
HB.mixin Record M5 T of S4 T := { f5 : T }.
HB.structure Definition S5 := { T of M5 T }.
HB.mixin Record M6 T of S5 T := { f6 : T }.
HB.structure Definition S6 := { T of M6 T }.
HB.mixin Record M7 T of S6 T := { f7 : T }.
HB.structure Definition S7 := { T of M7 T }.
HB.mixin Record M8 T of S7 T := { f8 : T }.
HB.structure Definition S8 := { T of M8 T }.
HB.mixin Record M9 T of S8 T := { f9 : T }.
HB.structure Definition S9 := { T of M9 T }.
HB.mixin Record M10 T of S9 T := { f10 : T }.
HB.structure Definition S10 := { T of M10 T }.

HB.mixin Record N0 T := { g0 : T }.
HB.structure Definition R0 := { T of N0 T }.
HB.mixin Record N1 T of R0 T := { g1 : T }.
HB.structure Definition R1 := { T of N1 T }.
HB.mixin Record N2 T of R1 T := { g2 : T }.
HB.structure Definition R2 := { T of N2 T }.
HB.mixin Record N3 T of R2 T := { g3 : T }.
HB.structure Definition R3 := { T of N3 T }.
HB.mixin Record N4 T of R3 T := { g4 : T }.
HB.structure Definition R4 := { T of N4 T }.
HB.mixin Record N5 T of R4 T := { g5 : T }.
HB.structure Definition R5 := { T of N5 T }.
HB.mixin Record N6 T of R5 T := { g6 : T }.
HB.structure Definition R6 := { T of N6 T }.
HB.mixin Record N7 T of R6 T := { g7 : T }.
HB.structure Definition R7 := { T of N7 T }.
HB.mixin Record N8 T of R7 T := { g8 : T }.
HB.structure Definition R8 := { T of N8 T }.
HB.mixin Record N9 T of R8 T := { g9 : T }.
HB.structure Definition R9 := { T of N9 T }.
HB.mixin Record N10 T of R9 T := { g10 : T }.
HB.structure Definition R10 := { T of N10 T }.

(*
HB.structure Definition X1 := { T of N1 T & M1 T }.
HB.structure Definition X2 := { T of N2 T & M2 T }.
HB.structure Definition X3 := { T of N3 T & M3 T }.
HB.structure Definition X4 := { T of N4 T & M4 T }.
HB.structure Definition X5 := { T of N5 T & M5 T }.
HB.structure Definition X6 := { T of N6 T & M6 T }.
HB.structure Definition X7 := { T of N7 T & M7 T }.
HB.structure Definition X8 := { T of N8 T & M8 T }.
HB.structure Definition X9 := { T of N9 T & M9 T }.
HB.structure Definition X10 := { T of N10 T & M10 T }.
*)

HB.structure Definition X1 := { T of R1 T & S1 T }.
HB.structure Definition X2 := { T of R2 T & S2 T }.
HB.structure Definition X3 := { T of R3 T & S3 T }.
HB.structure Definition X4 := { T of R4 T & S4 T }.
HB.structure Definition X5 := { T of R5 T & S5 T }.
HB.structure Definition X6 := { T of R6 T & S6 T }.
HB.structure Definition X7 := { T of R7 T & S7 T }.
HB.structure Definition X8 := { T of R8 T & S8 T }.
HB.structure Definition X9 := { T of R9 T & S9 T }.
HB.structure Definition X10 := { T of R10 T & S10 T }.

HB.instance Definition _ : M0 nat := M0.Build nat 0.
HB.instance Definition _ : M1 nat := M1.Build nat 0.
HB.instance Definition _ : M2 nat := M2.Build nat 0.
HB.instance Definition _ : M3 nat := M3.Build nat 0.
HB.instance Definition _ : M4 nat := M4.Build nat 0.
HB.instance Definition _ : M5 nat := M5.Build nat 0.
HB.instance Definition _ : M6 nat := M6.Build nat 0.
HB.instance Definition _ : M7 nat := M7.Build nat 0.
HB.instance Definition _ : M8 nat := M8.Build nat 0.
HB.instance Definition _ : M9 nat := M9.Build nat 0.
HB.instance Definition _ : M10 nat := M10.Build nat 0.
HB.instance Definition _ : N0 nat := N0.Build nat 0.
HB.instance Definition _ : N1 nat := N1.Build nat 0.
HB.instance Definition _ : N2 nat := N2.Build nat 0.
HB.instance Definition _ : N3 nat := N3.Build nat 0.
HB.instance Definition _ : N4 nat := N4.Build nat 0.
HB.instance Definition _ : N5 nat := N5.Build nat 0.
HB.instance Definition _ : N6 nat := N6.Build nat 0.
HB.instance Definition _ : N7 nat := N7.Build nat 0.
HB.instance Definition _ : N8 nat := N8.Build nat 0.
HB.instance Definition _ : N9 nat := N9.Build nat 0.

Time HB.instance Definition _ : N10 nat := N10.Build nat 0.

Time HB.instance Definition _ : M0 bool := M0.Build bool true.
Time HB.instance Definition _ : N0 bool := N0.Build bool true.
Time HB.instance Definition _ : M1 bool := M1.Build bool true.
Time HB.instance Definition _ : N1 bool := N1.Build bool true.
Time HB.instance Definition _ : M2 bool := M2.Build bool true.
Time HB.instance Definition _ : N2 bool := N2.Build bool true.
Time HB.instance Definition _ : M3 bool := M3.Build bool true.
Time HB.instance Definition _ : N3 bool := N3.Build bool true.
Time HB.instance Definition _ : M4 bool := M4.Build bool true.
Time HB.instance Definition _ : N4 bool := N4.Build bool true.
Time HB.instance Definition _ : M5 bool := M5.Build bool true.
Time HB.instance Definition _ : N5 bool := N5.Build bool true.
Time HB.instance Definition _ : M6 bool := M6.Build bool true.
Time HB.instance Definition _ : N6 bool := N6.Build bool true.
Time HB.instance Definition _ : M7 bool := M7.Build bool true.
Time HB.instance Definition _ : N7 bool := N7.Build bool true.
Time HB.instance Definition _ : M8 bool := M8.Build bool true.
Time HB.instance Definition _ : N8 bool := N8.Build bool true.
Time HB.instance Definition _ : M9 bool := M9.Build bool true.
Time HB.instance Definition _ : N9 bool := N9.Build bool true.
Time HB.instance Definition _ : M10 bool := M10.Build bool true.
Time HB.instance Definition _ : N10 bool := N10.Build bool true.

Elpi Accumulate HB.instance lp:{{

:before "stop:begin"
instance.infer-class _T  _Class _Struct _MLwP _S _Name _STy _Clauses :- !, fail.
/*
  list-w-params_list MLwP XX,
  not (std.forall XX (x\synthesis.private.mixin-for T x _ )),
  !,
  fail.
*/
}}.
Elpi Typecheck HB.instance.

Elpi Print HB.instance.

(*
#[verbose] HB.mixin Record M13 T of S12 T := { f13 : T }.
#[verbose] HB.structure Definition S13 := { T of M13 T }.
HB.mixin Record M14 T of S13 T := { f14 : T }.
HB.structure Definition S14 := { T of M14 T }.
HB.mixin Record M15 T of S14 T := { f15 : T }.
HB.structure Definition S15 := { T of M15 T }.
HB.mixin Record M16 T of S15 T := { f16 : T }.
HB.structure Definition S16 := { T of M16 T }.
HB.mixin Record M17 T of S16 T := { f17 : T }.
HB.structure Definition S17 := { T of M17 T }.
HB.mixin Record M18 T of S17 T := { f18 : T }.
HB.structure Definition S18 := { T of M18 T }.
HB.mixin Record M19 T of S18 T := { f19 : T }.
HB.structure Definition S19 := { T of M19 T }.
HB.mixin Record M20 T of S19 T := { f20 : T }.
HB.structure Definition S20 := { T of M20 T }.
HB.mixin Record M21 T of S20 T := { f21 : T }.
HB.structure Definition S21 := { T of M21 T }.
HB.mixin Record M22 T of S21 T := { f22 : T }.
HB.structure Definition S22 := { T of M22 T }.
HB.mixin Record M23 T of S22 T := { f23 : T }.
HB.structure Definition S23 := { T of M23 T }.
HB.mixin Record M24 T of S23 T := { f24 : T }.
HB.structure Definition S24 := { T of M24 T }.
HB.mixin Record M25 T of S24 T := { f25 : T }.
HB.structure Definition S25 := { T of M25 T }.
HB.mixin Record M26 T of S25 T := { f26 : T }.
HB.structure Definition S26 := { T of M26 T }.
HB.mixin Record M27 T of S26 T := { f27 : T }.
HB.structure Definition S27 := { T of M27 T }.
HB.mixin Record M28 T of S27 T := { f28 : T }.
HB.structure Definition S28 := { T of M28 T }.
HB.mixin Record M29 T of S28 T := { f29 : T }.
HB.structure Definition S29 := { T of M29 T }.
HB.mixin Record M30 T of S29 T := { f30 : T }.
HB.structure Definition S30 := { T of M30 T }.
HB.mixin Record M31 T of S30 T := { f31 : T }.
HB.structure Definition S31 := { T of M31 T }.
HB.mixin Record M32 T of S31 T := { f32 : T }.
HB.structure Definition S32 := { T of M32 T }.
HB.mixin Record M33 T of S32 T := { f33 : T }.
HB.structure Definition S33 := { T of M33 T }.
HB.mixin Record M34 T of S33 T := { f34 : T }.
HB.structure Definition S34 := { T of M34 T }.
HB.mixin Record M35 T of S34 T := { f35 : T }.
HB.structure Definition S35 := { T of M35 T }.
HB.mixin Record M36 T of S35 T := { f36 : T }.
HB.structure Definition S36 := { T of M36 T }.
HB.mixin Record M37 T of S36 T := { f37 : T }.
HB.structure Definition S37 := { T of M37 T }.
HB.mixin Record M38 T of S37 T := { f38 : T }.
HB.structure Definition S38 := { T of M38 T }.
HB.mixin Record M39 T of S38 T := { f39 : T }.
HB.structure Definition S39 := { T of M39 T }.
HB.mixin Record M40 T of S39 T := { f40 : T }.
HB.structure Definition S40 := { T of M40 T }.
HB.mixin Record M41 T of S40 T := { f41 : T }.
HB.structure Definition S41 := { T of M41 T }.
HB.mixin Record M42 T of S41 T := { f42 : T }.
HB.structure Definition S42 := { T of M42 T }.
HB.mixin Record M43 T of S42 T := { f43 : T }.
HB.structure Definition S43 := { T of M43 T }.
HB.mixin Record M44 T of S43 T := { f44 : T }.
HB.structure Definition S44 := { T of M44 T }.
HB.mixin Record M45 T of S44 T := { f45 : T }.
HB.structure Definition S45 := { T of M45 T }.
HB.mixin Record M46 T of S45 T := { f46 : T }.
HB.structure Definition S46 := { T of M46 T }.
HB.mixin Record M47 T of S46 T := { f47 : T }.
HB.structure Definition S47 := { T of M47 T }.
HB.mixin Record M48 T of S47 T := { f48 : T }.
HB.structure Definition S48 := { T of M48 T }.
HB.mixin Record M49 T of S48 T := { f49 : T }.
HB.structure Definition S49 := { T of M49 T }.
HB.mixin Record M50 T of S49 T := { f50 : T }.
HB.structure Definition S50 := { T of M50 T }.
HB.mixin Record M51 T of S50 T := { f51 : T }.
HB.structure Definition S51 := { T of M51 T }.
HB.mixin Record M52 T of S51 T := { f52 : T }.
HB.structure Definition S52 := { T of M52 T }.
HB.mixin Record M53 T of S52 T := { f53 : T }.
HB.structure Definition S53 := { T of M53 T }.
HB.mixin Record M54 T of S53 T := { f54 : T }.
HB.structure Definition S54 := { T of M54 T }.
HB.mixin Record M55 T of S54 T := { f55 : T }.
HB.structure Definition S55 := { T of M55 T }.
HB.mixin Record M56 T of S55 T := { f56 : T }.
HB.structure Definition S56 := { T of M56 T }.
HB.mixin Record M57 T of S56 T := { f57 : T }.
HB.structure Definition S57 := { T of M57 T }.
HB.mixin Record M58 T of S57 T := { f58 : T }.
HB.structure Definition S58 := { T of M58 T }.
HB.mixin Record M59 T of S58 T := { f59 : T }.
HB.structure Definition S59 := { T of M59 T }.
HB.mixin Record M60 T of S59 T := { f60 : T }.
HB.structure Definition S60 := { T of M60 T }.
HB.mixin Record M61 T of S60 T := { f61 : T }.
HB.structure Definition S61 := { T of M61 T }.
HB.mixin Record M62 T of S61 T := { f62 : T }.
HB.structure Definition S62 := { T of M62 T }.
HB.mixin Record M63 T of S62 T := { f63 : T }.
HB.structure Definition S63 := { T of M63 T }.
HB.mixin Record M64 T of S63 T := { f64 : T }.
HB.structure Definition S64 := { T of M64 T }.
HB.mixin Record M65 T of S64 T := { f65 : T }.
HB.structure Definition S65 := { T of M65 T }.
HB.mixin Record M66 T of S65 T := { f66 : T }.
HB.structure Definition S66 := { T of M66 T }.
HB.mixin Record M67 T of S66 T := { f67 : T }.
HB.structure Definition S67 := { T of M67 T }.
HB.mixin Record M68 T of S67 T := { f68 : T }.
HB.structure Definition S68 := { T of M68 T }.
HB.mixin Record M69 T of S68 T := { f69 : T }.
HB.structure Definition S69 := { T of M69 T }.
HB.mixin Record M70 T of S69 T := { f70 : T }.
HB.structure Definition S70 := { T of M70 T }.
HB.mixin Record M71 T of S70 T := { f71 : T }.
HB.structure Definition S71 := { T of M71 T }.
HB.mixin Record M72 T of S71 T := { f72 : T }.
HB.structure Definition S72 := { T of M72 T }.
HB.mixin Record M73 T of S72 T := { f73 : T }.
HB.structure Definition S73 := { T of M73 T }.
HB.mixin Record M74 T of S73 T := { f74 : T }.
HB.structure Definition S74 := { T of M74 T }.
HB.mixin Record M75 T of S74 T := { f75 : T }.
HB.structure Definition S75 := { T of M75 T }.
HB.mixin Record M76 T of S75 T := { f76 : T }.
HB.structure Definition S76 := { T of M76 T }.
HB.mixin Record M77 T of S76 T := { f77 : T }.
HB.structure Definition S77 := { T of M77 T }.
HB.mixin Record M78 T of S77 T := { f78 : T }.
HB.structure Definition S78 := { T of M78 T }.
HB.mixin Record M79 T of S78 T := { f79 : T }.
HB.structure Definition S79 := { T of M79 T }.
HB.mixin Record M80 T of S79 T := { f80 : T }.
HB.structure Definition S80 := { T of M80 T }.
HB.mixin Record M81 T of S80 T := { f81 : T }.
HB.structure Definition S81 := { T of M81 T }.
HB.mixin Record M82 T of S81 T := { f82 : T }.
HB.structure Definition S82 := { T of M82 T }.
HB.mixin Record M83 T of S82 T := { f83 : T }.
HB.structure Definition S83 := { T of M83 T }.
HB.mixin Record M84 T of S83 T := { f84 : T }.
HB.structure Definition S84 := { T of M84 T }.
HB.mixin Record M85 T of S84 T := { f85 : T }.
HB.structure Definition S85 := { T of M85 T }.
HB.mixin Record M86 T of S85 T := { f86 : T }.
HB.structure Definition S86 := { T of M86 T }.
HB.mixin Record M87 T of S86 T := { f87 : T }.
HB.structure Definition S87 := { T of M87 T }.
HB.mixin Record M88 T of S87 T := { f88 : T }.
HB.structure Definition S88 := { T of M88 T }.
HB.mixin Record M89 T of S88 T := { f89 : T }.
HB.structure Definition S89 := { T of M89 T }.
HB.mixin Record M90 T of S89 T := { f90 : T }.
HB.structure Definition S90 := { T of M90 T }.
HB.mixin Record M91 T of S90 T := { f91 : T }.
HB.structure Definition S91 := { T of M91 T }.
HB.mixin Record M92 T of S91 T := { f92 : T }.
HB.structure Definition S92 := { T of M92 T }.
HB.mixin Record M93 T of S92 T := { f93 : T }.
HB.structure Definition S93 := { T of M93 T }.
HB.mixin Record M94 T of S93 T := { f94 : T }.
HB.structure Definition S94 := { T of M94 T }.
HB.mixin Record M95 T of S94 T := { f95 : T }.
HB.structure Definition S95 := { T of M95 T }.
HB.mixin Record M96 T of S95 T := { f96 : T }.
HB.structure Definition S96 := { T of M96 T }.
HB.mixin Record M97 T of S96 T := { f97 : T }.
HB.structure Definition S97 := { T of M97 T }.
HB.mixin Record M98 T of S97 T := { f98 : T }.
HB.structure Definition S98 := { T of M98 T }.
HB.mixin Record M99 T of S98 T := { f99 : T }.
HB.structure Definition S99 := { T of M99 T }.
HB.mixin Record M100 T of S99 T := { f100 : T }.
HB.structure Definition S100 := { T of M100 T }.
*)
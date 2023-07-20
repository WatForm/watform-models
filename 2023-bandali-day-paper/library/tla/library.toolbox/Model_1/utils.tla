------------------------------- MODULE utils -------------------------------
(***************************************************************************)
(* Contains various helper predicates for dealing with sets and functions. *)
(***************************************************************************)

(* The Library case study - TLA+ model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Library TLA+ model.

The Library TLA+ model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Library TLA+ model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Library TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.

*)

EXTENDS Integers, FiniteSets


\* Sets

RECURSIVE SetSum(_)
SetSum(S) ==
    IF S = {}
    THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  x + SetSum(S \ {x})

ChooseOne(S, P(_)) ==
    CHOOSE x \in S: P(x) /\ \A y \in S: P(y) => y = x

Min(S) ==
    CHOOSE x \in S: ~(\E y \in S: y # x /\ y < x)

Max(S) ==
    CHOOSE x \in S: ~(\E y \in S: y # x /\ x < y)


\* Functions

Range(f) == {f[x]: x \in DOMAIN f}

CardDom(f) == Cardinality(DOMAIN f)

CardRan(f) == Cardinality(Range(f))

Card(f) == CardDom(f)

DomRes(S, f) == [x \in (S \intersect DOMAIN f) |-> f[x]]
 \* Restriction on domain of f for set S
 \* S <| f = {x |-> y | (x |-> y) \in f /\ x \in S}

DomSub(S, f) == [x \in DOMAIN f \ S |-> f[x]]
 \* Subtraction on domain of f for set S
 \* S <<| f = {x |-> y | (x |-> y) \in f /\ x \notin S}

RanRes(f, S) == [x \in {y \in DOMAIN f: f[y] \in S} |-> f[x]]
 \* Restriction on range of f for set S
 \* f |> S = {x |-> y | (x |-> y) \in f /\ y \in S}

RanSub(f, S) == [x \in {y \in DOMAIN f: f[y] \notin S} |-> f[x]]
 \* Subtraction on range of f for set S
 \* f |>> S = {x |-> y | (x |-> y) \in f /\ y \notin S}

DomResBy(x, f) == DomRes({x}, f)
 \* Domain restriction by given element
 \* x @< f = {x} <| f

DomSubBy(x, f) == DomSub({x}, f)
 \* Domain subtraction by given element
 \* x @<< f = {x} <<| f

RanResBy(f, x) == RanRes(f, {x})
 \* Range restriction by given element
 \* x @> f = f |> {x}

RanSubBy(f, x) == RanSub(f, {x})
 \* Range subtraction by given element
 \* x @>> f = f |>> {x}

\* Inverse of f, defined only if f is invertible
Inverse(f) == [y \in Range(f) |-> ChooseOne(DOMAIN f, LAMBDA x: f[x] = y)]

\* Index i such that f[i] = x
Index(x, f) == Inverse(f)[x]

\* Partial function from S to T, where
\* its domain could be any subset of S
PFun(S, T) == UNION {[Ss -> T] : Ss \in SUBSET S}

=============================================================================
\* Modification History
\* Last modified Wed Dec 25 17:36:15 EST 2019 by bandali
\* Last modified Sat Nov 18 19:28:05 EST 2017 by amin
\* Created Sat Nov 18 01:13:19 EST 2017 by amin

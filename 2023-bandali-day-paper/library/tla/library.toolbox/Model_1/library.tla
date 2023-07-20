------------------------------ MODULE library ------------------------------
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


The Library management case study is described in
\cite{DBLP:conf/icfem/FrappierFCCO10} by Frappier et al.

@InProceedings{DBLP:conf/icfem/FrappierFCCO10,
  author    = {Marc Frappier and Beno{\^{\i}}t Fraikin and Romain
                  Chossart and Rapha{\"{e}}l Chane{-}Yack{-}Fa and
                  Mohammed Ouenzar},
  title     = {Comparison of Model Checking Tools for Information
                  Systems},
  year      = 2010,
  booktitle = {Formal Methods and Software Engineering - 12th
                  International Conference on Formal Engineering
                  Methods, {ICFEM} 2010, Shanghai, China, November
                  17-19, 2010. Proceedings},
  pages     = {581-596},
  doi       = {10.1007/978-3-642-16901-4\_38},
  url       = {https://doi.org/10.1007/978-3-642-16901-4\_38},
  crossref  = {DBLP:conf/icfem/2010},
  timestamp = {Tue, 14 May 2019 10:00:50 +0200},
  biburl    = {https://dblp.org/rec/bib/conf/icfem/FrappierFCCO10},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

The Library TLA+ model is an adaptation of the Alloy one by
Frappier et al.

This model has appeared in the following publications:

@mastersthesis{bandali2020,
  type      = {{MMath} thesis},
  author    = {Amin Bandali},
  title     = {{A Comprehensive Study of Declarative Modelling Languages}},
  school    = "University of Waterloo, David R. Cheriton School of Computer Science",
  year      = 2020,
  month     = {July},
  publisher = "UWSpace",
  url       = {http://hdl.handle.net/10012/16059},
  note      = {\url{http://hdl.handle.net/10012/16059} and
                  \url{https://bndl.org/mmath}},
  pdf       = {https://p.bndl.org/bandali-mmath-thesis.pdf}
}

*)

EXTENDS Sequences, TLC, utils

CONSTANTS MemberID, BookID

VARIABLES members, books, loans, reservations

vars == << members, books, loans, reservations >>

maxNbLoans == Cardinality(BookID) - 1

TypeOK ==
    /\ members \subseteq MemberID
    /\ books \subseteq BookID
    /\ loans \in [books -> SUBSET members]
    /\ reservations \in [books -> Seq(members)]

Acquire(book) ==
    /\ book \in BookID
    /\ book \notin books
    /\ books' = books \union {book}
    /\ loans' = loans @@ book :> {}
    /\ reservations' = reservations @@ book :> <<>>
    /\ UNCHANGED members

Cancel(member, book) ==
    /\ member \in MemberID
    /\ book \in BookID
    /\ member \in members
    /\ book \in books
    /\ reservations[book] # <<>>
    /\ member \in Range(reservations[book])
    /\ reservations' =
        [reservations EXCEPT ![book] =
            LET s == reservations[book] IN
                LET i == Index(member, reservations[book]) IN
                    SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))]
    /\ UNCHANGED << members, books, loans >>

Discard(book) ==
    /\ book \in BookID
    /\ book \in books
    /\ loans[book] = {}
    /\ reservations[book] = <<>>
    /\ books' = books \ {book}
    /\ loans' = DomSub({book}, loans)
    /\ reservations' = DomSub({book}, reservations)
    /\ UNCHANGED members

Join(member) ==
    /\ member \in MemberID
    /\ member \notin members
    /\ members' = members \union {member}
    /\ UNCHANGED << books, loans, reservations >>

Leave(member) ==
    /\ member \in MemberID
    /\ member \in members
    /\ {member} \notin Range(loans)
    /\ reservations # <<>> =>
        \A r \in Range(reservations): RanRes(r, {member}) = <<>>
    /\ members' = members \ {member}
    /\ UNCHANGED << books, loans, reservations >>

Lend(member, book) ==
    /\ member \in MemberID
    /\ book \in BookID
    /\ member \in members
    /\ book \in books
    /\ loans[book] = {}
    /\ reservations[book] = <<>>
    /\ Card(RanRes(loans, {{member}})) < maxNbLoans
    /\ loans' = [loans EXCEPT ![book] = {member}]
    /\ UNCHANGED << members, books, reservations >>

Renew(member, book) ==
    /\ member \in MemberID
    /\ book \in BookID
    /\ member \in members
    /\ book \in books
    /\ loans[book] = {member}
    /\ reservations[book] = <<>>
    /\ TRUE
    /\ UNCHANGED vars

Reserve(member, book) ==
    /\ member \in MemberID
    /\ book \in BookID
    /\ member \in members
    /\ book \in books
    /\ member \notin Range(reservations[book])
    /\ loans[book] # {member}
    /\ \/ loans[book] # {}
       \/ reservations[book] # <<>>
    /\ reservations' =
        [reservations EXCEPT ![book] = Append(reservations[book], member)]
    /\ UNCHANGED << members, books, loans >>

Return(book) ==
    /\ book \in BookID
    /\ book \in books
    /\ loans[book] # {}
    /\ loans' = [loans EXCEPT ![book] = {}]
    /\ UNCHANGED << members, books, reservations >>

Take(member, book) ==
    /\ member \in MemberID
    /\ book \in BookID
    /\ member \in members
    /\ book \in books
    /\ loans[book] = {}
    /\ Card(RanRes(loans, {{member}})) < maxNbLoans
    /\ Card(reservations[book]) # 0
    /\ Head(reservations[book]) = member
    /\ loans' = [loans EXCEPT ![book] = {member}]
    /\ reservations' =
        [reservations EXCEPT ![book] = Tail(reservations[book])]
    /\ UNCHANGED << members, books >>


Init ==
    /\ members = {}
    /\ books = {}
    /\ loans = <<>>
    /\ reservations = <<>>

Next ==
    \/ \E b \in BookID:
        \/ Acquire(b)
        \/ Discard(b)
        \/ Return(b)
    \/ \E m \in MemberID:
        \/ Join(m)
        \/ Leave(m)
    \/ \E m \in MemberID, b \in BookID:
        \/ Cancel(m, b)
        \/ Lend(m, b)
        \/ Renew(m, b)
        \/ Reserve(m, b)
        \/ Take(m, b)

Live == TRUE \* WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Live


ASSERT_LTL_2 ==
    \A b \in BookID:
        [](ENABLED Acquire(b) => b \notin books)

ASSERT_LTL_3 ==
    \A b \in BookID:
        [](ENABLED Discard(b) =>
            /\ loans[b] = {}
            /\ reservations[b] = <<>>)

ASSERT_LTL_4 ==
    \A m \in MemberID, b \in BookID:
        [](ENABLED Lend(m, b) => m \in members)

ASSERT_LTL_5 ==
    \A m \in MemberID, b \in BookID:
        [](ENABLED Reserve(m, b) =>
            /\ m \notin Range(reservations[b])
            /\ loans[b] # {m}
            /\ \/ loans[b] # {}
               \/ reservations[b] # <<>>)

ASSERT_LTL_6 ==
    \A m \in MemberID, b \in BookID:
        [](ENABLED Reserve(m, b) => loans[b] # {m})

ASSERT_LTL_7 ==
    \A m \in MemberID, b \in BookID:
        [](ENABLED Reserve(m, b) => m \notin Range(reservations[b]))

ASSERT_LTL_8 ==
    \A m \in MemberID, b \in BookID:
        [](\A b_ \in DOMAIN reservations:
            reservations[b_] # <<>> =>
                ~(ENABLED Lend(m, b) /\ b = b_))

ASSERT_LTL_9 ==
    \A m \in MemberID, b \in BookID:
        [](\A b_ \in DOMAIN reservations:
            reservations[b_] # <<>> =>
                ~(ENABLED Renew(m, b) /\ b = b_))

ASSERT_LTL_10 ==
    \A m \in MemberID, b \in BookID:
        [](ENABLED Take(m, b) =>
            /\ reservations[b] # <<>>
            /\ Head(reservations[b]) = m)

ASSERT_LTL_11 ==  \* not accurately represented, since TLA+ doesn't have W
    \A m \in MemberID, b \in BookID:
        /\ [](\A b_ \in DOMAIN loans:
            loans[b_] # {} => ~(ENABLED Take(m, b) /\ b = b_))
        /\ [](ENABLED Take(m, b) => loans[b] = {})

ASSERT_LTL_13 ==
    \A m \in MemberID:
        [](ENABLED Leave(m) =>
            /\ m \in members
            /\ {m} \notin Range(loans)
            /\ reservations # <<>> =>
                \A r \in Range(reservations): RanRes(r, {m}) = <<>>)

ASSERT_LTL_15 ==
    [](\A m \in members: Card(RanRes(loans, {{m}})) <= maxNbLoans)

=============================================================================
\* Modification History
\* Last modified Sat Jan 04 17:37:47 EST 2020 by bandali
\* Created Mon Dec 30 12:52:34 EST 2019 by bandali

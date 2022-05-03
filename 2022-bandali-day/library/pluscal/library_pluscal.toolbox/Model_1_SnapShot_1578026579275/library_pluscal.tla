-------------------------- MODULE library_pluscal --------------------------
(* The Library case study - PlusCal model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Library PlusCal model.

The Library PlusCal model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Library PlusCal model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Library PlusCal model.  If not, see
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

The Library PlusCal model is an adaptation of the Alloy one by
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

maxNbLoans == Cardinality(BookID) - 1

(* --algorithm library_pluscal
variables loans = <<>>,
          members = {},
          books = {},
          reservations = <<>>;

define

TypeOK ==
    /\ members \subseteq MemberID
    /\ books \subseteq BookID
    /\ loans \in [books -> SUBSET members]
    /\ reservations \in [books -> Seq(members)]

end define

process Acquire = "Acquire"
variable book \in BookID
begin
    acquire:
        when book \notin books;
        books := books \union {book};
        loans := loans @@ book :> {};
        reservations := reservations @@ book :> <<>>
end process

process Cancel = "cancel"
variables member \in MemberID,
          book \in BookID;
begin
    cancel:
        when
            /\ member \in members
            /\ book \in books
            /\ reservations[book] # <<>>
            /\ member \in Range(reservations[book]);
        reservations[book] :=
            LET s == reservations[book] IN
                LET i == Index(member, reservations[book]) IN
                    SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))
end process

process Discard = "Discard"
variable book \in BookID
begin
    discard:
        when
            /\ book \in books
            /\ loans[book] = {}
            /\ reservations[book] = <<>>;
        books := books \ {book};
        loans := DomSub({book}, loans);
        reservations := DomSub({book}, reservations)
end process

process Join = "Join"
variable member \in MemberID
begin
    join:
        when member \notin members;
        members := members \union {member}
end process

process Leave = "Leave"
variable member \in MemberID
begin
    leave:
        when
            /\ member \in members
            /\ {member} \notin Range(loans)
            /\ reservations # <<>> =>
                \A r \in Range(reservations): RanRes(r, {member}) = <<>>;
        members := members \ {member}
end process

process Lend = "Lend"
variables member \in MemberID,
          book \in BookID;
begin
    lend:
        when
            /\ member \in members
            /\ book \in books
            /\ loans[book] = {}
            /\ reservations[book] = <<>>
            /\ Card(RanRes(loans, {{member}})) < maxNbLoans;
        loans[book] := {member}
end process

process Renew = "Renew"
variables member \in MemberID,
          book \in BookID;
begin
    renew:
        when
            /\ member \in members
            /\ book \in books
            /\ loans[book] = {member}
            /\ reservations[book] = <<>>;
        skip
end process

process Reserve = "Reserve"
variables member \in MemberID,
          book \in BookID;
begin
    reserve:
        when
            /\ member \in members
            /\ book \in books
            /\ member \notin Range(reservations[book])
            /\ loans[book] # {member}
            /\ \/ loans[book] # {}
               \/ reservations[book] # <<>>;
        reservations[book] := Append(reservations[book], member)
end process

process Return = "Return"
variables book \in BookID
begin
    return_:
        when
            /\ book \in books
            /\ loans[book] # {};
        loans[book] := {}
end process

process Take = "Take"
variables member \in MemberID,
          book \in BookID;
begin
    take:
        when
            /\ member \in members
            /\ book \in books
            /\ loans[book] = {}
            /\ Card(RanRes(loans, {{member}})) < maxNbLoans
            /\ Card(reservations[book]) # 0
            /\ Head(reservations[book]) = member;
        loans[book] := {member};
        reservations[book] := Tail(reservations[book])
end process

end algorithm *)
\* BEGIN TRANSLATION
\* Process variable book of process Acquire at line 26 col 10 changed to book_
\* Process variable member of process Cancel at line 36 col 11 changed to member_
\* Process variable book of process Cancel at line 37 col 11 changed to book_C
\* Process variable book of process Discard at line 52 col 10 changed to book_D
\* Process variable member of process Join at line 65 col 10 changed to member_J
\* Process variable member of process Leave at line 73 col 10 changed to member_L
\* Process variable member of process Lend at line 85 col 11 changed to member_Le
\* Process variable book of process Lend at line 86 col 11 changed to book_L
\* Process variable member of process Renew at line 99 col 11 changed to member_R
\* Process variable book of process Renew at line 100 col 11 changed to book_R
\* Process variable member of process Reserve at line 112 col 11 changed to member_Re
\* Process variable book of process Reserve at line 113 col 11 changed to book_Re
\* Process variable book of process Return at line 127 col 11 changed to book_Ret
VARIABLES loans, members, books, reservations, pc

(* define statement *)
TypeOK ==
    /\ members \subseteq MemberID
    /\ books \subseteq BookID
    /\ loans \in [books -> SUBSET members]
    /\ reservations \in [books -> Seq(members)]

VARIABLES book_, member_, book_C, book_D, member_J, member_L, member_Le, 
          book_L, member_R, book_R, member_Re, book_Re, book_Ret, member, 
          book

vars == << loans, members, books, reservations, pc, book_, member_, book_C, 
           book_D, member_J, member_L, member_Le, book_L, member_R, book_R, 
           member_Re, book_Re, book_Ret, member, book >>

ProcSet == {"Acquire"} \cup {"cancel"} \cup {"Discard"} \cup {"Join"} \cup {"Leave"} \cup {"Lend"} \cup {"Renew"} \cup {"Reserve"} \cup {"Return"} \cup {"Take"}

Init == (* Global variables *)
        /\ loans = <<>>
        /\ members = {}
        /\ books = {}
        /\ reservations = <<>>
        (* Process Acquire *)
        /\ book_ \in BookID
        (* Process Cancel *)
        /\ member_ \in MemberID
        /\ book_C \in BookID
        (* Process Discard *)
        /\ book_D \in BookID
        (* Process Join *)
        /\ member_J \in MemberID
        (* Process Leave *)
        /\ member_L \in MemberID
        (* Process Lend *)
        /\ member_Le \in MemberID
        /\ book_L \in BookID
        (* Process Renew *)
        /\ member_R \in MemberID
        /\ book_R \in BookID
        (* Process Reserve *)
        /\ member_Re \in MemberID
        /\ book_Re \in BookID
        (* Process Return *)
        /\ book_Ret \in BookID
        (* Process Take *)
        /\ member \in MemberID
        /\ book \in BookID
        /\ pc = [self \in ProcSet |-> CASE self = "Acquire" -> "acquire"
                                        [] self = "cancel" -> "cancel"
                                        [] self = "Discard" -> "discard"
                                        [] self = "Join" -> "join"
                                        [] self = "Leave" -> "leave"
                                        [] self = "Lend" -> "lend"
                                        [] self = "Renew" -> "renew"
                                        [] self = "Reserve" -> "reserve"
                                        [] self = "Return" -> "return_"
                                        [] self = "Take" -> "take"]

acquire == /\ pc["Acquire"] = "acquire"
           /\ book_ \notin books
           /\ books' = (books \union {book_})
           /\ loans' = (loans @@ book_ :> {})
           /\ reservations' = (reservations @@ book_ :> <<>>)
           /\ pc' = [pc EXCEPT !["Acquire"] = "Done"]
           /\ UNCHANGED << members, book_, member_, book_C, book_D, member_J, 
                           member_L, member_Le, book_L, member_R, book_R, 
                           member_Re, book_Re, book_Ret, member, book >>

Acquire == acquire

cancel == /\ pc["cancel"] = "cancel"
          /\ /\ member_ \in members
             /\ book_C \in books
             /\ reservations[book_C] # <<>>
             /\ member_ \in Range(reservations[book_C])
          /\ reservations' = [reservations EXCEPT ![book_C] = LET s == reservations[book_C] IN
                                                                  LET i == Index(member_, reservations[book_C]) IN
                                                                      SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))]
          /\ pc' = [pc EXCEPT !["cancel"] = "Done"]
          /\ UNCHANGED << loans, members, books, book_, member_, book_C, 
                          book_D, member_J, member_L, member_Le, book_L, 
                          member_R, book_R, member_Re, book_Re, book_Ret, 
                          member, book >>

Cancel == cancel

discard == /\ pc["Discard"] = "discard"
           /\ /\ book_D \in books
              /\ loans[book_D] = {}
              /\ reservations[book_D] = <<>>
           /\ books' = books \ {book_D}
           /\ loans' = DomSub({book_D}, loans)
           /\ reservations' = DomSub({book_D}, reservations)
           /\ pc' = [pc EXCEPT !["Discard"] = "Done"]
           /\ UNCHANGED << members, book_, member_, book_C, book_D, member_J, 
                           member_L, member_Le, book_L, member_R, book_R, 
                           member_Re, book_Re, book_Ret, member, book >>

Discard == discard

join == /\ pc["Join"] = "join"
        /\ member_J \notin members
        /\ members' = (members \union {member_J})
        /\ pc' = [pc EXCEPT !["Join"] = "Done"]
        /\ UNCHANGED << loans, books, reservations, book_, member_, book_C, 
                        book_D, member_J, member_L, member_Le, book_L, 
                        member_R, book_R, member_Re, book_Re, book_Ret, member, 
                        book >>

Join == join

leave == /\ pc["Leave"] = "leave"
         /\ /\ member_L \in members
            /\ {member_L} \notin Range(loans)
            /\ reservations # <<>> =>
                \A r \in Range(reservations): RanRes(r, {member_L}) = <<>>
         /\ members' = members \ {member_L}
         /\ pc' = [pc EXCEPT !["Leave"] = "Done"]
         /\ UNCHANGED << loans, books, reservations, book_, member_, book_C, 
                         book_D, member_J, member_L, member_Le, book_L, 
                         member_R, book_R, member_Re, book_Re, book_Ret, 
                         member, book >>

Leave == leave

lend == /\ pc["Lend"] = "lend"
        /\ /\ member_Le \in members
           /\ book_L \in books
           /\ loans[book_L] = {}
           /\ reservations[book_L] = <<>>
           /\ Card(RanRes(loans, {{member_Le}})) < maxNbLoans
        /\ loans' = [loans EXCEPT ![book_L] = {member_Le}]
        /\ pc' = [pc EXCEPT !["Lend"] = "Done"]
        /\ UNCHANGED << members, books, reservations, book_, member_, book_C, 
                        book_D, member_J, member_L, member_Le, book_L, 
                        member_R, book_R, member_Re, book_Re, book_Ret, member, 
                        book >>

Lend == lend

renew == /\ pc["Renew"] = "renew"
         /\ /\ member_R \in members
            /\ book_R \in books
            /\ loans[book_R] = {member_R}
            /\ reservations[book_R] = <<>>
         /\ TRUE
         /\ pc' = [pc EXCEPT !["Renew"] = "Done"]
         /\ UNCHANGED << loans, members, books, reservations, book_, member_, 
                         book_C, book_D, member_J, member_L, member_Le, book_L, 
                         member_R, book_R, member_Re, book_Re, book_Ret, 
                         member, book >>

Renew == renew

reserve == /\ pc["Reserve"] = "reserve"
           /\ /\ member_Re \in members
              /\ book_Re \in books
              /\ member_Re \notin Range(reservations[book_Re])
              /\ loans[book_Re] # {member_Re}
              /\ \/ loans[book_Re] # {}
                 \/ reservations[book_Re] # <<>>
           /\ reservations' = [reservations EXCEPT ![book_Re] = Append(reservations[book_Re], member_Re)]
           /\ pc' = [pc EXCEPT !["Reserve"] = "Done"]
           /\ UNCHANGED << loans, members, books, book_, member_, book_C, 
                           book_D, member_J, member_L, member_Le, book_L, 
                           member_R, book_R, member_Re, book_Re, book_Ret, 
                           member, book >>

Reserve == reserve

return_ == /\ pc["Return"] = "return_"
           /\ /\ book_Ret \in books
              /\ loans[book_Ret] # {}
           /\ loans' = [loans EXCEPT ![book_Ret] = {}]
           /\ pc' = [pc EXCEPT !["Return"] = "Done"]
           /\ UNCHANGED << members, books, reservations, book_, member_, 
                           book_C, book_D, member_J, member_L, member_Le, 
                           book_L, member_R, book_R, member_Re, book_Re, 
                           book_Ret, member, book >>

Return == return_

take == /\ pc["Take"] = "take"
        /\ /\ member \in members
           /\ book \in books
           /\ loans[book] = {}
           /\ Card(RanRes(loans, {{member}})) < maxNbLoans
           /\ Card(reservations[book]) # 0
           /\ Head(reservations[book]) = member
        /\ loans' = [loans EXCEPT ![book] = {member}]
        /\ reservations' = [reservations EXCEPT ![book] = Tail(reservations[book])]
        /\ pc' = [pc EXCEPT !["Take"] = "Done"]
        /\ UNCHANGED << members, books, book_, member_, book_C, book_D, 
                        member_J, member_L, member_Le, book_L, member_R, 
                        book_R, member_Re, book_Re, book_Ret, member, book >>

Take == take

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Acquire \/ Cancel \/ Discard \/ Join \/ Leave \/ Lend \/ Renew
           \/ Reserve \/ Return \/ Take
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ASSERT_LTL_2 == [](ENABLED Acquire => book_ \notin books)

ASSERT_LTL_3 ==
    [](ENABLED Discard =>
        /\ loans[book_D] = {}
        /\ reservations[book_D] = <<>>)

ASSERT_LTL_4 == [](ENABLED Lend => member_Le \in members)

ASSERT_LTL_5 ==
    [](ENABLED Reserve =>
        /\ member_Re \notin Range(reservations[book_Re])
        /\ loans[book_Re] # {member_Re}
        /\ \/ loans[book_Re] # {}
           \/ reservations[book_Re] # <<>>)

ASSERT_LTL_6 ==
    [](ENABLED Reserve => loans[book_Re] # {member_Re})

ASSERT_LTL_7 ==
    [](ENABLED Reserve => member_Re \notin Range(reservations[book_Re]))

ASSERT_LTL_8 ==
    [](\A b \in DOMAIN reservations:
        reservations[b] # <<>> => ~(ENABLED Lend /\ book_L = b))

ASSERT_LTL_9 ==
    [](\A b \in DOMAIN reservations:
        reservations[b] # <<>> => ~(ENABLED Renew /\ book_R = b))

ASSERT_LTL_10 ==
    [](ENABLED Take =>
        /\ reservations[book] # <<>>
        /\ Head(reservations[book]) = member)

ASSERT_LTL_11 ==  \* not accurately represented, since TLA+ doesn't have W
    /\ [](\A b \in DOMAIN loans:
        loans[b] # {} => ~(ENABLED Take /\ book = b))
    /\ [](ENABLED Take => loans[book] = {})

ASSERT_LTL_13 ==
    [](ENABLED Leave =>
        /\ member_L \in members
        /\ {member_L} \notin Range(loans)
        /\ reservations # <<>> =>
            \A r \in Range(reservations): RanRes(r, {member_L}) = <<>>)

ASSERT_LTL_15 ==
    [](\A m \in members: Card(RanRes(loans, {{m}})) <= maxNbLoans)

=============================================================================
\* Modification History
\* Last modified Thu Jan 02 23:20:51 EST 2020 by bandali
\* Created Tue Dec 24 20:53:14 EST 2019 by bandali

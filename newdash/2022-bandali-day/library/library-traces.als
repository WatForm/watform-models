/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-06-05 14:19:45
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/* The Library case study - Dash model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Library Dash model.

The Library Dash model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Library Dash model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Library Dash model.  If not, see
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

The Library Dash model is an adaptation of the Alloy one by
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

*/

open util/sequniv

one sig Const {
    maxNbLoans: Int
}

sig MemberID, BookID {}

abstract sig DshStates {}
abstract sig Library extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  Library_in_m: lone MemberID,
  Library_in_b: lone BookID,
  Library_members: set MemberID,
  Library_books: set BookID,
  Library_loans: Library_books one->one Library_members,
  Library_reservations: Library_books one->one
                        (seq Library_members)
}

pred dsh_initial [
	s: one DshSnapshot] {
  (s.dsh_conf0) = Library and
  no
  s.Library_members and
  no
  s.Library_books and
  no
  s.Library_loans and
  no
  s.Library_reservations
}

fact inv {  (Const.maxNbLoans) = (7)
}

pred Library_Cancel_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  s.Library_in_b in s.Library_books and
  one
  ((Int -> s.Library_in_m) &
     ((s.Library_in_b).(s.Library_reservations)))
  !(Library in (s.dsh_sc_used0))
}


pred Library_Cancel_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  ((s.Library_in_b).(sn.Library_reservations)) =
  (((s.Library_in_m).(((s.Library_in_b).(s.Library_reservations)).idxOf)).(((s.Library_in_b).(s.Library_reservations)).delete))
}

pred Library_Cancel [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Cancel_pre
  sn.(s.Library_Cancel_post)
}

pred Library_Join_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  !(s.Library_in_m in s.Library_members)
  !(Library in (s.dsh_sc_used0))
}


pred Library_Join_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_members) =
  ((s.Library_members) + (s.Library_in_m))
}

pred Library_Join [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Join_pre
  sn.(s.Library_Join_post)
}

pred Library_Return_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_b in s.Library_books and
  some
  ((s.Library_in_b).(s.Library_loans))
  !(Library in (s.dsh_sc_used0))
}


pred Library_Return_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_loans) =
  ((s.Library_loans) -
     (s.Library_in_b -> ((s.Library_in_b).(s.Library_loans))))
}

pred Library_Return [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Return_pre
  sn.(s.Library_Return_post)
}

pred Library_Discard_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_b in s.Library_books and
  no
  ((s.Library_in_b).(s.Library_loans)) and
  no
  ((s.Library_in_b).(s.Library_reservations))
  !(Library in (s.dsh_sc_used0))
}


pred Library_Discard_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_books) = ((s.Library_books) - (s.Library_in_b))
}

pred Library_Discard [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Discard_pre
  sn.(s.Library_Discard_post)
}

pred Library_Leave_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  no
  ((s.Library_loans).(s.Library_in_m)) and
  no
  ((Int -> s.Library_in_m) &
     ((s.Library_in_b).(s.Library_reservations)))
  !(Library in (s.dsh_sc_used0))
}


pred Library_Leave_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_members) =
  ((s.Library_members) - (s.Library_in_m))
}

pred Library_Leave [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Leave_pre
  sn.(s.Library_Leave_post)
}

pred Library_Renew_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  s.Library_in_b in s.Library_books and
  (s.Library_in_b -> s.Library_in_m) in s.Library_loans and
  no
  ((s.Library_in_b).(s.Library_reservations))
  !(Library in (s.dsh_sc_used0))
}


pred Library_Renew_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
}

pred Library_Renew [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Renew_pre
  sn.(s.Library_Renew_post)
}

pred Library_Take_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  s.Library_in_b in s.Library_books and
  no
  ((s.Library_in_b).(s.Library_loans)) and
  (# ((s.Library_loans).(s.Library_in_m))) <
    (Const.maxNbLoans) and
  (# ((s.Library_in_b).(s.Library_reservations))) > (0) and
  (((s.Library_in_b).(s.Library_reservations)).first) =
    (s.Library_in_m)
  !(Library in (s.dsh_sc_used0))
}


pred Library_Take_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_loans) =
  ((s.Library_loans) + (s.Library_in_b -> s.Library_in_m)) and
  ((s.Library_in_b).(sn.Library_reservations)) =
    (((s.Library_in_m).(((s.Library_in_b).(s.Library_reservations)).idxOf)).(((s.Library_in_b).(s.Library_reservations)).delete))
}

pred Library_Take [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Take_pre
  sn.(s.Library_Take_post)
}

pred Library_Acquire_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  !(s.Library_in_b in s.Library_books)
  !(Library in (s.dsh_sc_used0))
}


pred Library_Acquire_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_books) = ((s.Library_books) + (s.Library_in_b))
}

pred Library_Acquire [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Acquire_pre
  sn.(s.Library_Acquire_post)
}

pred Library_Lend_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  s.Library_in_b in s.Library_books and
  (all m: s.Library_members | no
    (((s.Library_loans).m) & s.Library_in_b)) and
  no
  ((s.Library_in_b).(s.Library_reservations)) and
  (# ((s.Library_loans).(s.Library_in_m))) <
    (Const.maxNbLoans)
  !(Library in (s.dsh_sc_used0))
}


pred Library_Lend_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  (sn.Library_loans) =
  ((s.Library_loans) + (s.Library_in_b -> s.Library_in_m))
}

pred Library_Lend [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Lend_pre
  sn.(s.Library_Lend_post)
}

pred Library_Reserve_pre [
	s: one DshSnapshot] {
  some (Library & (s.dsh_conf0))
  s.Library_in_m in s.Library_members and
  s.Library_in_b in s.Library_books and
  !((s.Library_in_b -> s.Library_in_m) in s.Library_loans) and
  no
  ((Int -> s.Library_in_m) &
     ((s.Library_in_b).(s.Library_reservations))) and
  { some
      ((s.Library_in_b).(s.Library_loans)) or
      !(((s.Library_in_b).(s.Library_reservations)).isEmpty) }
  !(Library in (s.dsh_sc_used0))
}


pred Library_Reserve_post [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  (sn.dsh_conf0) = (((s.dsh_conf0) - Library) + Library)
  ((s.Library_in_b).(sn.Library_reservations)) =
  ((s.Library_in_m).(((s.Library_in_b).(s.Library_reservations)).add))
}

pred Library_Reserve [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  s.Library_Reserve_pre
  sn.(s.Library_Reserve_post)
}

pred dsh_small_step [
	s: one DshSnapshot,
	sn: one DshSnapshot] {
  { sn.(s.Library_Cancel) or
    sn.(s.Library_Join) or
    sn.(s.Library_Return) or
    sn.(s.Library_Discard) or
    sn.(s.Library_Leave) or
    sn.(s.Library_Renew) or
    sn.(s.Library_Take) or
    sn.(s.Library_Acquire) or
    sn.(s.Library_Lend) or
    sn.(s.Library_Reserve) }
}

fact dsh_traces_fact {  DshSnapshot/first.dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s.DshSnapshot/next).(s.dsh_small_step))
}


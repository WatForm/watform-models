/* The Library case study - AsmetaL model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Library AsmetaL model.

The Library AsmetaL model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Library AsmetaL model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Library AsmetaL model.  If not, see
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

The Library AsmetaL model is an adaptation of the Alloy one by
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

asm library

import utils
import LTLlibrary
import CTLlibrary

signature:
	// domains
	enum domain RuleId = {ACQUIRE
						| CANCEL
						| DISCARD
						| JOIN
						| LEAVE
						| LEND
						| RENEW
						| RESERVE
						| RETURN
						| TAKE}
	enum domain MemberID = {MM1 | MM2 | MM3}
	enum domain BookID = {BB1 | BB2 | BB3}

	// function
	controlled members: Powerset(MemberID)
	controlled books: Powerset(BookID)
	controlled loans: Powerset(Prod(BookID, Powerset(MemberID)))
	controlled reservations: Powerset(Prod(BookID, Seq(MemberID)))

	derived pre_Acquire: BookID -> Boolean
	derived pre_Cancel: Prod(MemberID, BookID) -> Boolean
	derived pre_Discard: BookID -> Boolean
	derived pre_Join: MemberID -> Boolean
	derived pre_Leave: MemberID -> Boolean
	derived pre_Lend: Prod(MemberID, BookID) -> Boolean
	derived pre_Renew: Prod(MemberID, BookID) -> Boolean
	derived pre_Reserve: Prod(MemberID, BookID) -> Boolean
	derived pre_Return: BookID -> Boolean
	derived pre_Take: Prod(MemberID, BookID) -> Boolean

	static maxNbLoans: Integer

definitions:
	function maxNbLoans = 2 // card(BookID) - 1

	// helpers for preconditions
	
	function pre_Acquire($b in BookID) = notin(books, $b)

	function pre_Cancel($m in MemberID, $b in BookID) =
		contains(members, $m)
			and contains(books, $b)
			and contains(dom(reservations), $b)
			and (exist $r in ran(reservations) with
					(contains(reservations, ($b, $r)) and contains($r, $m)))

	function pre_Discard($b in BookID) =
		contains(books, $b)
			and contains(loans, ($b, {}))
			and contains(reservations, ($b, []))

	function pre_Join($m in MemberID) = notin(members, $m)

	function pre_Leave($m in MemberID) =
		contains(members, $m)
			and notin(ran(loans), {$m})
			and (forall $r in ran(reservations) with
					(not contains($r, $m)))

	function pre_Lend($m in MemberID, $b in BookID) =
		contains(members, $m)
			and contains(books, $b)
			and contains(loans, ($b, {}))
			and contains(reservations, ($b, []))
			and size(ranres(loans, {{$m}})) < maxNbLoans

	function pre_Renew($m in MemberID, $b in BookID) =
		contains(members, $m)
			and contains(books, $b)
			and contains(loans, ($b, {$m}))
			and contains(reservations, ($b, []))

	function pre_Reserve($m in MemberID, $b in BookID) =
		contains(members, $m) and contains(books, $b)
			and (not(exist $br in ran(domres({$b}, reservations)) with
					contains($br, $m)))
			and (exist $bm in loans with
					(eq(first($bm), $b) and neq(second($bm), {$m})))

	function pre_Return($b in BookID) =
		contains(books, $b) and
			(exist $m in members with
				contains(loans, ($b, {$m})))

	function pre_Take($m in MemberID, $b in BookID) =
		contains(members, $m)
			and contains(books, $b)
			and contains(loans, ($b, {}))
			and size(ranres(loans, {{$m}})) < maxNbLoans
			and neq(size(domres({$b}, reservations)), 0)
			and (exist $r in ran(reservations) with
					(contains(reservations, ($b, $r)) and eq(first($r), $m)))

	// transitions

	rule r_Acquire($b in BookID) =
		if (pre_Acquire($b)) then
			books := union(books, {$b})
		endif

	rule r_Cancel($m in MemberID, $b in BookID) =
		if (pre_Cancel($m, $b)) then
			choose $r in ran(reservations) with
					(contains(reservations, ($b, $r)) and contains($r, $m)) do
				reservations :=
					union(excluding(reservations, ($b, $r)),
							{($b, excluding($r, $m))})
		endif

	rule r_Discard($b in BookID) =
		if (pre_Discard($b)) then
			par
				books := excluding(books, $b)
				loans := excluding(loans, ($b, {}))
				reservations := excluding(reservations, ($b, []))
			endpar
		endif

	rule r_Join($m in MemberID) =
		if (pre_Join($m)) then
			members := union(members, {$m})
		endif

	rule r_Leave($m in MemberID) =
		if (pre_Leave($m)) then
			members := excluding(members, $m)
		endif

	rule r_Lend($m in MemberID, $b in BookID) =
		if (pre_Lend($m, $b)) then
			loans := union(excluding(loans, ($b, {})),
							{($b, {$m})})
		endif

	rule r_Renew($m in MemberID, $b in BookID) =
		if (pre_Renew($m, $b)) then
			skip
		endif

	rule r_Reserve($m in MemberID, $b in BookID) =
		if (pre_Reserve($m, $b)) then
			choose $r in ran(reservations) with	contains(reservations, ($b, $r)) do
				reservations :=
					union(excluding(reservations, ($b, $r)),
							{($b, append($r, $m))})
		endif

	rule r_Return($b in BookID) =
		if (pre_Return($b)) then
			choose $m in members with contains(loans, ($b, {$m})) do
				loans := union(excluding(loans, ($b, {$m})),
								{($b, {})})
		endif

	rule r_Take($m in MemberID, $b in BookID) =
		if (pre_Take($m, $b)) then
			choose $r in ran(reservations) with
					(contains(reservations, ($b, $r)) and eq(first($r), $m)) do
				par
					loans := union(excluding(loans, ($b, {})),
									{($b, {$m})})
					reservations :=
						union(excluding(reservations, ($b, $r)),
								{($b, excluding($r, $m))})
			endpar
		endif

	// invariants and properties

	invariant over books: // ASSERT_LTL_2
		(forall $b in BookID with pre_Acquire($b) implies
			notin(books, $b))

	invariant over loans: // ASSERT_LTL_3
		(forall $b in BookID with pre_Discard($b) implies
			(contains(loans, ($b, {}))
				and contains(reservations, ($b, []))))

	invariant over members: // ASSERT_LTL_4
		(forall $m in MemberID, $b in BookID with pre_Lend($m, $b) implies
			contains(members, $m))

	invariant over reservations: // ASSERT_LTL_5
		(forall $m in MemberID, $b in BookID with pre_Reserve($m, $b) implies
			(not(exist $br in ran(domres({$b}, reservations)) with
					contains($br, $m))
			and (not(contains(loans, ($b, {$m}))))
			and (contains(dom(loans), $b) or
					notin(ran(domres({$b}, reservations)), []))))

	invariant over loans: // ASSERT_LTL_6
		(forall $m in MemberID, $b in BookID with pre_Reserve($m, $b) implies
			not(contains(loans, ($b, {$m}))))

	invariant over reservations: // ASSERT_LTL_7
		(forall $m in MemberID, $b in BookID with pre_Reserve($m, $b) implies
			not(exist $br in ran(domres({$b}, reservations)) with
				contains($br, $m)))

	invariant over reservations: // ASSERT_LTL_8
		(forall $m in MemberID, $b in dom(reservations) with
			(contains(dom(reservations), $b)
				and not(contains(reservations, ($b, [])))) implies
			not(pre_Lend($m, $b)))

	invariant over reservations: // ASSERT_LTL_9
		(forall $m in MemberID, $b in dom(reservations) with
			(contains(dom(reservations), $b)
				and not(contains(reservations, ($b, [])))) implies
			not(pre_Renew($m, $b)))

	invariant over reservations: // ASSERT_LTL_10
		(forall $m in MemberID, $b in BookID with pre_Take($m, $b) implies
			((contains(dom(reservations), $b)
				and not(contains(reservations, ($b, []))))
			and (exist $r in ran(reservations) with
					(contains(reservations, ($b, $r))
						and eq(first($r), $m)))))

	invariant over loans: // ASSERT_LTL_11
		(contains(loans, (BB1, {MM2})) implies
			(u(not(pre_Take(MM1, BB1)), not(contains(loans, (BB1, {MM2}))))
			 or g(not(pre_Take(MM1, BB1)))))
		// W(f1, f2) == U(f1, f2) or G(f1) 

	invariant over members: // ASSERT_LTL_13
		(forall $m in MemberID with pre_Leave($m) implies
			(contains(members, $m)
				and notin(ran(loans), {$m})
				and (forall $r in ran(reservations) with
						(not contains($r, $m)))))

	invariant over members: // ASSERT_LTL_14 (ASSERT_CTL_14)
		ag(ef(notin(members, MM1)))

	invariant over loans: // ASSERT_LTL_15
		(forall $m in members with true implies
			size(ranres(loans, {{$m}})) <= maxNbLoans)

	// transition relation

	main rule r_Main =
		choose $b in BookID, $m in MemberID, $rule in RuleId with true do
			switch($rule)
				case ACQUIRE:
					r_Acquire[$b]
				case CANCEL:
					r_Cancel[$m, $b]
				case DISCARD:
					r_Discard[$b]
				case JOIN:
					r_Join[$m]
				case LEAVE:
					r_Leave[$m]
				case LEND:
					r_Lend[$m, $b]
				case RENEW:
					r_Renew[$m, $b]
				case RESERVE:
					r_Reserve[$m, $b]
				case RETURN:
					r_Return[$b]
				case TAKE:
					r_Take[$m, $b]
			endswitch

default init s0:
	function members = {}
	function books = {}
	function loans = {}
	function reservations = {}

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

*/

module utils

import StandardLibrary

export *

signature:

	derived dom: Powerset(Prod(D1, D2)) -> Powerset(D1)
	derived ran: Powerset(Prod(D1, D2)) -> Powerset(D2)
	derived domres: Prod(Powerset(D1), Powerset(Prod(D1, D2))) -> Powerset(Prod(D1, D2))
	derived ranres: Prod(Powerset(Prod(D1, D2)), Powerset(D2)) -> Powerset(Prod(D1, D2))

definitions:

	function dom($f in Powerset(Prod(D1, D2))) =
		{$d1 in D1, $d2 in D2 | contains($f, ($d1, $d2)): $d1}

	function ran($f in Powerset(Prod(D1, D2))) =
		{$d1 in D1, $d2 in D2 | contains($f, ($d1, $d2)): $d2}

	function domres($s in Powerset(D1), $f in Powerset(Prod(D1, D2))) =
		{$d1 in D1, $d2 in D2 |
			contains($f, ($d1, $d2)) and contains($s, $d1): ($d1, $d2)}

	function ranres($f in Powerset(Prod(D1, D2)), $s in Powerset(D2)) =
		{$d1 in D1, $d2 in D2 |
			contains($f, ($d1, $d2)) and contains($s, $d2): ($d1, $d2)}


//	turbo rule r_get($f in Powerset(Prod(D1, D2)), $x in D1) in D2 =
//		choose $xy in $f with eq(first($xy), $x) do
//			result := second($xy)

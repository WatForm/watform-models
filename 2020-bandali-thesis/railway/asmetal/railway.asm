/* The Railway case study - AsmetaL model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Railway AsmetaL model.

The Railway AsmetaL model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Railway AsmetaL model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Railway AsmetaL model.  If not, see
<https://www.gnu.org/licenses/>.


The Railway case study (train scheduling deadlock avoidance model) is
described in~\cite{DBLP:journals/sttt/MazzantiFS18} by Frappier et al.
The Railway AsmetaL model is an adaptation of the original model(s)
presented there.

@Article{DBLP:journals/sttt/MazzantiFS18,
  author    = {Franco Mazzanti and Alessio Ferrari and Giorgio Oronzo
                  Spagnolo},
  title     = {Towards formal methods diversity in railways: an
                  experience report with seven frameworks},
  year      = 2018,
  volume    = 20,
  number    = 3,
  pages     = {263-288},
  doi       = {10.1007/s10009-018-0488-3},
  url       = {https://doi.org/10.1007/s10009-018-0488-3},
  journal   = {{STTT}},
  timestamp = {Fri, 30 Nov 2018 13:26:45 +0100},
  biburl    = {https://dblp.org/rec/bib/journals/sttt/MazzantiFS18},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

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

asm railway

import StandardLibrary

signature:
	domain Station subsetof Integer
	domain Train subsetof Natural
	domain Constraint subsetof Integer

	monitored ct: Train

	controlled p: Seq(Natural)
	controlled ra: Integer
	controlled rb: Integer

	static t: Seq(Seq(Station))
	static a: Seq(Seq(Constraint))
	static b: Seq(Seq(Constraint))
	static la: Integer
	static lb: Integer

definitions:
	domain Station = {1..27}
	domain Train = {0n..7n}
	domain Constraint = {-1..1}

	// train missions
	function t =
		[[1,   9, 10, 13, 15, 20, 23],
		 [3,   9, 10, 13, 15, 20, 24],
		 [5,  27, 11, 13, 16, 20, 25],
		 [7,  27, 11, 13, 16, 20, 26],
		 [23, 22, 17, 18, 11,  9,  2],
		 [24, 22, 17, 18, 11,  9,  4],
		 [25, 22, 17, 18, 12, 27,  6],
		 [26, 22, 17, 18, 12, 27,  8]]
	// region A train constraints
	function a =
		[[0, 0, 0,  1,  0, -1, 0],
		 [0, 0, 0,  1,  0, -1, 0],
		 [0, 0, 1, -1,  0,  1, 0],
		 [0, 0, 1, -1,  0,  0, 0],
		 [0, 1, 0,  0, -1,  0, 0],
		 [0, 1, 0,  0, -1,  0, 0],
		 [0, 0, 0, -1,  0,  0, 0],
		 [0, 1, 0, -1,  0,  0, 0]]
	// region B train constraints
	function b =
		[[0, 0, 0,  1,  0, -1, 0],
		 [0, 0, 0,  1,  0, -1, 0],
		 [0, 0, 1, -1,  0,  0, 0],
		 [0, 0, 1, -1,  0,  1, 0],
		 [0, 1, 0,  0, -1,  0, 0],
		 [0, 1, 0,  0, -1,  0, 0],
		 [0, 1, 0, -1,  0,  0, 0],
		 [0, 0, 0, -1,  0,  0, 0]]
	function la = 7
	function lb = 7

	// invariant over sseq: eq(indexOf(sseq, CROSS), 1)

	rule r_move_train =
		if (lt(at(p, ct), 6n)
				and	(forall $t in Train with $t != ct implies
						at(at(t, ct), at(p, ct) + 1n) != at(at(t, $t), at(p, $t)))
				and at(at(a, ct), at(p, ct) + 1n) <= la
				and	at(at(b, ct), at(p, ct) + 1n) <= lb) then
			par
				p := replaceAt(p, ct, at(p, ct) + 1n)
				ra := ra + at(at(a, ct), at(p, ct))
				rb := rb + at(at(b, ct), at(p, ct))
			endpar
		endif

	main rule r_Main = r_move_train[]

default init s0:
	function p = [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]
	function ra = 1
	function rb = 1

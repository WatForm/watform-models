/* The Railway case study - B model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Railway B model.

The Railway B model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Railway B model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Railway B model.  If not, see
<https://www.gnu.org/licenses/>.


The Railway case study (train scheduling deadlock avoidance model) is
described in~\cite{DBLP:journals/sttt/MazzantiFS18} by Frappier et al.
The Railway B model is an adaptation of the original model(s)
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

MACHINE railway

CONSTANTS
    T, A, B

PROPERTIES
    T : 0..7 --> (0..6 --> 1..27) &
    A : 0..7 --> (0..6 --> -1..1) &
    B : 0..7 --> (0..6 --> -1..1) &
    // train missions
    T = { 0 |-> {0|->1, 1|->9, 2|->10, 3|->13, 4|->15, 5|->20, 6|->23},
          1 |-> {0|->3, 1|->9, 2|->10, 3|->13, 4|->15, 5|->20, 6|->24},
          2 |-> {0|->5, 1|->27, 2|->11, 3|->13, 4|->16, 5|->20, 6|->25},
          3 |-> {0|->7, 1|->27, 2|->11, 3|->13, 4|->16, 5|->20, 6|->26},
          4 |-> {0|->23, 1|->22, 2|->17, 3|->18, 4|->11, 5|->9, 6|->2},
          5 |-> {0|->24, 1|->22, 2|->17, 3|->18, 4|->11, 5|->9, 6|->4},
          6 |-> {0|->25, 1|->22, 2|->17, 3|->18, 4|->12, 5|->27, 6|->6},
          7 |-> {0|->26, 1|->22, 2|->17, 3|->18, 4|->12, 5|->27, 6|->8} } &
    // region A train constraints
    A = { 0 |-> {0|->0, 1|->0, 2|->0, 3|->1, 4|->0, 5|->-1, 6|->0},
          1 |-> {0|->0, 1|->0, 2|->0, 3|->1, 4|->0, 5|->-1, 6|->0},
          2 |-> {0|->0, 1|->0, 2|->1, 3|->-1, 4|->0, 5|->1, 6|->0},
          3 |-> {0|->0, 1|->0, 2|->1, 3|->-1, 4|->0, 5|->0, 6|->0},
          4 |-> {0|->0, 1|->1, 2|->0, 3|->0, 4|->-1, 5|->0, 6|->0},
          5 |-> {0|->0, 1|->1, 2|->0, 3|->0, 4|->-1, 5|->0, 6|->0},
          6 |-> {0|->0, 1|->0, 2|->0, 3|->-1, 4|->0, 5|->0, 6|->0},
          7 |-> {0|->0, 1|->1, 2|->0, 3|->-1, 4|->0, 5|->0, 6|->0} } &
    // region B train constraints
    B = { 0 |-> {0|->0, 1|->0, 2|->0, 3|->1, 4|->0, 5|->-1, 6|->0},
          1 |-> {0|->0, 1|->0, 2|->0, 3|->1, 4|->0, 5|->-1, 6|->0},
          2 |-> {0|->0, 1|->0, 2|->1, 3|->-1, 4|->0, 5|->0, 6|->0},
          3 |-> {0|->0, 1|->0, 2|->1, 3|->-1, 4|->0, 5|->1, 6|->0},
          4 |-> {0|->0, 1|->1, 2|->0, 3|->0, 4|->-1, 5|->0, 6|->0},
          5 |-> {0|->0, 1|->1, 2|->0, 3|->0, 4|->-1, 5|->0, 6|->0},
          6 |-> {0|->0, 1|->1, 2|->0, 3|->-1, 4|->0, 5|->0, 6|->0},
          7 |-> {0|->0, 1|->0, 2|->0, 3|->-1, 4|->0, 5|->0, 6|->0} }

DEFINITIONS
    LA == 7;
    LB == 7;
    ASSERT_LTL == "GF({!i. (i : 0..7 => P(i) = 6)})";
    ASSERT_LTL2 == "(WF(choose_train)) & (SF(move_train)) => GF({!i. (i : 0..7 => P(i) = 6)})"

VARIABLES
    P, RA, RB,
    ct // chosen train

INVARIANT
    !i. (i : 0..7 => P(i) : 0..6) &
    RA : 0..8 &
    RB : 0..8 &
    ct : 0..7

INITIALISATION
    P := (0..7) * {0};
    RA, RB := 1, 1;
    ct :: 0..7

OPERATIONS
    move_train =
    PRE
        // ct hasn't reached end of its mission
        P(ct) < 6 &
        // next stop of ct isn't occupied by any other train
        !t. (t : 0..7 & t /= ct =>
               T(ct)(P(ct) + 1) /= T(t)(P(t))) &
        // progress of ct will not saturate A or B
        RA + A(ct)(P(ct) + 1) <= LA &
        RB + B(ct)(P(ct) + 1) <= LB
    THEN
        P(ct) := P(ct) + 1;
        RA := RA + A(ct)(P(ct));
        RB := RB + B(ct)(P(ct))
    END;

    // choose_train = ct :: 0..7
    choose_train =
    IF ct < 7 THEN
       ct := ct + 1
    ELSE
        ct := 0
    END

END

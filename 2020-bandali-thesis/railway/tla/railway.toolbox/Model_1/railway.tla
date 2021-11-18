------------------------------ MODULE railway ------------------------------
(* The Railway case study - TLA+ model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Railway TLA+ model.

The Railway TLA+ model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Railway TLA+ model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Railway TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.


The Railway case study (train scheduling deadlock avoidance model) is
described in~\cite{DBLP:journals/sttt/MazzantiFS18} by Frappier et al.
The Railway TLA+ model is an adaptation of the original model(s)
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

*)

EXTENDS Integers, Sequences, TLC

VARIABLES P, RA, RB, ct
vars == << P, RA, RB, ct >>

trains == 0..7
LA == 7
LB == 7

TypeOK ==
    /\ P \in [trains -> 0..6]
    /\ RA \in 0..8
    /\ RB \in 0..8
    /\ ct \in trains

T ==  \* train missions
    ( 0 :> (0:>1  @@ 1:>9  @@ 2:>10 @@ 3:>13 @@ 4:>15 @@ 5:>20 @@ 6:>23) @@
      1 :> (0:>3  @@ 1:>9  @@ 2:>10 @@ 3:>13 @@ 4:>15 @@ 5:>20 @@ 6:>24) @@
      2 :> (0:>5  @@ 1:>27 @@ 2:>11 @@ 3:>13 @@ 4:>16 @@ 5:>20 @@ 6:>25) @@
      3 :> (0:>7  @@ 1:>27 @@ 2:>11 @@ 3:>13 @@ 4:>16 @@ 5:>20 @@ 6:>26) @@
      4 :> (0:>23 @@ 1:>22 @@ 2:>17 @@ 3:>18 @@ 4:>11 @@ 5:>9  @@ 6:>2)  @@
      5 :> (0:>24 @@ 1:>22 @@ 2:>17 @@ 3:>18 @@ 4:>11 @@ 5:>9  @@ 6:>4)  @@
      6 :> (0:>25 @@ 1:>22 @@ 2:>17 @@ 3:>18 @@ 4:>12 @@ 5:>27 @@ 6:>6)  @@
      7 :> (0:>26 @@ 1:>22 @@ 2:>17 @@ 3:>18 @@ 4:>12 @@ 5:>27 @@ 6:>8) )

A ==  \* region A train constraints
    ( 0 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>1  @@ 4:>0  @@ 5:>-1 @@ 6:>0) @@
      1 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>1  @@ 4:>0  @@ 5:>-1 @@ 6:>0) @@
      2 :> (0:>0 @@ 1:>0 @@ 2:>1 @@ 3:>-1 @@ 4:>0  @@ 5:>1  @@ 6:>0) @@
      3 :> (0:>0 @@ 1:>0 @@ 2:>1 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) @@
      4 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>0  @@ 4:>-1 @@ 5:>0  @@ 6:>0) @@
      5 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>0  @@ 4:>-1 @@ 5:>0  @@ 6:>0) @@
      6 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) @@
      7 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) )

B ==  \* region B train constraints
    ( 0 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>1  @@ 4:>0  @@ 5:>-1 @@ 6:>0) @@
      1 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>1  @@ 4:>0  @@ 5:>-1 @@ 6:>0) @@
      2 :> (0:>0 @@ 1:>0 @@ 2:>1 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) @@
      3 :> (0:>0 @@ 1:>0 @@ 2:>1 @@ 3:>-1 @@ 4:>0  @@ 5:>1  @@ 6:>0) @@
      4 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>0  @@ 4:>-1 @@ 5:>0  @@ 6:>0) @@
      5 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>0  @@ 4:>-1 @@ 5:>0  @@ 6:>0) @@
      6 :> (0:>0 @@ 1:>1 @@ 2:>0 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) @@
      7 :> (0:>0 @@ 1:>0 @@ 2:>0 @@ 3:>-1 @@ 4:>0  @@ 5:>0  @@ 6:>0) )

Init ==
    /\ P = [t \in trains |-> 0]
    /\ RA = 1
    /\ RB = 1
    /\ ct \in trains

move_train ==
    /\ /\ P[ct] < 6
       /\ \A t \in trains:
           t # ct => T[ct][P[ct] + 1] # T[t][P[t]]
       /\ RA + A[ct][P[ct] + 1] <= LA
       /\ RB + B[ct][P[ct] + 1] <= LB
    /\ P' = [P EXCEPT ![ct] = P[ct] + 1]
    /\ RA' = RA + A[ct][P'[ct]]
    /\ RB' = RB + B[ct][P'[ct]]
    /\ UNCHANGED ct

choose_train ==
    /\ IF ct < 7
          THEN ct' = ct + 1
          ELSE ct' = 0
    /\ UNCHANGED << P, RA, RB >>

Next ==
    \/ move_train
    \/ choose_train

Spec ==
    /\ Init /\ [][Next]_vars
    /\ SF_vars(move_train)
    /\ WF_vars(choose_train)

ASSERT_LTL == []<>(\A t \in trains: P[t] = 6)

=============================================================================
\* Modification History
\* Last modified Wed Oct 27 22:01:56 EDT 2021 by bandali
\* Created Wed Jan 22 01:12:38 EST 2020 by bandali

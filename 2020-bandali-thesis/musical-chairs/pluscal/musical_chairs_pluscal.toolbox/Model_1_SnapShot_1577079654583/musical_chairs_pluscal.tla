----------------------- MODULE musical_chairs_pluscal -----------------------
(* The Musical Chairs case study - PlusCal model

Copyright (c) 2018 Jose Serna <jserna@uwaterloo.ca>
Copyright (c) 2018 Nancy Day <nday@uwaterloo.ca>
Copyright (c) 2018-2020 Amin Bandali <bandali@uwaterloo.ca>

This file is part of the Musical Chairs PlusCal model.

The Musical Chairs PlusCal model is free software: you can
redistribute it and/or modify it under the terms of the GNU General
Public License as published by the Free Software Foundation, either
version 3 of the License, or (at your option) any later version.

The Musical Chairs PlusCal model is distributed in the hope that it
will be useful, but WITHOUT ANY WARRANTY; without even the implied
warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See
the GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Musical Chairs PlusCal model.  If not, see
<https://www.gnu.org/licenses/>.


The Musical Chairs case study is described in~\cite{Nissanke_1999} by
Nissanke.  The Musical Chairs PlusCal model is an adaptation of the
original model(s) presented there.

@Book{Nissanke_1999,
  author    = {Nissanke, Nimal},
  title     = {Formal Specification: Techniques and Applications},
  year      = 1999,
  doi       = {10.1007/978-1-4471-0791-0},
  url       = {http://dx.doi.org/10.1007/978-1-4471-0791-0},
  isbn      = 9781447107910,
  publisher = {Springer London}
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

EXTENDS Integers, FiniteSets, TLC, Sequences

CONSTANTS CHAIRS, PLAYERS

STATE_ == { "Start", "Walking", "Sitting", "Won" }

\* Helper predicate for range of a function
Range(f) == {f[x]: x \in DOMAIN f}

(* --algorithm musical_chairs_pluscal
variables activePlayers = PLAYERS,
          activeChairs = CHAIRS,
          occupied = <<>>,
          musicPlaying = TRUE,
          state = "Start";

fair+ process Walk = "Walk"
begin
    walk:
        await
            /\ state = "Start"
            /\ musicPlaying
            /\ Cardinality(activePlayers) > 1;
        occupied := <<>>;
        state := "Walking";
        goto walk
end process

fair+ process Sit = "Sit"
\* variable loser = CHOOSE l \in activePlayers: TRUE;
begin
    sit:
        await
            /\ state = "Walking"
            /\ ~musicPlaying;
        occupied := CHOOSE o \in [activeChairs -> activePlayers]:
                        /\ (\A c \in activeChairs,
                              p1 \in activePlayers,
                              p2 \in activePlayers:
                               o[c] = p1 /\ o[c] = p2 => p1 = p2)
                        /\ (\A p \in Range(o),
                              c1 \in DOMAIN o,
                              c2 \in DOMAIN o:
                               o[c1] = p /\ o[c2] = p => c1 = c2);
        assert(\E p \in activePlayers: p \notin Range(occupied));
        state := "Sitting";
        goto sit
end process

fair+ process EliminateLoser = "EliminateLoser"
variable oldCard = Cardinality(activeChairs);
begin
    eliminateloser:
        await
            /\ state = "Sitting"
            /\ Cardinality(activePlayers) > 1
            /\ Cardinality(activePlayers) - Cardinality(Range(occupied)) = 1;
        activePlayers := Range(occupied);
        activeChairs := activeChairs \ {CHOOSE c \in activeChairs : TRUE};
        assert(Cardinality(activeChairs) = oldCard - 1);
        occupied := <<>>;
        state := "Start";
        goto eliminateloser
end process

fair+ process Win = "Win"
begin
    win:
        await
            /\ state = "Sitting"
            /\ Cardinality(activePlayers) = 1;
        state := "Won"
end process

fair process ChangeMusicPlaying = "ChangeMusicPlaying"
begin
    cmp:
        await state \in {"Start", "Walking"};
        musicPlaying := ~musicPlaying;
        goto cmp
end process

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES activePlayers, activeChairs, occupied, musicPlaying, state, pc, 
          oldCard

vars == << activePlayers, activeChairs, occupied, musicPlaying, state, pc, 
           oldCard >>

ProcSet == {"Walk"} \cup {"Sit"} \cup {"EliminateLoser"} \cup {"Win"} \cup {"ChangeMusicPlaying"}

Init == (* Global variables *)
        /\ activePlayers = PLAYERS
        /\ activeChairs = CHAIRS
        /\ occupied = <<>>
        /\ musicPlaying = TRUE
        /\ state = "Start"
        (* Process EliminateLoser *)
        /\ oldCard = Cardinality(activeChairs)
        /\ pc = [self \in ProcSet |-> CASE self = "Walk" -> "walk"
                                        [] self = "Sit" -> "sit"
                                        [] self = "EliminateLoser" -> "eliminateloser"
                                        [] self = "Win" -> "win"
                                        [] self = "ChangeMusicPlaying" -> "cmp"]

walk == /\ pc["Walk"] = "walk"
        /\ /\ state = "Start"
           /\ musicPlaying
           /\ Cardinality(activePlayers) > 1
        /\ occupied' = <<>>
        /\ state' = "Walking"
        /\ pc' = [pc EXCEPT !["Walk"] = "walk"]
        /\ UNCHANGED << activePlayers, activeChairs, musicPlaying, oldCard >>

Walk == walk

sit == /\ pc["Sit"] = "sit"
       /\ /\ state = "Walking"
          /\ ~musicPlaying
       /\ occupied' = (CHOOSE o \in [activeChairs -> activePlayers]:
                           /\ (\A c \in activeChairs,
                                 p1 \in activePlayers,
                                 p2 \in activePlayers:
                                  o[c] = p1 /\ o[c] = p2 => p1 = p2)
                           /\ (\A p \in Range(o),
                                 c1 \in DOMAIN o,
                                 c2 \in DOMAIN o:
                                  o[c1] = p /\ o[c2] = p => c1 = c2))
       /\ Assert((\E p \in activePlayers: p \notin Range(occupied')), 
                 "Failure of assertion at line 47, column 9.")
       /\ state' = "Sitting"
       /\ pc' = [pc EXCEPT !["Sit"] = "sit"]
       /\ UNCHANGED << activePlayers, activeChairs, musicPlaying, oldCard >>

Sit == sit

eliminateloser == /\ pc["EliminateLoser"] = "eliminateloser"
                  /\ /\ state = "Sitting"
                     /\ Cardinality(activePlayers) > 1
                     /\ Cardinality(activePlayers) - Cardinality(Range(occupied)) = 1
                  /\ activePlayers' = Range(occupied)
                  /\ activeChairs' = activeChairs \ {CHOOSE c \in activeChairs : TRUE}
                  /\ Assert((Cardinality(activeChairs') = oldCard - 1), 
                            "Failure of assertion at line 62, column 9.")
                  /\ occupied' = <<>>
                  /\ state' = "Start"
                  /\ pc' = [pc EXCEPT !["EliminateLoser"] = "eliminateloser"]
                  /\ UNCHANGED << musicPlaying, oldCard >>

EliminateLoser == eliminateloser

win == /\ pc["Win"] = "win"
       /\ /\ state = "Sitting"
          /\ Cardinality(activePlayers) = 1
       /\ state' = "Won"
       /\ pc' = [pc EXCEPT !["Win"] = "Done"]
       /\ UNCHANGED << activePlayers, activeChairs, occupied, musicPlaying, 
                       oldCard >>

Win == win

cmp == /\ pc["ChangeMusicPlaying"] = "cmp"
       /\ state \in {"Start", "Walking"}
       /\ musicPlaying' = ~musicPlaying
       /\ pc' = [pc EXCEPT !["ChangeMusicPlaying"] = "cmp"]
       /\ UNCHANGED << activePlayers, activeChairs, occupied, state, oldCard >>

ChangeMusicPlaying == cmp

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Walk \/ Sit \/ EliminateLoser \/ Win \/ ChangeMusicPlaying
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(Walk)
        /\ SF_vars(Sit)
        /\ SF_vars(EliminateLoser)
        /\ SF_vars(Win)
        /\ WF_vars(ChangeMusicPlaying)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Typing invariant
TypeOK ==
    /\ activePlayers  \subseteq PLAYERS
    /\ activeChairs   \subseteq CHAIRS
    /\ occupied \in [activeChairs -> activePlayers] \union {<<>>}
    /\ musicPlaying \in BOOLEAN  \* whether music is playing
    /\ state \in STATE_

\* Safety invariants

OneMorePlayerThanChairs ==
    Cardinality(activePlayers) = Cardinality(activeChairs) + 1

\* Temporal properties

ExistentialLiveness ==
    \E p \in PLAYERS: <> (activePlayers = {p})

FiniteLiveness == <> ENABLED Sit

InfiniteLiveness == <>[](Cardinality(activePlayers) = 1)

=============================================================================
\* Modification History
\* Last modified Mon Dec 23 00:40:49 EST 2019 by bandali
\* Created Sun Dec 22 02:24:10 EST 2019 by bandali

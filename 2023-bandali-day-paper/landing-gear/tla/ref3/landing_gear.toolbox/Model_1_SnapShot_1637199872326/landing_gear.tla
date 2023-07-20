---------------------------- MODULE landing_gear ----------------------------
(* The Landing Gear case study - TLA+ model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Landing Gear TLA+ model.

The Landing Gear TLA+ model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Landing Gear TLA+ model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Landing Gear TLA+ model.  If not, see
<https://www.gnu.org/licenses/>.


The Landing Gear management case study is described in
\cite{DBLP:conf/asm/BoniolW14} by Boniol et al.

@inproceedings{DBLP:conf/asm/BoniolW14,
  author    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels},
  editor    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels and
               Yamine A{\"{\i}}t Ameur and
               Klaus{-}Dieter Schewe},
  title     = {The Landing Gear System Case Study},
  booktitle = {{ABZ} 2014: The Landing Gear Case Study - Case Study Track, Held at
               the 4th International Conference on Abstract State Machines, Alloy,
               B, TLA, VDM, and Z, Toulouse, France, June 2-6, 2014. Proceedings},
  series    = {Communications in Computer and Information Science},
  volume    = {433},
  pages     = {1--18},
  publisher = {Springer},
  year      = {2014},
  url       = {https://doi.org/10.1007/978-3-319-07512-9\_1},
  doi       = {10.1007/978-3-319-07512-9\_1},
  timestamp = {Tue, 07 May 2019 12:19:36 +0200},
  biburl    = {https://dblp.org/rec/conf/asm/BoniolW14.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

The Landing Gear TLA+ model is an adaptation of the AsmetaL one
described in \cite{DBLP:conf/asm/ArcainiGR14} by Arcaini et al.

@inproceedings{DBLP:conf/asm/ArcainiGR14,
  author    = {Paolo Arcaini and
               Angelo Gargantini and
               Elvinia Riccobene},
  editor    = {Fr{\'{e}}d{\'{e}}ric Boniol and
               Virginie Wiels and
               Yamine A{\"{\i}}t Ameur and
               Klaus{-}Dieter Schewe},
  title     = {Modeling and Analyzing Using ASMs: The Landing Gear System Case Study},
  booktitle = {{ABZ} 2014: The Landing Gear Case Study - Case Study Track, Held at
               the 4th International Conference on Abstract State Machines, Alloy,
               B, TLA, VDM, and Z, Toulouse, France, June 2-6, 2014. Proceedings},
  series    = {Communications in Computer and Information Science},
  volume    = {433},
  pages     = {36--51},
  publisher = {Springer},
  year      = {2014},
  url       = {https://doi.org/10.1007/978-3-319-07512-9\_3},
  doi       = {10.1007/978-3-319-07512-9\_3},
  timestamp = {Wed, 29 May 2019 09:35:57 +0200},
  biburl    = {https://dblp.org/rec/conf/asm/ArcainiGR14.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}

This model has appeared in the following publications:

TODO

*)

VARIABLES handle, doors, gears

vars == << handle, doors, gears >>

HandleStatus == { "UP", "DOWN" }
DoorStatus == { "CLOSED", "OPENING", "OPEN", "CLOSING" }
GearStatus == { "RETRACTED", "EXTENDING", "EXTENDED", "RETRACTING" }

TypeOK ==
    /\ handle \in HandleStatus
    /\ doors \in DoorStatus
    /\ gears \in GearStatus


close_door ==
    /\ doors' =
        CASE doors = "OPEN" -> "CLOSING"
          [] doors = "CLOSING" -> "CLOSED"
          [] doors = "OPENING" -> "CLOSING"
          [] doors = "CLOSED" -> "CLOSED" \* missing in ASM model


retraction_sequence ==
    /\ IF gears # "RETRACTED"
       THEN
           IF doors = "OPEN"
           THEN /\ gears' = (CASE gears = "EXTENDED" -> "RETRACTING"
                               [] gears = "RETRACTING" -> "RETRACTED"
                               [] gears = "EXTENDING" -> "RETRACTING")
                /\ doors' = doors
           ELSE /\ doors' = (CASE doors = "CLOSED" -> "OPENING"
                               [] doors = "CLOSING" -> "OPENING"
                               [] doors = "OPENING" -> "OPEN")
                /\ gears' = gears
       ELSE /\ close_door
            /\ gears' = gears
    /\ UNCHANGED handle

outgoing_sequence ==
    /\ IF gears # "EXTENDED"
       THEN /\ IF doors = "OPEN"
               THEN /\ gears' = (CASE gears = "RETRACTED" -> "EXTENDING"
                                   [] gears = "EXTENDING" -> "EXTENDED"
                                   [] gears = "RETRACTING" -> "EXTENDING")
                    /\ doors' = doors
               ELSE /\ doors' = (CASE doors = "CLOSED" -> "OPENING"
                                   [] doors = "OPENING" -> "OPEN"
                                   [] doors = "CLOSING" -> "OPENING")
                    /\ gears' = gears
       ELSE /\ close_door
            /\ gears' = gears
    /\ UNCHANGED handle

toggle_handle ==
    /\ IF handle = "UP"
       THEN handle' = "DOWN"
       ELSE handle' = "UP"
    /\ UNCHANGED << doors, gears >>


\* Spec

Init ==
    /\ handle \in HandleStatus
    /\ doors = "CLOSED"
    /\ gears = "EXTENDED"

Next ==
    \/ IF handle = "UP"
       THEN retraction_sequence
       ELSE outgoing_sequence
    \/ toggle_handle

Spec == Init /\ [][Next]_vars
    /\ SF_vars(retraction_sequence)
    /\ SF_vars(outgoing_sequence)
    /\ WF_vars(toggle_handle)


\* Invariants

Inv1 ==
  (gears = "EXTENDING" \/ gears = "RETRACTING") => doors = "OPEN"
Inv2 ==
  doors = "CLOSED" => (gears = "EXTENDED" \/ gears = "RETRACTED")


\* Temporal properties

Inv3 ==
  []([](handle = "DOWN") =>
       <>(gears = "EXTENDED" /\ doors = "CLOSED"))
Inv4 ==
  []([](handle = "UP") =>
       <>(gears = "RETRACTED" /\ doors = "CLOSED"))
Inv5 ==
  []([](handle = "DOWN") => <>(gears # "RETRACTING"))
Inv6 ==
  []([](handle = "UP") => <>(gears # "EXTENDING"))

=============================================================================
\* Modification History
\* Last modified Wed Nov 17 20:44:26 EST 2021 by bandali
\* Created Thu Nov 11 12:31:13 EST 2021 by bandali

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

VARIABLES handle,  \* monitored
          doors, gears, general_electro_valve,
          open_doors_electro_valve, close_doors_electro_valve,
          retract_gears_electro_valve, extend_gears_electro_valve,
          \* === sensors ===
          \* gears_extended is true if the corresponding gear is
          \* locked in the extended position and false in other
          \* cases
          gears_extended, \* monitored
          \* gears_retracted is true if the corresponding gear is
          \* locked in the retracted position and false in other
          \* cases
          gears_retracted, \* monitored
          \* doors_closed is true if and only if the corresponding
          \* door is locked closed
           doors_closed, \* monitored
          \* doors_open is true if and only if the corresponding
          \* door is locked open
          doors_open \* monitored
          

vars == << handle, doors, gears, general_electro_valve,
          open_doors_electro_valve, close_doors_electro_valve,
          retract_gears_electro_valve, extend_gears_electro_valve,
          gears_extended, gears_retracted, doors_closed, doors_open >>

HandleStatus == { "UP", "DOWN" }
DoorStatus == { "CLOSED", "OPENING", "OPEN", "CLOSING" }
GearStatus == { "RETRACTED", "EXTENDING", "EXTENDED", "RETRACTING" }
CylinderStatus == { "CYLINDER_RETRACTED", "CYLINDER_EXTENDING",
                    "CYLINDER_EXTENDED", "CYLINDER_RETRACTING" }


\* "derived" functions (macro-like)

cylinders_doors ==
    CASE doors = "OPEN" -> "CYLINDER_EXTENDED"
      [] doors = "OPENING" -> "CYLINDER_EXTENDING"
      [] doors = "CLOSING" -> "CYLINDER_RETRACTING"
      [] doors = "CLOSED" -> "CYLINDER_RETRACTED"

cylinders_gears ==
    CASE gears = "RETRACTED" -> "CYLINDER_RETRACTED"
      [] gears = "EXTENDING" -> "CYLINDER_EXTENDING"
      [] gears = "EXTENDED" -> "CYLINDER_EXTENDED"
      [] gears = "RETRACTING" -> "CYLINDER_RETRACTING"


TypeOK ==
    /\ handle \in HandleStatus
    /\ doors \in DoorStatus
    /\ gears \in GearStatus
    /\ general_electro_valve \in BOOLEAN
    /\ open_doors_electro_valve \in BOOLEAN
    /\ close_doors_electro_valve \in BOOLEAN
    /\ retract_gears_electro_valve \in BOOLEAN
    /\ extend_gears_electro_valve \in BOOLEAN
    /\ gears_extended \in BOOLEAN
    /\ gears_retracted \in BOOLEAN
    /\ doors_closed \in BOOLEAN
    /\ doors_open \in BOOLEAN    
    /\ cylinders_doors \in CylinderStatus
    /\ cylinders_gears \in CylinderStatus


close_door ==
    /\ doors' =
        CASE doors = "OPEN" -> "CLOSING"
          [] doors = "CLOSING" -> IF doors_closed THEN "CLOSED" ELSE doors
          [] doors = "OPENING" -> "CLOSING"
          [] doors = "CLOSED" -> "CLOSED" \* missing in ASM model
    /\ general_electro_valve' =
        CASE doors' = "OPEN" -> general_electro_valve
          [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE general_electro_valve
          [] doors' = "OPENING" -> general_electro_valve
          [] doors' = "CLOSED" -> general_electro_valve
    /\ close_doors_electro_valve' =
        CASE doors' = "OPEN" -> TRUE
          [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE close_doors_electro_valve
          [] doors' = "OPENING" -> TRUE
          [] doors' = "CLOSED" -> close_doors_electro_valve
    /\ open_doors_electro_valve' =
        CASE doors' = "OPEN" -> open_doors_electro_valve
          [] doors' = "CLOSING" -> open_doors_electro_valve
          [] doors' = "OPENING" -> FALSE
          [] doors' = "CLOSED" -> open_doors_electro_valve


retraction_sequence ==
    /\ IF gears # "RETRACTED"
       THEN
           IF doors = "OPEN"
           THEN /\ gears' =
                    (CASE gears = "EXTENDED" -> "RETRACTING"
                       [] gears = "RETRACTING" -> IF gears_retracted THEN "RETRACTED" ELSE gears
                       [] gears = "EXTENDING" -> "RETRACTING"
                       [] gears = "RETRACTED" -> "RETRACTED") \* missing in ASM model
                /\ retract_gears_electro_valve' =
                    (CASE gears' = "EXTENDED" -> TRUE
                       [] gears' = "RETRACTING" -> IF gears_retracted THEN FALSE ELSE retract_gears_electro_valve
                       [] gears' = "EXTENDING" -> TRUE
                       [] gears' = "RETRACTED" -> retract_gears_electro_valve) \* missing in ASM model
                /\ extend_gears_electro_valve' =
                    (CASE gears' = "EXTENDED" -> extend_gears_electro_valve
                       [] gears' = "RETRACTING" -> extend_gears_electro_valve
                       [] gears' = "EXTENDING" -> FALSE
                       [] gears' = "RETRACTED" -> extend_gears_electro_valve) \* missing in ASM model
                /\ UNCHANGED << doors,
                                general_electro_valve,
                                open_doors_electro_valve,
                                close_doors_electro_valve >>
           ELSE /\ doors' =
                    (CASE doors = "CLOSED" -> "OPENING"
                       [] doors = "CLOSING" -> "OPENING"
                       [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors)
                /\ general_electro_valve' =
                    (CASE doors' = "CLOSED" -> TRUE
                       [] doors' = "CLOSING" -> general_electro_valve
                       [] doors' = "OPENING" -> general_electro_valve
                       [] doors' = "OPEN" -> general_electro_valve) \* missing in ASM model
                /\ close_doors_electro_valve' =
                    (CASE doors' = "CLOSED" -> close_doors_electro_valve
                       [] doors' = "CLOSING" -> FALSE
                       [] doors' = "OPENING" -> close_doors_electro_valve
                       [] doors' = "OPEN" -> close_doors_electro_valve) \* missing in ASM model
                /\ open_doors_electro_valve' =
                    (CASE doors' = "CLOSED" -> TRUE
                       [] doors' = "CLOSING" -> TRUE
                       [] doors' = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
                       [] doors' = "OPEN" -> open_doors_electro_valve) \* missing in ASM model
                /\ UNCHANGED << gears,
                                retract_gears_electro_valve,
                                extend_gears_electro_valve >>
       ELSE /\ close_door
            /\ UNCHANGED << gears,
                            retract_gears_electro_valve,
                            extend_gears_electro_valve >>
    /\ UNCHANGED << handle,
                    gears_extended, gears_retracted,
                    doors_closed, doors_open >>

outgoing_sequence ==
    /\ IF gears # "EXTENDED"
       THEN /\ IF doors = "OPEN"
               THEN /\ gears' =
                        (CASE gears = "RETRACTED" -> "EXTENDING"
                           [] gears = "EXTENDING" -> IF gears_extended THEN "EXTENDED" ELSE gears
                           [] gears = "RETRACTING" -> "EXTENDING"
                           [] gears = "EXTENDED" -> gears) \* missing in ASM model
                    /\ extend_gears_electro_valve' =
                        (CASE gears' = "RETRACTED" -> TRUE
                           [] gears' = "EXTENDING" -> IF gears_extended THEN FALSE ELSE extend_gears_electro_valve
                           [] gears' = "RETRACTING" -> TRUE
                           [] gears' = "EXTENDED" -> extend_gears_electro_valve) \* missing in ASM model
                    /\ retract_gears_electro_valve' =
                        (CASE gears' = "RETRACTED" -> retract_gears_electro_valve
                           [] gears' = "EXTENDING" -> retract_gears_electro_valve
                           [] gears' = "RETRACTING" -> FALSE
                           [] gears' = "EXTENDED" -> retract_gears_electro_valve) \* missing in ASM model
                    /\ UNCHANGED << doors,
                                    general_electro_valve,
                                    open_doors_electro_valve >>
               ELSE /\ doors' =
                        (CASE doors = "CLOSED" -> "OPENING"
                           [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors
                           [] doors = "CLOSING" -> "OPENING") \* missing in ASM model
                    /\ general_electro_valve' =
                        (CASE doors' = "CLOSED" -> TRUE
                           [] doors' = "OPENING" -> general_electro_valve
                           [] doors' = "CLOSING" -> general_electro_valve
                           [] doors' = "OPEN" -> general_electro_valve) \* missing in ASM model
                    /\ open_doors_electro_valve' =
                        (CASE doors' = "CLOSED" -> TRUE
                           [] doors' = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
                           [] doors' = "CLOSING" -> open_doors_electro_valve
                           [] doors' = "OPEN" -> open_doors_electro_valve) \* missing in ASM model
                    /\ UNCHANGED << gears,
                                    retract_gears_electro_valve,
                                    extend_gears_electro_valve >>
            /\ UNCHANGED close_doors_electro_valve
       ELSE /\ close_door
            /\ UNCHANGED << gears,
                            retract_gears_electro_valve,
                            extend_gears_electro_valve >>
    /\ UNCHANGED << handle,
                    gears_extended, gears_retracted,
                    doors_closed, doors_open >>

toggle_handle ==
    /\ IF handle = "UP"
       THEN handle' = "DOWN"
       ELSE handle' = "UP"
    /\ UNCHANGED << doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    gears_extended, gears_retracted,
                    doors_closed, doors_open >>

toggle_gears_extended ==
    /\ IF gears_extended
       THEN gears_extended' = FALSE
       ELSE gears_extended' = TRUE
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    gears_retracted,
                    doors_closed, doors_open >>

toggle_gears_retracted ==
    /\ IF gears_retracted
       THEN gears_retracted' = FALSE
       ELSE gears_retracted' = TRUE
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    gears_extended,
                    doors_closed, doors_open >>

toggle_doors_closed ==
    /\ IF doors_closed
       THEN doors_closed' = FALSE
       ELSE doors_closed' = TRUE
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    gears_extended, gears_retracted,
                    doors_open >>

toggle_doors_open ==
    /\ IF doors_open
       THEN doors_open' = FALSE
       ELSE doors_open' = TRUE
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    gears_extended, gears_retracted,
                    doors_closed >>


\* Spec

Init ==
    /\ handle \in HandleStatus
    /\ doors = "CLOSED"
    /\ gears = "EXTENDED"
    /\ general_electro_valve = FALSE
    /\ open_doors_electro_valve = FALSE
    /\ close_doors_electro_valve = FALSE
    /\ retract_gears_electro_valve = FALSE
    /\ extend_gears_electro_valve = FALSE
    /\ gears_extended \in BOOLEAN
    /\ gears_retracted \in BOOLEAN
    /\ doors_closed \in BOOLEAN
    /\ doors_open \in BOOLEAN
    

Next ==
    \/ IF handle = "UP"
       THEN retraction_sequence
       ELSE outgoing_sequence
    \/ toggle_handle
    \/ toggle_gears_extended \/ toggle_gears_retracted
    \/ toggle_doors_closed \/ toggle_doors_open

Spec == Init /\ [][Next]_vars
    /\ SF_vars(retraction_sequence)
    /\ SF_vars(outgoing_sequence)
    /\ WF_vars(toggle_handle)
    /\ WF_vars(toggle_gears_extended)
    /\ WF_vars(toggle_gears_retracted)
    /\ WF_vars(toggle_doors_closed)
    /\ WF_vars(toggle_doors_open)


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

Inv7 == \* R31
  []((extend_gears_electro_valve \/ retract_gears_electro_valve) =>
      doors = "OPEN")
Inv8 == \* R31
  []((open_doors_electro_valve \/ close_doors_electro_valve) =>
      (gears = "RETRACTED" \/ gears = "EXTENDED"))
Inv9 == \* R41
  [](~(open_doors_electro_valve /\ close_doors_electro_valve))
Inv10 == \* R42
  [](~(extend_gears_electro_valve /\ retract_gears_electro_valve))
Inv11 == \* R51
  []((\/ open_doors_electro_valve
      \/ close_doors_electro_valve
      \/ extend_gears_electro_valve
      \/ retract_gears_electro_valve) => general_electro_valve)

=============================================================================
\* Modification History
\* Last modified Wed Nov 17 23:24:08 EST 2021 by bandali
\* Created Thu Nov 11 12:31:13 EST 2021 by bandali

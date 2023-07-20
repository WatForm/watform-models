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
          \* f_gears_extended is true if the corresponding gear is
          \* locked in the extended position and false in other
          \* cases
          f_gears_extended, \* monitored
          \* f_gears_retracted is true if the corresponding gear is
          \* locked in the retracted position and false in other
          \* cases
          f_gears_retracted, \* monitored
          \* f_doors_closed is true if and only if the corresponding
          \* door is locked closed
          f_doors_closed, \* monitored
          \* f_doors_open is true if and only if the corresponding
          \* door is locked open
          f_doors_open, \* monitored
          timeout, \* monitored
          anomaly
          

vars == << handle, doors, gears, general_electro_valve,
          open_doors_electro_valve, close_doors_electro_valve,
          retract_gears_electro_valve, extend_gears_electro_valve,
          f_gears_extended, f_gears_retracted, f_doors_closed,
          f_doors_open, timeout, anomaly >>

LandingSet == { "FRONT", "LEFT", "RIGHT" }
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

gears_extended ==
  \A s \in LandingSet: f_gears_extended[s]

gears_retracted ==
  \A s \in LandingSet: f_gears_retracted[s]

doors_closed ==
  \A s \in LandingSet: f_doors_closed[s]

doors_open ==
  \A s \in LandingSet: f_doors_open[s]

a_gear_extended ==
  \E s \in LandingSet: f_gears_extended[s]

a_gear_retracted ==
  \E s \in LandingSet: f_gears_retracted[s]

a_door_closed ==
  \E s \in LandingSet: f_doors_closed[s]

a_door_open ==
  \E s \in LandingSet: f_doors_open[s]

green_light == gears = "EXTENDED"

orange_light == gears = "EXTENDING" \/ gears = "RETRACTING"

red_light == anomaly


TypeOK ==
    /\ handle \in HandleStatus
    /\ doors \in DoorStatus
    /\ gears \in GearStatus
    /\ general_electro_valve \in BOOLEAN
    /\ open_doors_electro_valve \in BOOLEAN
    /\ close_doors_electro_valve \in BOOLEAN
    /\ retract_gears_electro_valve \in BOOLEAN
    /\ extend_gears_electro_valve \in BOOLEAN
    /\ f_gears_extended \in [LandingSet -> BOOLEAN]
    /\ f_gears_retracted \in [LandingSet -> BOOLEAN]
    /\ f_doors_closed \in [LandingSet -> BOOLEAN]
    /\ f_doors_open \in [LandingSet -> BOOLEAN]
    /\ timeout \in BOOLEAN
    /\ anomaly \in BOOLEAN
    /\ gears_extended \in BOOLEAN
    /\ gears_retracted \in BOOLEAN
    /\ doors_closed \in BOOLEAN
    /\ doors_open \in BOOLEAN
    /\ a_gear_extended \in BOOLEAN
    /\ a_gear_retracted \in BOOLEAN
    /\ a_door_closed \in BOOLEAN
    /\ a_door_open \in BOOLEAN
    /\ green_light \in BOOLEAN
    /\ orange_light \in BOOLEAN
    /\ red_light \in BOOLEAN
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
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, f_doors_open, timeout, anomaly >>

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
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, f_doors_open, timeout, anomaly >>

health_monitoring ==
    /\ IF (\/ open_doors_electro_valve /\ a_door_closed /\ timeout
           \/ open_doors_electro_valve /\ ~(doors_open) /\ timeout
           \/ close_doors_electro_valve /\ a_door_open /\ timeout
           \/ close_doors_electro_valve /\ ~(doors_closed) /\ timeout
           \/ retract_gears_electro_valve /\ a_gear_extended /\ timeout
           \/ retract_gears_electro_valve /\ ~(gears_retracted) /\ timeout
           \/ extend_gears_electro_valve /\ a_gear_retracted /\ timeout
           \/ extend_gears_electro_valve /\ ~(gears_extended) /\ timeout)
       THEN anomaly' = TRUE
       ELSE UNCHANGED anomaly
    /\ UNCHANGED << handle, doors, gears, 
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, f_doors_open, timeout >>

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
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, f_doors_open, anomaly, timeout >>

toggle_gears_extended(s) ==
    /\ IF f_gears_extended[s]
       THEN f_gears_extended' = [f_gears_extended EXCEPT ![s] = FALSE]
       ELSE f_gears_extended' = [f_gears_extended EXCEPT ![s] = TRUE]
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_retracted,
                    f_doors_closed, f_doors_open, anomaly, timeout >>

toggle_gears_retracted(s) ==
    /\ IF f_gears_retracted[s]
       THEN f_gears_retracted' = [f_gears_retracted EXCEPT ![s] = FALSE]
       ELSE f_gears_retracted' = [f_gears_retracted EXCEPT ![s] = TRUE]
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_extended,
                    f_doors_closed, f_doors_open, anomaly, timeout >>

toggle_doors_closed(s) ==
    /\ IF f_doors_closed[s]
       THEN f_doors_closed' = [f_doors_closed EXCEPT ![s] = FALSE]
       ELSE f_doors_closed' = [f_doors_closed EXCEPT ![s] = TRUE]
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_extended, f_gears_retracted,
                    f_doors_open, anomaly, timeout >>

toggle_doors_open(s) ==
    /\ IF f_doors_open[s]
       THEN f_doors_open' = [f_doors_open EXCEPT ![s] = FALSE]
       ELSE f_doors_open' = [f_doors_open EXCEPT ![s] = TRUE]
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, anomaly, timeout >>

toggle_timeout ==
    /\ IF timeout
       THEN timeout' = FALSE
       ELSE timeout' = TRUE
    /\ UNCHANGED << handle, doors, gears,
                    general_electro_valve,
                    open_doors_electro_valve,
                    close_doors_electro_valve,
                    retract_gears_electro_valve,
                    extend_gears_electro_valve,
                    f_gears_extended, f_gears_retracted,
                    f_doors_closed, f_doors_open, anomaly >>


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
    /\ f_gears_extended \in [LandingSet -> BOOLEAN]
    /\ f_gears_retracted \in [LandingSet -> BOOLEAN]
    /\ f_doors_closed \in [LandingSet -> BOOLEAN]
    /\ f_doors_open \in [LandingSet -> BOOLEAN]
    /\ timeout \in BOOLEAN
    /\ anomaly = FALSE
    

Next ==
    \/ IF ~(anomaly) THEN
        /\ IF handle = "UP"
           THEN retraction_sequence
           ELSE outgoing_sequence
        /\ health_monitoring
       ELSE TRUE
    \/ toggle_handle
    \/ (\E s \in LandingSet:
        \/ toggle_gears_extended(s)
        \/ toggle_gears_retracted(s)
        \/ toggle_doors_closed(s)
        \/ toggle_doors_open(s))
    \/ toggle_timeout

Spec == Init /\ [][Next]_vars
    /\ SF_vars(retraction_sequence)
    /\ SF_vars(outgoing_sequence)
    /\ SF_vars(health_monitoring)
    /\ WF_vars(toggle_handle)
    /\ (\A s \in LandingSet:
        /\ WF_vars(toggle_gears_extended(s))
        /\ WF_vars(toggle_gears_retracted(s))
        /\ WF_vars(toggle_doors_closed(s))
        /\ WF_vars(toggle_doors_open(s)))
    \* /\ WF_vars(Next)
    /\ WF_vars(toggle_timeout)


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

Inv12 == \* R61 (not an exact match, since TLA+ does not have next)
  []((open_doors_electro_valve /\ a_door_closed /\ timeout) =>
      <>(anomaly))
Inv13 == \* R62 (not an exact match, since TLA+ does not have next)
  []((close_doors_electro_valve /\ a_door_open /\ timeout) =>
      <>(anomaly))
Inv14 == \* R63 (not an exact match, since TLA+ does not have next)
  []((retract_gears_electro_valve /\ a_gear_extended /\ timeout) =>
      <>(anomaly))
Inv15 == \* R64 (not an exact match, since TLA+ does not have next)
  []((extend_gears_electro_valve /\ a_gear_retracted /\ timeout) =>
      <>(anomaly))

Inv16 == \* R71 (not an exact match, since TLA+ does not have next)
  []((open_doors_electro_valve /\ ~(doors_open) /\ timeout) =>
      <>(anomaly))
Inv17 == \* R72 (not an exact match, since TLA+ does not have next)
  []((close_doors_electro_valve /\ ~(doors_closed) /\ timeout) =>
      <>(anomaly))
Inv18 == \* R73 (not an exact match, since TLA+ does not have next)
  []((retract_gears_electro_valve /\ ~(gears_retracted) /\ timeout) =>
      <>(anomaly))
Inv19 == \* R74 (not an exact match, since TLA+ does not have next)
  []((extend_gears_electro_valve /\ ~(gears_extended) /\ timeout) =>
      <>(anomaly))

=============================================================================
\* Modification History
\* Last modified Thu Nov 18 17:49:23 EST 2021 by bandali
\* Created Thu Nov 11 12:31:13 EST 2021 by bandali

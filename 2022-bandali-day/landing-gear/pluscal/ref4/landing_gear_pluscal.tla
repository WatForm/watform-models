------------------------ MODULE landing_gear_pluscal ------------------------
(* The Landing Gear case study - PlusCal model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Landing Gear PlusCal model.

The Landing Gear PlusCal model is free software: you can redistribute
it and/or modify it under the terms of the GNU General Public License
as published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Landing Gear PlusCal model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Landing Gear PlusCal model.  If not, see
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

The Landing Gear PlusCal model is an adaptation of the AsmetaL one
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

LandingSet == {"FRONT", "LEFT", "RIGHT"}
HandleStatus == {"UP", "DOWN"}
DoorStatus == {"CLOSED", "OPENING", "OPEN", "CLOSING"}
GearStatus == {"RETRACTED", "EXTENDING", "EXTENDED", "RETRACTING"}
CylinderStatus == {"CYLINDER_RETRACTED", "CYLINDER_EXTENDING",
                   "CYLINDER_EXTENDED", "CYLINDER_RETRACTING"}

(* --algorithm ehealth_pluscal
variables handle \in HandleStatus, \* monitored
          doors = "CLOSED",
          gears = "EXTENDED",
          general_electro_valve = FALSE,
          open_doors_electro_valve = FALSE,
          close_doors_electro_valve = FALSE,
          retract_gears_electro_valve = FALSE,
          extend_gears_electro_valve = FALSE,
          \* === sensors ===
          \* f_gears_extended is true if the corresponding gear is
          \* locked in the extended position and false in other
          \* cases
          f_gears_extended \in [LandingSet -> BOOLEAN], \* monitored
          \* f_gears_retracted is true if the corresponding gear is
          \* locked in the retracted position and false in other
          \* cases
          f_gears_retracted \in [LandingSet -> BOOLEAN], \* monitored
          \* f_doors_closed is true if and only if the corresponding
          \* door is locked closed
          f_doors_closed \in [LandingSet -> BOOLEAN], \* monitored
          \* f_doors_open is true if and only if the corresponding
          \* door is locked open
          f_doors_open \in [LandingSet -> BOOLEAN], \* monitored

          timeout \in BOOLEAN, \* monitored
          anomaly = FALSE;

define
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


\* Invariants

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

Inv1 ==
  (gears = "EXTENDING" \/ gears = "RETRACTING") => doors = "OPEN"
Inv2 ==
  doors = "CLOSED" => (gears = "EXTENDED" \/ gears = "RETRACTED")


\* Temporal Properties

Inv3 == \* R11_bis
  []([](handle = "DOWN") =>
       <>(gears = "EXTENDED" /\ doors = "CLOSED"))
Inv4 == \* R12_bis
  []([](handle = "UP") =>
       <>(gears = "RETRACTED" /\ doors = "CLOSED"))
Inv5 == \* R21 (not an exact match, since TLA+ does not have next)
  []([](handle = "DOWN") => <>(gears # "RETRACTING"))
Inv6 == \* R22 (not an exact match, since TLA+ does not have next)
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
end define

macro close_door()
begin
  doors :=
    CASE doors = "OPEN" -> "CLOSING"
      [] doors = "CLOSING" -> IF doors_closed THEN "CLOSED" ELSE doors
      [] doors = "OPENING" -> "CLOSING"
      [] doors = "CLOSED" -> "CLOSED"; \* missing in ASM model
  general_electro_valve :=
    CASE doors = "OPEN" -> general_electro_valve
      [] doors = "CLOSING" -> IF doors_closed THEN FALSE ELSE general_electro_valve
      [] doors = "OPENING" -> general_electro_valve
      [] doors = "CLOSED" -> general_electro_valve;
  close_doors_electro_valve :=
    CASE doors = "OPEN" -> TRUE
      [] doors = "CLOSING" -> IF doors_closed THEN FALSE ELSE close_doors_electro_valve
      [] doors = "OPENING" -> TRUE
      [] doors = "CLOSED" -> close_doors_electro_valve;
  open_doors_electro_valve :=
    CASE doors = "OPEN" -> open_doors_electro_valve
      [] doors = "CLOSING" -> open_doors_electro_valve
      [] doors = "OPENING" -> FALSE
      [] doors = "CLOSED" -> open_doors_electro_valve;
end macro

fair+ process retraction_sequence = "retraction_sequence"
begin
  retraction_sequence:
    if gears # "RETRACTED" then
      if doors = "OPEN" then
        gears :=
          CASE gears = "EXTENDED" -> "RETRACTING"
            [] gears = "RETRACTING" -> IF gears_retracted THEN "RETRACTED" ELSE gears
            [] gears = "EXTENDING" -> "RETRACTING"
            [] gears = "RETRACTED" -> "RETRACTED"; \* missing in ASM model
        retract_gears_electro_valve :=
          CASE gears = "EXTENDED" -> TRUE
            [] gears = "RETRACTING" -> IF gears_retracted THEN FALSE ELSE retract_gears_electro_valve
            [] gears = "EXTENDING" -> TRUE
            [] gears = "RETRACTED" -> retract_gears_electro_valve; \* missing in ASM model
        extend_gears_electro_valve :=
          CASE gears = "EXTENDED" -> extend_gears_electro_valve
            [] gears = "RETRACTING" -> extend_gears_electro_valve
            [] gears = "EXTENDING" -> FALSE
            [] gears = "RETRACTED" -> extend_gears_electro_valve; \* missing in ASM model
      else
        doors :=
          CASE doors = "CLOSED" -> "OPENING"
            [] doors = "CLOSING" -> "OPENING"
            [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors;
        general_electro_valve :=
          CASE doors = "CLOSED" -> TRUE
            [] doors = "CLOSING" -> general_electro_valve
            [] doors = "OPENING" -> general_electro_valve
            [] doors = "OPEN" -> general_electro_valve; \* missing in ASM model
        close_doors_electro_valve :=
          CASE doors = "CLOSED" -> close_doors_electro_valve
            [] doors = "CLOSING" -> FALSE
            [] doors = "OPENING" -> close_doors_electro_valve
            [] doors = "OPEN" -> close_doors_electro_valve; \* missing in ASM model
        open_doors_electro_valve :=
          CASE doors = "CLOSED" -> TRUE
            [] doors = "CLOSING" -> TRUE
            [] doors = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
            [] doors = "OPEN" -> open_doors_electro_valve; \* missing in ASM model
      end if
    else
      close_door()
    end if;
    goto retraction_sequence
end process

fair+ process outgoing_sequence = "outgoing_sequence"
begin
  outgoing_sequence:
    if gears # "EXTENDED" then
      if doors = "OPEN" then
        gears :=
          CASE gears = "RETRACTED" -> "EXTENDING"
            [] gears = "EXTENDING" -> IF gears_extended THEN "EXTENDED" ELSE gears
            [] gears = "RETRACTING" -> "EXTENDING"
            [] gears = "EXTENDED" -> gears; \* missing in ASM model
        extend_gears_electro_valve :=
          CASE gears = "RETRACTED" -> TRUE
            [] gears = "EXTENDING" -> IF gears_extended THEN FALSE ELSE extend_gears_electro_valve
            [] gears = "RETRACTING" -> TRUE
            [] gears = "EXTENDED" -> extend_gears_electro_valve; \* missing in ASM model
        retract_gears_electro_valve :=
          CASE gears = "RETRACTED" -> retract_gears_electro_valve
            [] gears = "EXTENDING" -> retract_gears_electro_valve
            [] gears = "RETRACTING" -> FALSE
            [] gears = "EXTENDED" -> retract_gears_electro_valve; \* missing in ASM model
      else
        doors :=
          CASE doors = "CLOSED" -> "OPENING"
            [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors
            [] doors = "CLOSING" -> "OPENING"; \* missing in ASM model
        general_electro_valve :=
          CASE doors = "CLOSED" -> TRUE
            [] doors = "OPENING" -> general_electro_valve
            [] doors = "CLOSING" -> general_electro_valve \* missing in ASM model
            [] doors = "OPEN" -> general_electro_valve; \* missing in ASM model
        open_doors_electro_valve :=
          CASE doors = "CLOSED" -> TRUE
            [] doors = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
            [] doors = "CLOSING" -> open_doors_electro_valve \* missing in ASM model
            [] doors = "OPEN" -> open_doors_electro_valve; \* missing in ASM model
      end if
    else
      close_door()
    end if;
    goto outgoing_sequence
end process

fair+ process health_monitoring = "health_monitoring"
begin
  health_monitoring:
    if (\/ open_doors_electro_valve /\ a_door_closed /\ timeout
        \/ open_doors_electro_valve /\ ~(doors_open) /\ timeout
        \/ close_doors_electro_valve /\ a_door_open /\ timeout
        \/ close_doors_electro_valve /\ ~(doors_closed) /\ timeout
        \/ retract_gears_electro_valve /\ a_gear_extended /\ timeout
        \/ retract_gears_electro_valve /\ ~(gears_retracted) /\ timeout
        \/ extend_gears_electro_valve /\ a_gear_retracted /\ timeout
        \/ extend_gears_electro_valve /\ ~(gears_extended) /\ timeout) then
      anomaly := TRUE
    end if;
    goto health_monitoring
end process

fair process toggle_handle = "toggle_handle"
begin
  toggle_handle:
    if handle = "UP" then
      handle := "DOWN"
    else
      handle := "UP"
    end if;
    goto toggle_handle
end process

fair process toggle_gears_extended = "toggle_gears_extended"
variable s \in LandingSet
begin
  toggle_gears_extended:
    if f_gears_extended[s] = FALSE then
      f_gears_extended[s] := TRUE
    else
      f_gears_extended[s] := FALSE
    end if;
    goto toggle_gears_extended
end process

fair process toggle_gears_retracted = "toggle_gears_retracted"
variable s \in LandingSet
begin
  toggle_gears_retracted:
    if f_gears_retracted[s] = FALSE then
      f_gears_retracted[s] := TRUE
    else
      f_gears_retracted[s] := FALSE
    end if;
    goto toggle_gears_retracted
end process

fair process toggle_doors_closed = "toggle_doors_closed"
variable s \in LandingSet
begin
  toggle_doors_closed:
    if f_doors_closed[s] = FALSE then
      f_doors_closed[s] := TRUE
    else
      f_doors_closed[s] := FALSE
    end if;
    goto toggle_doors_closed
end process

fair process toggle_doors_open = "toggle_doors_open"
variable s \in LandingSet
begin
  toggle_doors_open:
    if f_doors_open[s] = FALSE then
      f_doors_open[s] := TRUE
    else
      f_doors_open[s] := FALSE
    end if;
    goto toggle_doors_open
end process

fair process toggle_timeout = "toggle_timeout"
begin
  toggle_timeout:
    if timeout = FALSE then
      timeout := TRUE
    else
      timeout := FALSE
    end if;
    goto toggle_timeout
end process

end algorithm; *)

\* BEGIN TRANSLATION
\* Label retraction_sequence of process retraction_sequence at line 204 col 5 changed to retraction_sequence_
\* Label outgoing_sequence of process outgoing_sequence at line 251 col 5 changed to outgoing_sequence_
\* Label health_monitoring of process health_monitoring at line 293 col 5 changed to health_monitoring_
\* Label toggle_handle of process toggle_handle at line 309 col 5 changed to toggle_handle_
\* Label toggle_gears_extended of process toggle_gears_extended at line 321 col 5 changed to toggle_gears_extended_
\* Label toggle_gears_retracted of process toggle_gears_retracted at line 333 col 5 changed to toggle_gears_retracted_
\* Label toggle_doors_closed of process toggle_doors_closed at line 345 col 5 changed to toggle_doors_closed_
\* Label toggle_doors_open of process toggle_doors_open at line 357 col 5 changed to toggle_doors_open_
\* Label toggle_timeout of process toggle_timeout at line 368 col 5 changed to toggle_timeout_
\* Process variable s of process toggle_gears_extended at line 318 col 10 changed to s_
\* Process variable s of process toggle_gears_retracted at line 330 col 10 changed to s_t
\* Process variable s of process toggle_doors_closed at line 342 col 10 changed to s_to
VARIABLES handle, doors, gears, general_electro_valve, 
          open_doors_electro_valve, close_doors_electro_valve, 
          retract_gears_electro_valve, extend_gears_electro_valve, 
          f_gears_extended, f_gears_retracted, f_doors_closed, f_doors_open, 
          timeout, anomaly, pc

(* define statement *)
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

Inv1 ==
  (gears = "EXTENDING" \/ gears = "RETRACTING") => doors = "OPEN"
Inv2 ==
  doors = "CLOSED" => (gears = "EXTENDED" \/ gears = "RETRACTED")




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

Inv7 ==
  []((extend_gears_electro_valve \/ retract_gears_electro_valve) =>
      doors = "OPEN")
Inv8 ==
  []((open_doors_electro_valve \/ close_doors_electro_valve) =>
      (gears = "RETRACTED" \/ gears = "EXTENDED"))
Inv9 ==
  [](~(open_doors_electro_valve /\ close_doors_electro_valve))
Inv10 ==
  [](~(extend_gears_electro_valve /\ retract_gears_electro_valve))
Inv11 ==
  []((\/ open_doors_electro_valve
      \/ close_doors_electro_valve
      \/ extend_gears_electro_valve
      \/ retract_gears_electro_valve) => general_electro_valve)

Inv12 ==
  []((open_doors_electro_valve /\ a_door_closed /\ timeout) =>
      <>(anomaly))
Inv13 ==
  []((close_doors_electro_valve /\ a_door_open /\ timeout) =>
      <>(anomaly))
Inv14 ==
  []((retract_gears_electro_valve /\ a_gear_extended /\ timeout) =>
      <>(anomaly))
Inv15 ==
  []((extend_gears_electro_valve /\ a_gear_retracted /\ timeout) =>
      <>(anomaly))

Inv16 ==
  []((open_doors_electro_valve /\ ~(doors_open) /\ timeout) =>
      <>(anomaly))
Inv17 ==
  []((close_doors_electro_valve /\ ~(doors_closed) /\ timeout) =>
      <>(anomaly))
Inv18 ==
  []((retract_gears_electro_valve /\ ~(gears_retracted) /\ timeout) =>
      <>(anomaly))
Inv19 ==
  []((extend_gears_electro_valve /\ ~(gears_extended) /\ timeout) =>
      <>(anomaly))

VARIABLES s_, s_t, s_to, s

vars == << handle, doors, gears, general_electro_valve, 
           open_doors_electro_valve, close_doors_electro_valve, 
           retract_gears_electro_valve, extend_gears_electro_valve, 
           f_gears_extended, f_gears_retracted, f_doors_closed, f_doors_open, 
           timeout, anomaly, pc, s_, s_t, s_to, s >>

ProcSet == {"retraction_sequence"} \cup {"outgoing_sequence"} \cup {"health_monitoring"} \cup {"toggle_handle"} \cup {"toggle_gears_extended"} \cup {"toggle_gears_retracted"} \cup {"toggle_doors_closed"} \cup {"toggle_doors_open"} \cup {"toggle_timeout"}

Init == (* Global variables *)
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
        (* Process toggle_gears_extended *)
        /\ s_ \in LandingSet
        (* Process toggle_gears_retracted *)
        /\ s_t \in LandingSet
        (* Process toggle_doors_closed *)
        /\ s_to \in LandingSet
        (* Process toggle_doors_open *)
        /\ s \in LandingSet
        /\ pc = [self \in ProcSet |-> CASE self = "retraction_sequence" -> "retraction_sequence_"
                                        [] self = "outgoing_sequence" -> "outgoing_sequence_"
                                        [] self = "health_monitoring" -> "health_monitoring_"
                                        [] self = "toggle_handle" -> "toggle_handle_"
                                        [] self = "toggle_gears_extended" -> "toggle_gears_extended_"
                                        [] self = "toggle_gears_retracted" -> "toggle_gears_retracted_"
                                        [] self = "toggle_doors_closed" -> "toggle_doors_closed_"
                                        [] self = "toggle_doors_open" -> "toggle_doors_open_"
                                        [] self = "toggle_timeout" -> "toggle_timeout_"]

retraction_sequence_ == /\ pc["retraction_sequence"] = "retraction_sequence_"
                        /\ IF gears # "RETRACTED"
                              THEN /\ IF doors = "OPEN"
                                         THEN /\ gears' = (CASE gears = "EXTENDED" -> "RETRACTING"
                                                             [] gears = "RETRACTING" -> IF gears_retracted THEN "RETRACTED" ELSE gears
                                                             [] gears = "EXTENDING" -> "RETRACTING"
                                                             [] gears = "RETRACTED" -> "RETRACTED")
                                              /\ retract_gears_electro_valve' = (CASE gears' = "EXTENDED" -> TRUE
                                                                                   [] gears' = "RETRACTING" -> IF gears_retracted THEN FALSE ELSE retract_gears_electro_valve
                                                                                   [] gears' = "EXTENDING" -> TRUE
                                                                                   [] gears' = "RETRACTED" -> retract_gears_electro_valve)
                                              /\ extend_gears_electro_valve' = (CASE gears' = "EXTENDED" -> extend_gears_electro_valve
                                                                                  [] gears' = "RETRACTING" -> extend_gears_electro_valve
                                                                                  [] gears' = "EXTENDING" -> FALSE
                                                                                  [] gears' = "RETRACTED" -> extend_gears_electro_valve)
                                              /\ UNCHANGED << doors, 
                                                              general_electro_valve, 
                                                              open_doors_electro_valve, 
                                                              close_doors_electro_valve >>
                                         ELSE /\ doors' = (CASE doors = "CLOSED" -> "OPENING"
                                                             [] doors = "CLOSING" -> "OPENING"
                                                             [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors)
                                              /\ general_electro_valve' = (CASE doors' = "CLOSED" -> TRUE
                                                                             [] doors' = "CLOSING" -> general_electro_valve
                                                                             [] doors' = "OPENING" -> general_electro_valve
                                                                             [] doors' = "OPEN" -> general_electro_valve)
                                              /\ close_doors_electro_valve' = (CASE doors' = "CLOSED" -> close_doors_electro_valve
                                                                                 [] doors' = "CLOSING" -> FALSE
                                                                                 [] doors' = "OPENING" -> close_doors_electro_valve
                                                                                 [] doors' = "OPEN" -> close_doors_electro_valve)
                                              /\ open_doors_electro_valve' = (CASE doors' = "CLOSED" -> TRUE
                                                                                [] doors' = "CLOSING" -> TRUE
                                                                                [] doors' = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
                                                                                [] doors' = "OPEN" -> open_doors_electro_valve)
                                              /\ UNCHANGED << gears, 
                                                              retract_gears_electro_valve, 
                                                              extend_gears_electro_valve >>
                              ELSE /\ doors' = (CASE doors = "OPEN" -> "CLOSING"
                                                  [] doors = "CLOSING" -> IF doors_closed THEN "CLOSED" ELSE doors
                                                  [] doors = "OPENING" -> "CLOSING"
                                                  [] doors = "CLOSED" -> "CLOSED")
                                   /\ general_electro_valve' = (CASE doors' = "OPEN" -> general_electro_valve
                                                                  [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE general_electro_valve
                                                                  [] doors' = "OPENING" -> general_electro_valve
                                                                  [] doors' = "CLOSED" -> general_electro_valve)
                                   /\ close_doors_electro_valve' = (CASE doors' = "OPEN" -> TRUE
                                                                      [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE close_doors_electro_valve
                                                                      [] doors' = "OPENING" -> TRUE
                                                                      [] doors' = "CLOSED" -> close_doors_electro_valve)
                                   /\ open_doors_electro_valve' = (CASE doors' = "OPEN" -> open_doors_electro_valve
                                                                     [] doors' = "CLOSING" -> open_doors_electro_valve
                                                                     [] doors' = "OPENING" -> FALSE
                                                                     [] doors' = "CLOSED" -> open_doors_electro_valve)
                                   /\ UNCHANGED << gears, 
                                                   retract_gears_electro_valve, 
                                                   extend_gears_electro_valve >>
                        /\ pc' = [pc EXCEPT !["retraction_sequence"] = "retraction_sequence_"]
                        /\ UNCHANGED << handle, f_gears_extended, 
                                        f_gears_retracted, f_doors_closed, 
                                        f_doors_open, timeout, anomaly, s_, 
                                        s_t, s_to, s >>

retraction_sequence == retraction_sequence_

outgoing_sequence_ == /\ pc["outgoing_sequence"] = "outgoing_sequence_"
                      /\ IF gears # "EXTENDED"
                            THEN /\ IF doors = "OPEN"
                                       THEN /\ gears' = (CASE gears = "RETRACTED" -> "EXTENDING"
                                                           [] gears = "EXTENDING" -> IF gears_extended THEN "EXTENDED" ELSE gears
                                                           [] gears = "RETRACTING" -> "EXTENDING"
                                                           [] gears = "EXTENDED" -> gears)
                                            /\ extend_gears_electro_valve' = (CASE gears' = "RETRACTED" -> TRUE
                                                                                [] gears' = "EXTENDING" -> IF gears_extended THEN FALSE ELSE extend_gears_electro_valve
                                                                                [] gears' = "RETRACTING" -> TRUE
                                                                                [] gears' = "EXTENDED" -> extend_gears_electro_valve)
                                            /\ retract_gears_electro_valve' = (CASE gears' = "RETRACTED" -> retract_gears_electro_valve
                                                                                 [] gears' = "EXTENDING" -> retract_gears_electro_valve
                                                                                 [] gears' = "RETRACTING" -> FALSE
                                                                                 [] gears' = "EXTENDED" -> retract_gears_electro_valve)
                                            /\ UNCHANGED << doors, 
                                                            general_electro_valve, 
                                                            open_doors_electro_valve >>
                                       ELSE /\ doors' = (CASE doors = "CLOSED" -> "OPENING"
                                                           [] doors = "OPENING" -> IF doors_open THEN "OPEN" ELSE doors
                                                           [] doors = "CLOSING" -> "OPENING")
                                            /\ general_electro_valve' = (CASE doors' = "CLOSED" -> TRUE
                                                                           [] doors' = "OPENING" -> general_electro_valve
                                                                           [] doors' = "CLOSING" -> general_electro_valve
                                                                           [] doors' = "OPEN" -> general_electro_valve)
                                            /\ open_doors_electro_valve' = (CASE doors' = "CLOSED" -> TRUE
                                                                              [] doors' = "OPENING" -> IF doors_open THEN FALSE ELSE open_doors_electro_valve
                                                                              [] doors' = "CLOSING" -> open_doors_electro_valve
                                                                              [] doors' = "OPEN" -> open_doors_electro_valve)
                                            /\ UNCHANGED << gears, 
                                                            retract_gears_electro_valve, 
                                                            extend_gears_electro_valve >>
                                 /\ UNCHANGED close_doors_electro_valve
                            ELSE /\ doors' = (CASE doors = "OPEN" -> "CLOSING"
                                                [] doors = "CLOSING" -> IF doors_closed THEN "CLOSED" ELSE doors
                                                [] doors = "OPENING" -> "CLOSING"
                                                [] doors = "CLOSED" -> "CLOSED")
                                 /\ general_electro_valve' = (CASE doors' = "OPEN" -> general_electro_valve
                                                                [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE general_electro_valve
                                                                [] doors' = "OPENING" -> general_electro_valve
                                                                [] doors' = "CLOSED" -> general_electro_valve)
                                 /\ close_doors_electro_valve' = (CASE doors' = "OPEN" -> TRUE
                                                                    [] doors' = "CLOSING" -> IF doors_closed THEN FALSE ELSE close_doors_electro_valve
                                                                    [] doors' = "OPENING" -> TRUE
                                                                    [] doors' = "CLOSED" -> close_doors_electro_valve)
                                 /\ open_doors_electro_valve' = (CASE doors' = "OPEN" -> open_doors_electro_valve
                                                                   [] doors' = "CLOSING" -> open_doors_electro_valve
                                                                   [] doors' = "OPENING" -> FALSE
                                                                   [] doors' = "CLOSED" -> open_doors_electro_valve)
                                 /\ UNCHANGED << gears, 
                                                 retract_gears_electro_valve, 
                                                 extend_gears_electro_valve >>
                      /\ pc' = [pc EXCEPT !["outgoing_sequence"] = "outgoing_sequence_"]
                      /\ UNCHANGED << handle, f_gears_extended, 
                                      f_gears_retracted, f_doors_closed, 
                                      f_doors_open, timeout, anomaly, s_, s_t, 
                                      s_to, s >>

outgoing_sequence == outgoing_sequence_

health_monitoring_ == /\ pc["health_monitoring"] = "health_monitoring_"
                      /\ IF (\/ open_doors_electro_valve /\ a_door_closed /\ timeout
                             \/ open_doors_electro_valve /\ ~(doors_open) /\ timeout
                             \/ close_doors_electro_valve /\ a_door_open /\ timeout
                             \/ close_doors_electro_valve /\ ~(doors_closed) /\ timeout
                             \/ retract_gears_electro_valve /\ a_gear_extended /\ timeout
                             \/ retract_gears_electro_valve /\ ~(gears_retracted) /\ timeout
                             \/ extend_gears_electro_valve /\ a_gear_retracted /\ timeout
                             \/ extend_gears_electro_valve /\ ~(gears_extended) /\ timeout)
                            THEN /\ anomaly' = TRUE
                            ELSE /\ TRUE
                                 /\ UNCHANGED anomaly
                      /\ pc' = [pc EXCEPT !["health_monitoring"] = "health_monitoring_"]
                      /\ UNCHANGED << handle, doors, gears, 
                                      general_electro_valve, 
                                      open_doors_electro_valve, 
                                      close_doors_electro_valve, 
                                      retract_gears_electro_valve, 
                                      extend_gears_electro_valve, 
                                      f_gears_extended, f_gears_retracted, 
                                      f_doors_closed, f_doors_open, timeout, 
                                      s_, s_t, s_to, s >>

health_monitoring == health_monitoring_

toggle_handle_ == /\ pc["toggle_handle"] = "toggle_handle_"
                  /\ IF handle = "UP"
                        THEN /\ handle' = "DOWN"
                        ELSE /\ handle' = "UP"
                  /\ pc' = [pc EXCEPT !["toggle_handle"] = "toggle_handle_"]
                  /\ UNCHANGED << doors, gears, general_electro_valve, 
                                  open_doors_electro_valve, 
                                  close_doors_electro_valve, 
                                  retract_gears_electro_valve, 
                                  extend_gears_electro_valve, f_gears_extended, 
                                  f_gears_retracted, f_doors_closed, 
                                  f_doors_open, timeout, anomaly, s_, s_t, 
                                  s_to, s >>

toggle_handle == toggle_handle_

toggle_gears_extended_ == /\ pc["toggle_gears_extended"] = "toggle_gears_extended_"
                          /\ IF f_gears_extended[s_] = FALSE
                                THEN /\ f_gears_extended' = [f_gears_extended EXCEPT ![s_] = TRUE]
                                ELSE /\ f_gears_extended' = [f_gears_extended EXCEPT ![s_] = FALSE]
                          /\ pc' = [pc EXCEPT !["toggle_gears_extended"] = "toggle_gears_extended_"]
                          /\ UNCHANGED << handle, doors, gears, 
                                          general_electro_valve, 
                                          open_doors_electro_valve, 
                                          close_doors_electro_valve, 
                                          retract_gears_electro_valve, 
                                          extend_gears_electro_valve, 
                                          f_gears_retracted, f_doors_closed, 
                                          f_doors_open, timeout, anomaly, s_, 
                                          s_t, s_to, s >>

toggle_gears_extended == toggle_gears_extended_

toggle_gears_retracted_ == /\ pc["toggle_gears_retracted"] = "toggle_gears_retracted_"
                           /\ IF f_gears_retracted[s_t] = FALSE
                                 THEN /\ f_gears_retracted' = [f_gears_retracted EXCEPT ![s_t] = TRUE]
                                 ELSE /\ f_gears_retracted' = [f_gears_retracted EXCEPT ![s_t] = FALSE]
                           /\ pc' = [pc EXCEPT !["toggle_gears_retracted"] = "toggle_gears_retracted_"]
                           /\ UNCHANGED << handle, doors, gears, 
                                           general_electro_valve, 
                                           open_doors_electro_valve, 
                                           close_doors_electro_valve, 
                                           retract_gears_electro_valve, 
                                           extend_gears_electro_valve, 
                                           f_gears_extended, f_doors_closed, 
                                           f_doors_open, timeout, anomaly, s_, 
                                           s_t, s_to, s >>

toggle_gears_retracted == toggle_gears_retracted_

toggle_doors_closed_ == /\ pc["toggle_doors_closed"] = "toggle_doors_closed_"
                        /\ IF f_doors_closed[s_to] = FALSE
                              THEN /\ f_doors_closed' = [f_doors_closed EXCEPT ![s_to] = TRUE]
                              ELSE /\ f_doors_closed' = [f_doors_closed EXCEPT ![s_to] = FALSE]
                        /\ pc' = [pc EXCEPT !["toggle_doors_closed"] = "toggle_doors_closed_"]
                        /\ UNCHANGED << handle, doors, gears, 
                                        general_electro_valve, 
                                        open_doors_electro_valve, 
                                        close_doors_electro_valve, 
                                        retract_gears_electro_valve, 
                                        extend_gears_electro_valve, 
                                        f_gears_extended, f_gears_retracted, 
                                        f_doors_open, timeout, anomaly, s_, 
                                        s_t, s_to, s >>

toggle_doors_closed == toggle_doors_closed_

toggle_doors_open_ == /\ pc["toggle_doors_open"] = "toggle_doors_open_"
                      /\ IF f_doors_open[s] = FALSE
                            THEN /\ f_doors_open' = [f_doors_open EXCEPT ![s] = TRUE]
                            ELSE /\ f_doors_open' = [f_doors_open EXCEPT ![s] = FALSE]
                      /\ pc' = [pc EXCEPT !["toggle_doors_open"] = "toggle_doors_open_"]
                      /\ UNCHANGED << handle, doors, gears, 
                                      general_electro_valve, 
                                      open_doors_electro_valve, 
                                      close_doors_electro_valve, 
                                      retract_gears_electro_valve, 
                                      extend_gears_electro_valve, 
                                      f_gears_extended, f_gears_retracted, 
                                      f_doors_closed, timeout, anomaly, s_, 
                                      s_t, s_to, s >>

toggle_doors_open == toggle_doors_open_

toggle_timeout_ == /\ pc["toggle_timeout"] = "toggle_timeout_"
                   /\ IF timeout = FALSE
                         THEN /\ timeout' = TRUE
                         ELSE /\ timeout' = FALSE
                   /\ pc' = [pc EXCEPT !["toggle_timeout"] = "toggle_timeout_"]
                   /\ UNCHANGED << handle, doors, gears, general_electro_valve, 
                                   open_doors_electro_valve, 
                                   close_doors_electro_valve, 
                                   retract_gears_electro_valve, 
                                   extend_gears_electro_valve, 
                                   f_gears_extended, f_gears_retracted, 
                                   f_doors_closed, f_doors_open, anomaly, s_, 
                                   s_t, s_to, s >>

toggle_timeout == toggle_timeout_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == retraction_sequence \/ outgoing_sequence \/ health_monitoring
           \/ toggle_handle \/ toggle_gears_extended \/ toggle_gears_retracted
           \/ toggle_doors_closed \/ toggle_doors_open \/ toggle_timeout
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(retraction_sequence)
        /\ SF_vars(outgoing_sequence)
        /\ SF_vars(health_monitoring)
        /\ WF_vars(toggle_handle)
        /\ WF_vars(toggle_gears_extended)
        /\ WF_vars(toggle_gears_retracted)
        /\ WF_vars(toggle_doors_closed)
        /\ WF_vars(toggle_doors_open)
        /\ WF_vars(toggle_timeout)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MyNext ==
  \/ IF ~(anomaly) THEN
       /\ IF handle = "UP" THEN retraction_sequence
                           ELSE outgoing_sequence
       /\ health_monitoring
     ELSE TRUE
  \/ toggle_handle
  \/ toggle_gears_extended
  \/ toggle_gears_retracted
  \/ toggle_doors_closed
  \/ toggle_doors_open
  \/ toggle_timeout
  \/ Terminating

MySpec ==
  /\ Init /\ [][MyNext]_vars
  /\ SF_vars(retraction_sequence)
  /\ SF_vars(outgoing_sequence)
  /\ SF_vars(health_monitoring)
  /\ WF_vars(toggle_handle)
  /\ WF_vars(toggle_gears_extended)
  /\ WF_vars(toggle_gears_retracted)
  /\ WF_vars(toggle_doors_closed)
  /\ WF_vars(toggle_doors_open)
  /\ WF_vars(toggle_timeout)

=============================================================================
\* Modification History
\* Last modified Thu Sep 03 14:13:00 EDT 2020 by bandali
\* Created Wed Aug 19 21:45:19 EDT 2020 by bandali

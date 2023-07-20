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
          \* gears_extended is true if the corresponding gear is
          \* locked in the extended position and false in other
          \* cases
          gears_extended \in BOOLEAN, \* monitored
          \* gears_retracted is true if the corresponding gear is
          \* locked in the retracted position and false in other
          \* cases
          gears_retracted \in BOOLEAN, \* monitored
          \* doors_closed is true if and only if the corresponding
          \* door is locked closed
          doors_closed \in BOOLEAN, \* monitored
          \* doors_open is true if and only if the corresponding
          \* door is locked open
          doors_open \in BOOLEAN; \* monitored

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
    /\ gears_extended \in BOOLEAN
    /\ gears_retracted \in BOOLEAN
    /\ doors_closed \in BOOLEAN
    /\ doors_open \in BOOLEAN
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
begin
  toggle_gears_extended:
    if gears_extended = FALSE then
      gears_extended := TRUE
    else
      gears_extended := FALSE
    end if;
    goto toggle_gears_extended
end process

fair process toggle_gears_retracted = "toggle_gears_retracted"
begin
  toggle_gears_retracted:
    if gears_retracted = FALSE then
      gears_retracted := TRUE
    else
      gears_retracted := FALSE
    end if;
    goto toggle_gears_retracted
end process

fair process toggle_doors_closed = "toggle_doors_closed"
begin
  toggle_doors_closed:
    if doors_closed = FALSE then
      doors_closed := TRUE
    else
      doors_closed := FALSE
    end if;
    goto toggle_doors_closed
end process

fair process toggle_doors_open = "toggle_doors_open"
begin
  toggle_doors_open:
    if doors_open = FALSE then
      doors_open := TRUE
    else
      doors_open := FALSE
    end if;
    goto toggle_doors_open
end process

end algorithm; *)

\* BEGIN TRANSLATION
\* Label retraction_sequence of process retraction_sequence at line 131 col 5 changed to retraction_sequence_
\* Label outgoing_sequence of process outgoing_sequence at line 178 col 5 changed to outgoing_sequence_
\* Label toggle_handle of process toggle_handle at line 220 col 5 changed to toggle_handle_
\* Label toggle_gears_extended of process toggle_gears_extended at line 231 col 5 changed to toggle_gears_extended_
\* Label toggle_gears_retracted of process toggle_gears_retracted at line 242 col 5 changed to toggle_gears_retracted_
\* Label toggle_doors_closed of process toggle_doors_closed at line 253 col 5 changed to toggle_doors_closed_
\* Label toggle_doors_open of process toggle_doors_open at line 264 col 5 changed to toggle_doors_open_
VARIABLES handle, doors, gears, general_electro_valve, 
          open_doors_electro_valve, close_doors_electro_valve, 
          retract_gears_electro_valve, extend_gears_electro_valve, 
          gears_extended, gears_retracted, doors_closed, doors_open, pc

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


vars == << handle, doors, gears, general_electro_valve, 
           open_doors_electro_valve, close_doors_electro_valve, 
           retract_gears_electro_valve, extend_gears_electro_valve, 
           gears_extended, gears_retracted, doors_closed, doors_open, pc >>

ProcSet == {"retraction_sequence"} \cup {"outgoing_sequence"} \cup {"toggle_handle"} \cup {"toggle_gears_extended"} \cup {"toggle_gears_retracted"} \cup {"toggle_doors_closed"} \cup {"toggle_doors_open"}

Init == (* Global variables *)
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
        /\ pc = [self \in ProcSet |-> CASE self = "retraction_sequence" -> "retraction_sequence_"
                                        [] self = "outgoing_sequence" -> "outgoing_sequence_"
                                        [] self = "toggle_handle" -> "toggle_handle_"
                                        [] self = "toggle_gears_extended" -> "toggle_gears_extended_"
                                        [] self = "toggle_gears_retracted" -> "toggle_gears_retracted_"
                                        [] self = "toggle_doors_closed" -> "toggle_doors_closed_"
                                        [] self = "toggle_doors_open" -> "toggle_doors_open_"]

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
                        /\ UNCHANGED << handle, gears_extended, 
                                        gears_retracted, doors_closed, 
                                        doors_open >>

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
                      /\ UNCHANGED << handle, gears_extended, gears_retracted, 
                                      doors_closed, doors_open >>

outgoing_sequence == outgoing_sequence_

toggle_handle_ == /\ pc["toggle_handle"] = "toggle_handle_"
                  /\ IF handle = "UP"
                        THEN /\ handle' = "DOWN"
                        ELSE /\ handle' = "UP"
                  /\ pc' = [pc EXCEPT !["toggle_handle"] = "toggle_handle_"]
                  /\ UNCHANGED << doors, gears, general_electro_valve, 
                                  open_doors_electro_valve, 
                                  close_doors_electro_valve, 
                                  retract_gears_electro_valve, 
                                  extend_gears_electro_valve, gears_extended, 
                                  gears_retracted, doors_closed, doors_open >>

toggle_handle == toggle_handle_

toggle_gears_extended_ == /\ pc["toggle_gears_extended"] = "toggle_gears_extended_"
                          /\ IF gears_extended = FALSE
                                THEN /\ gears_extended' = TRUE
                                ELSE /\ gears_extended' = FALSE
                          /\ pc' = [pc EXCEPT !["toggle_gears_extended"] = "toggle_gears_extended_"]
                          /\ UNCHANGED << handle, doors, gears, 
                                          general_electro_valve, 
                                          open_doors_electro_valve, 
                                          close_doors_electro_valve, 
                                          retract_gears_electro_valve, 
                                          extend_gears_electro_valve, 
                                          gears_retracted, doors_closed, 
                                          doors_open >>

toggle_gears_extended == toggle_gears_extended_

toggle_gears_retracted_ == /\ pc["toggle_gears_retracted"] = "toggle_gears_retracted_"
                           /\ IF gears_retracted = FALSE
                                 THEN /\ gears_retracted' = TRUE
                                 ELSE /\ gears_retracted' = FALSE
                           /\ pc' = [pc EXCEPT !["toggle_gears_retracted"] = "toggle_gears_retracted_"]
                           /\ UNCHANGED << handle, doors, gears, 
                                           general_electro_valve, 
                                           open_doors_electro_valve, 
                                           close_doors_electro_valve, 
                                           retract_gears_electro_valve, 
                                           extend_gears_electro_valve, 
                                           gears_extended, doors_closed, 
                                           doors_open >>

toggle_gears_retracted == toggle_gears_retracted_

toggle_doors_closed_ == /\ pc["toggle_doors_closed"] = "toggle_doors_closed_"
                        /\ IF doors_closed = FALSE
                              THEN /\ doors_closed' = TRUE
                              ELSE /\ doors_closed' = FALSE
                        /\ pc' = [pc EXCEPT !["toggle_doors_closed"] = "toggle_doors_closed_"]
                        /\ UNCHANGED << handle, doors, gears, 
                                        general_electro_valve, 
                                        open_doors_electro_valve, 
                                        close_doors_electro_valve, 
                                        retract_gears_electro_valve, 
                                        extend_gears_electro_valve, 
                                        gears_extended, gears_retracted, 
                                        doors_open >>

toggle_doors_closed == toggle_doors_closed_

toggle_doors_open_ == /\ pc["toggle_doors_open"] = "toggle_doors_open_"
                      /\ IF doors_open = FALSE
                            THEN /\ doors_open' = TRUE
                            ELSE /\ doors_open' = FALSE
                      /\ pc' = [pc EXCEPT !["toggle_doors_open"] = "toggle_doors_open_"]
                      /\ UNCHANGED << handle, doors, gears, 
                                      general_electro_valve, 
                                      open_doors_electro_valve, 
                                      close_doors_electro_valve, 
                                      retract_gears_electro_valve, 
                                      extend_gears_electro_valve, 
                                      gears_extended, gears_retracted, 
                                      doors_closed >>

toggle_doors_open == toggle_doors_open_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == retraction_sequence \/ outgoing_sequence \/ toggle_handle
           \/ toggle_gears_extended \/ toggle_gears_retracted
           \/ toggle_doors_closed \/ toggle_doors_open
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(retraction_sequence)
        /\ SF_vars(outgoing_sequence)
        /\ WF_vars(toggle_handle)
        /\ WF_vars(toggle_gears_extended)
        /\ WF_vars(toggle_gears_retracted)
        /\ WF_vars(toggle_doors_closed)
        /\ WF_vars(toggle_doors_open)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MyNext ==
  \/ IF handle = "UP" THEN retraction_sequence ELSE outgoing_sequence
  \/ toggle_handle
  \/ toggle_gears_extended
  \/ toggle_gears_retracted
  \/ toggle_doors_closed
  \/ toggle_doors_open
  \/ Terminating

MySpec ==
  /\ Init /\ [][MyNext]_vars
  /\ SF_vars(retraction_sequence)
  /\ SF_vars(outgoing_sequence)
  /\ WF_vars(toggle_handle)
  /\ WF_vars(toggle_gears_extended)
  /\ WF_vars(toggle_gears_retracted)
  /\ WF_vars(toggle_doors_closed)
  /\ WF_vars(toggle_doors_open)

=============================================================================
\* Modification History
\* Last modified Mon Aug 31 12:14:57 EDT 2020 by bandali
\* Created Wed Aug 19 21:45:19 EDT 2020 by bandali

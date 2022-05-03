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

(* --algorithm ehealth_pluscal
variables handle \in HandleStatus, \* monitored
          doors = "CLOSED",
          gears = "EXTENDED";

define
TypeOK ==
    /\ handle \in HandleStatus
    /\ doors \in DoorStatus
    /\ gears \in GearStatus

\* Invariants

Inv1 ==
  (gears = "EXTENDING" \/ gears = "RETRACTING") => doors = "OPEN"
Inv2 ==
  doors = "CLOSED" => (gears = "EXTENDED" \/ gears = "RETRACTED")

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
end define

macro close_door()
begin
  doors :=
    CASE doors = "OPEN" -> "CLOSING"
      [] doors = "CLOSING" -> "CLOSED"
      [] doors = "OPENING" -> "CLOSING"
      [] doors = "CLOSED" -> "CLOSED" \* missing in ASM model
end macro

fair+ process retraction_sequence = "retraction_sequence"
begin
  retraction_sequence:
    if gears # "RETRACTED" then
      if doors = "OPEN" then
        gears :=
          CASE gears = "EXTENDED" -> "RETRACTING"
            [] gears = "RETRACTING" -> "RETRACTED"
            [] gears = "EXTENDING" -> "RETRACTING"
      else
        doors :=
          CASE doors = "CLOSED" -> "OPENING"
            [] doors = "CLOSING" -> "OPENING"
            [] doors = "OPENING" -> "OPEN"
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
            [] gears = "EXTENDING" -> "EXTENDED"
            [] gears = "RETRACTING" -> "EXTENDING"
      else
        doors :=
          CASE doors = "CLOSED" -> "OPENING"
            [] doors = "OPENING" -> "OPEN"
            [] doors = "CLOSING" -> "OPENING" \* missing in ASM model
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

end algorithm; *)

\* BEGIN TRANSLATION
\* Label retraction_sequence of process retraction_sequence at line 49 col 5 changed to retraction_sequence_
\* Label outgoing_sequence of process outgoing_sequence at line 70 col 5 changed to outgoing_sequence_
\* Label toggle_handle of process toggle_handle at line 91 col 5 changed to toggle_handle_
VARIABLES handle, doors, gears, pc

(* define statement *)
TypeOK ==
    /\ handle \in HandleStatus
    /\ doors \in DoorStatus
    /\ gears \in GearStatus



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


vars == << handle, doors, gears, pc >>

ProcSet == {"retraction_sequence"} \cup {"outgoing_sequence"} \cup {"toggle_handle"}

Init == (* Global variables *)
        /\ handle \in HandleStatus
        /\ doors = "CLOSED"
        /\ gears = "EXTENDED"
        /\ pc = [self \in ProcSet |-> CASE self = "retraction_sequence" -> "retraction_sequence_"
                                        [] self = "outgoing_sequence" -> "outgoing_sequence_"
                                        [] self = "toggle_handle" -> "toggle_handle_"]

retraction_sequence_ == /\ pc["retraction_sequence"] = "retraction_sequence_"
                        /\ IF gears # "RETRACTED"
                              THEN /\ IF doors = "OPEN"
                                         THEN /\ gears' = (CASE gears = "EXTENDED" -> "RETRACTING"
                                                             [] gears = "RETRACTING" -> "RETRACTED"
                                                             [] gears = "EXTENDING" -> "RETRACTING")
                                              /\ doors' = doors
                                         ELSE /\ doors' = (CASE doors = "CLOSED" -> "OPENING"
                                                             [] doors = "CLOSING" -> "OPENING"
                                                             [] doors = "OPENING" -> "OPEN")
                                              /\ gears' = gears
                              ELSE /\ doors' = (CASE doors = "OPEN" -> "CLOSING"
                                                  [] doors = "CLOSING" -> "CLOSED"
                                                  [] doors = "OPENING" -> "CLOSING"
                                                  [] doors = "CLOSED" -> "CLOSED")
                                   /\ gears' = gears
                        /\ pc' = [pc EXCEPT !["retraction_sequence"] = "retraction_sequence_"]
                        /\ UNCHANGED handle

retraction_sequence == retraction_sequence_

outgoing_sequence_ == /\ pc["outgoing_sequence"] = "outgoing_sequence_"
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
                            ELSE /\ doors' = (CASE doors = "OPEN" -> "CLOSING"
                                                [] doors = "CLOSING" -> "CLOSED"
                                                [] doors = "OPENING" -> "CLOSING"
                                                [] doors = "CLOSED" -> "CLOSED")
                                 /\ gears' = gears
                      /\ pc' = [pc EXCEPT !["outgoing_sequence"] = "outgoing_sequence_"]
                      /\ UNCHANGED handle

outgoing_sequence == outgoing_sequence_

toggle_handle_ == /\ pc["toggle_handle"] = "toggle_handle_"
                  /\ IF handle = "UP"
                        THEN /\ handle' = "DOWN"
                        ELSE /\ handle' = "UP"
                  /\ pc' = [pc EXCEPT !["toggle_handle"] = "toggle_handle_"]
                  /\ UNCHANGED << doors, gears >>

toggle_handle == toggle_handle_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == retraction_sequence \/ outgoing_sequence \/ toggle_handle
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(retraction_sequence)
        /\ SF_vars(outgoing_sequence)
        /\ WF_vars(toggle_handle)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MyNext ==
  \/ IF handle = "UP" THEN retraction_sequence ELSE outgoing_sequence
  \/ toggle_handle
  \/ Terminating

MySpec ==
  /\ Init /\ [][MyNext]_vars
  /\ SF_vars(retraction_sequence)
  /\ SF_vars(outgoing_sequence)
  /\ WF_vars(toggle_handle)

=============================================================================
\* Modification History
\* Last modified Mon Nov 01 19:52:37 EDT 2021 by bandali
\* Created Wed Aug 19 21:45:19 EDT 2020 by bandali

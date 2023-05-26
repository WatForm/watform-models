/*
   Automatically created via translation of a Dash model to Alloy
   on 2023-05-26 11:09:19
*/

open util/boolean
open util/traces[DshSnapshot] as DshSnapshot

/* The Landing Gear case study - Dash model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Landing Gear Dash model.

The Landing Gear Dash model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Landing Gear Dash model is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Landing Gear Dash model.  If not, see
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

The Landing Gear Dash model is an adaptation of the AsmetaL one
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

*/

// must run with TCMC option turned on for translation to Alloy

enum HandleStatus {UP, DOWN}
enum DoorStatus {CLOSED, OPENING, OPEN, CLOSING}
enum GearStatus {RETRACTED, EXTENDING, EXTENDED, RETRACTING}

pred close_door[d1, d2: DoorStatus] {
    d1 = OPEN implies d2 = CLOSING
    else d1 = CLOSING implies d2 = CLOSED
    else d1 = OPENING implies d2 = CLOSING
}

abstract sig DshStates {}
abstract sig LandingGear extends DshStates {} 

sig DshSnapshot {
  dsh_sc_used0: set DshStates,
  dsh_conf0: set DshStates,
  LandingGear_gears: one GearStatus,
  LandingGear_handle: one HandleStatus,
  LandingGear_doors: one DoorStatus
}

pred dsh_initial [s: one DshSnapshot] {
  (s . dsh_conf0) = LandingGear and
  (s . dsh_stable) = boolean/True and
  (s . LandingGear_doors) = CLOSED and
  (s . LandingGear_gears) = EXTENDED
}

fact inv {  (all s: one
  DshSnapshot | ({ (s . LandingGear_gears) = EXTENDING or
                     (s . LandingGear_gears) = RETRACTING })
                  => ((s . LandingGear_doors) = OPEN) and
                  ((s . LandingGear_doors) = CLOSED) =>
                    ({ (s . LandingGear_gears) = EXTENDED or
                         (s . LandingGear_gears) = RETRACTED }))
}

pred LandingGear_retraction_sequence_pre [s: one DshSnapshot] {
  some (LandingGear & (s . dsh_conf0))
  (s . LandingGear_handle) = UP
  ! (LandingGear in (s . dsh_sc_used0))
}


pred LandingGear_retraction_sequence_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((s . dsh_conf0) - LandingGear) + LandingGear)
  ((s . LandingGear_gears) != RETRACTED)=>
    ((s . LandingGear_doors) = CLOSED)=>
        ((sn . LandingGear_doors) = OPENING)
      else
        (((s . LandingGear_doors) = CLOSING)=>
             ((sn . LandingGear_doors) = OPENING)
           else
             (((s . LandingGear_doors) = OPEN) =>
                ((s . LandingGear_gears) = EXTENDED)=>
                    ((sn . LandingGear_gears) = RETRACTING)
                  else
                    (((s . LandingGear_gears) = RETRACTING)=>
                         ((sn . LandingGear_gears) =
                            RETRACTED)
                       else
                         (((s . LandingGear_gears) =
                             EXTENDING) =>
                            ((sn . LandingGear_gears) =
                               RETRACTING))
                     )
                )
         )
    
  else
    ((sn . LandingGear_doors).((s . LandingGear_doors).close_door))

}

pred LandingGear_retraction_sequence [s: one DshSnapshot, sn: one DshSnapshot] {
  s . LandingGear_retraction_sequence_pre
  sn . (s . LandingGear_retraction_sequence_post)
}

pred LandingGear_outgoing_sequence_pre [s: one DshSnapshot] {
  some (LandingGear & (s . dsh_conf0))
  (s . LandingGear_handle) != UP
  ! (LandingGear in (s . dsh_sc_used0))
}


pred LandingGear_outgoing_sequence_post [s: one DshSnapshot, sn: one DshSnapshot] {
  (sn . dsh_conf0) =
  (((s . dsh_conf0) - LandingGear) + LandingGear)
  ((s . LandingGear_gears) != EXTENDED)=>
    ((s . LandingGear_doors) = CLOSED)=>
        ((sn . LandingGear_doors) = OPENING)
      else
        (((s . LandingGear_doors) = OPENING)=>
             ((sn . LandingGear_doors) = OPEN)
           else
             (((s . LandingGear_doors) = OPEN) =>
                ((s . LandingGear_gears) = RETRACTED)=>
                    ((sn . LandingGear_gears) = EXTENDING)
                  else
                    (((s . LandingGear_gears) = EXTENDING)=>
                         ((sn . LandingGear_gears) =
                            EXTENDED)
                       else
                         (((s . LandingGear_gears) =
                             RETRACTING) =>
                            ((sn . LandingGear_gears) =
                               EXTENDING))
                     )
                )
         )
    
  else
    ((sn . LandingGear_doors).((s . LandingGear_doors).close_door))

}

pred LandingGear_outgoing_sequence [s: one DshSnapshot, sn: one DshSnapshot] {
  s . LandingGear_outgoing_sequence_pre
  sn . (s . LandingGear_outgoing_sequence_post)
}

pred dsh_small_step [s: one DshSnapshot, sn: one DshSnapshot] {
  { sn . (s . LandingGear_retraction_sequence) or
    sn . (s . LandingGear_outgoing_sequence) }
}

fact dsh_traces_fact {  DshSnapshot/first . dsh_initial
  (all s: one
  (DshSnapshot - DshSnapshot/last) | (s . DshSnapshot/next)
                                       .
                                       (s . dsh_small_step))
}

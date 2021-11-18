/* The Landing Gear case study - Alloy model

Copyright (c) 2020 Amin Bandali <bandali@uwaterloo.ca>
Copyright (c) 2020 Nancy Day <nday@uwaterloo.ca>

This file is part of the Landing Gear Alloy model.

The Landing Gear Alloy model is free software: you can redistribute it
and/or modify it under the terms of the GNU General Public License as
published by the Free Software Foundation, either version 3 of the
License, or (at your option) any later version.

The Landing Gear Alloy model is distributed in the hope that it will
be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with the Landing Gear Alloy model.  If not, see
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

The Landing Gear Alloy model is an adaptation of the AsmetaL one
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


open util/ordering [State] as StateOrdering

enum LandingSet {FRONT, LEFT, RIGHT}
enum Bool {False, True}
enum HandleStatus {UP, DOWN}
enum DoorStatus {CLOSED, OPENING, OPEN, CLOSING}
enum GearStatus {RETRACTED, EXTENDING, EXTENDED, RETRACTING}
enum CylinderStatus {CYLINDER_RETRACTED, CYLINDER_EXTENDING,
                     CYLINDER_EXTENDED, CYLINDER_RETRACTING}

one sig Const {
  cylinders_doors: DoorStatus -> CylinderStatus,
  cylinders_gears: GearStatus -> CylinderStatus
} {
  cylinders_doors = {
    OPEN -> CYLINDER_EXTENDED
    + OPENING -> CYLINDER_EXTENDING
    + CLOSING -> CYLINDER_RETRACTING
    + CLOSED -> CYLINDER_RETRACTED
  }
  cylinders_gears = {
    RETRACTED -> CYLINDER_RETRACTED
    + EXTENDING -> CYLINDER_EXTENDING
    + EXTENDED -> CYLINDER_EXTENDED
    + RETRACTING -> CYLINDER_RETRACTING
  }
}

pred close_door[s, s': State] {
    s.doors = OPEN implies {
      s'.doors = CLOSING
      s'.general_electro_valve = s.general_electro_valve
      s'.close_doors_electro_valve = True
      s'.open_doors_electro_valve = s.open_doors_electro_valve
    }
    else s.doors = CLOSING implies {
      doors_closed[s] implies {
        s'.doors = CLOSED
        and s'.general_electro_valve = False
        and s'.close_doors_electro_valve = False
        and s'.open_doors_electro_valve = s.open_doors_electro_valve
      }
    }
    else s.doors = OPENING implies {
      s'.doors = CLOSING
      and s'.general_electro_valve = s.general_electro_valve
      and s'.close_doors_electro_valve = True
      and s'.open_doors_electro_valve = False
    }
    else s.doors = CLOSED implies {
      s'.doors = CLOSED
      and s'.general_electro_valve = s.general_electro_valve
      and s'.close_doors_electro_valve = s.close_doors_electro_valve
      and s'.open_doors_electro_valve = s.open_doors_electro_valve
    }
}

pred gears_extended[s: State] {
  all ls: LandingSet | s.f_gears_extended[ls] = True
}

pred gears_retracted[s: State] {
  all ls: LandingSet | s.f_gears_retracted[ls] = True
}

pred doors_closed[s: State] {
  all ls: LandingSet | s.f_doors_closed[ls] = True
}

pred doors_open[s: State] {
  all ls: LandingSet | s.f_doors_open[ls] = True
}

pred a_gear_extended[s: State] {
  some ls: LandingSet | s.f_gears_extended[ls] = True
}

pred a_gear_retracted[s: State] {
  some ls: LandingSet | s.f_gears_retracted[ls] = True
}

pred a_door_closed[s: State] {
  some ls: LandingSet | s.f_doors_closed[ls] = True
}

pred a_door_open[s: State] {
  some ls: LandingSet | s.f_doors_open[ls] = True
}

pred green_light[s: State] {
  s.gears = EXTENDED
}

pred orange_light[s: State] {
  s.gears = EXTENDING or s.gears = RETRACTING
}

pred red_light[s: State] {
  s.anomaly = True
}

sig State {
  /* env */ handle: one HandleStatus,
  doors: one DoorStatus,
  gears: one GearStatus,

  general_electro_valve: one Bool,
  open_doors_electro_valve: one Bool,
  close_doors_electro_valve: one Bool,
  retract_gears_electro_valve: one Bool,
  extend_gears_electro_valve: one Bool,

  // === sensors ===
  // gears_extended is true if the corresponding gear is locked in
  // the extended position and false in other cases
  /* env */ f_gears_extended: LandingSet one -> one Bool,
  // gears_retracted is true if the corresponding gear is locked in
  // the retracted position and false in other cases
  /* env */ f_gears_retracted: LandingSet one -> one Bool,
  // doors_closed is true if and only if the corresponding door is
  // locked closed
  /* env */ f_doors_closed: LandingSet one -> one Bool,
  // doors_open is true if and only if the corresponding door is
  // locked open
  /* env */ f_doors_open: LandingSet one -> one Bool,

  /* env */ timeout: one Bool,
  anomaly: one Bool
}

pred pre_retraction_sequence[s: State] {
  not(s.anomaly = True)
  s.handle = UP
}
pred post_retraction_sequence[s, s': State] {
  s.gears != RETRACTED implies {
    s.doors = CLOSED implies {
      s'.doors = OPENING
      s'.gears = s.gears
      s'.general_electro_valve = True
      s'.open_doors_electro_valve = True
      s'.close_doors_electro_valve = s.close_doors_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = CLOSING implies {
      s'.doors = OPENING
      s'.gears = s.gears
      s'.open_doors_electro_valve = True
      s'.close_doors_electro_valve = False
      s'.general_electro_valve = s.general_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = OPENING implies {
      doors_open[s] implies {
        s'.doors = OPEN
        s'.open_doors_electro_valve = False
      }
      s'.gears = s.gears
      s'.general_electro_valve = s.general_electro_valve
      s'.close_doors_electro_valve = s.close_doors_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = OPEN implies {
      s.gears = EXTENDED implies {
        s'.gears = RETRACTING
        s'.retract_gears_electro_valve = True
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
        s'.extend_gears_electro_valve = s.extend_gears_electro_valve
      }
      else s.gears = RETRACTING implies {
        gears_retracted[s] implies {
          s'.gears = RETRACTED
          s'.retract_gears_electro_valve = False
        }
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
        s'.extend_gears_electro_valve = s.extend_gears_electro_valve
      }
      else s.gears = EXTENDING implies {
        s'.gears = RETRACTING
        s'.extend_gears_electro_valve = False
        s'.retract_gears_electro_valve = True
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
      }
      s'.doors = s.doors
    }
  }
  else {
    close_door[s, s']
    s'.gears = s.gears
    s'.general_electro_valve = s.general_electro_valve
    s'.open_doors_electro_valve = s.open_doors_electro_valve
    s'.close_doors_electro_valve = s.close_doors_electro_valve
    s'.retract_gears_electro_valve = s.retract_gears_electro_valve
    s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  }
  s'.handle = s.handle
  s'.f_gears_extended = s.f_gears_extended
  s'.f_gears_retracted = s.f_gears_retracted
  s'.f_doors_closed = s.f_doors_closed
  s'.f_doors_open = s.f_doors_open
}
pred retraction_sequence[s, s': State] {
  pre_retraction_sequence[s]
  post_retraction_sequence[s, s']
}

pred pre_outgoing_sequence[s: State] {
  not(s.anomaly = True)
  s.handle != UP
}
pred post_outgoing_sequence[s, s': State] {
  s.gears != EXTENDED implies {
    s.doors = CLOSED implies {
      s'.doors = OPENING
      s'.gears = s.gears
      s'.general_electro_valve = True
      s'.open_doors_electro_valve = True
      s'.close_doors_electro_valve = s.close_doors_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = OPENING implies {
      doors_open[s] implies {
        s'.doors = OPEN
        s'.open_doors_electro_valve = False
      }
      s'.gears = s.gears
      s'.general_electro_valve = s.general_electro_valve
      s'.close_doors_electro_valve = s.close_doors_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = CLOSING implies {
      s'.doors = OPENING
      s'.gears = s.gears
      s'.general_electro_valve = s.general_electro_valve
      s'.open_doors_electro_valve = s.open_doors_electro_valve
      s'.close_doors_electro_valve = s.close_doors_electro_valve
      s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      s'.extend_gears_electro_valve = s.extend_gears_electro_valve
    }
    else s.doors = OPEN implies {
      s.gears = RETRACTED implies {
        s'.gears = EXTENDING
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
        s'.retract_gears_electro_valve = s.retract_gears_electro_valve
        s'.extend_gears_electro_valve = True
      }
      else s.gears = EXTENDING implies {
        gears_extended[s] implies {
          s'.gears = EXTENDED
          s'.extend_gears_electro_valve = False
        }
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
        s'.retract_gears_electro_valve = s.retract_gears_electro_valve
      }
      else s.gears = RETRACTING implies {
        s'.gears = EXTENDING
        s'.general_electro_valve = s.general_electro_valve
        s'.open_doors_electro_valve = s.open_doors_electro_valve
        s'.close_doors_electro_valve = s.close_doors_electro_valve
        s'.retract_gears_electro_valve = False
        s'.extend_gears_electro_valve = True
      }
      s'.doors = s.doors
    }
  }
  else {
    close_door[s, s']
    s'.gears = s.gears
    s'.general_electro_valve = s.general_electro_valve
    s'.open_doors_electro_valve = s.open_doors_electro_valve
    s'.close_doors_electro_valve = s.close_doors_electro_valve
    s'.retract_gears_electro_valve = s.retract_gears_electro_valve
    s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  }
  s'.handle = s.handle
  s'.f_gears_extended = s.f_gears_extended
  s'.f_gears_retracted = s.f_gears_retracted
  s'.f_doors_closed = s.f_doors_closed
  s'.f_doors_open = s.f_doors_open
}
pred outgoing_sequence[s, s': State] {
  pre_outgoing_sequence[s]
  post_outgoing_sequence[s, s']
}

pred health_monitoring[s, s': State] {
  (s.open_doors_electro_valve = True
   and a_door_closed[s]
   and s.timeout = True) implies s'.anomaly = True
          
  (s.open_doors_electro_valve = True
   and not(doors_open[s])
   and s.timeout = True) implies s'.anomaly = True

  (s.close_doors_electro_valve = True
   and a_door_open[s]
   and s.timeout = True) implies s'.anomaly = True

  (s.close_doors_electro_valve = True
   and not(doors_closed[s])
   and s.timeout = True) implies s'.anomaly = True

  (s.retract_gears_electro_valve = True
   and a_gear_extended[s]
   and s.timeout = True) implies s'.anomaly = True
          
  (s.retract_gears_electro_valve = True
   and not(gears_retracted[s])
   and s.timeout = True) implies s'.anomaly = True

  (s.extend_gears_electro_valve = True
   and a_gear_retracted[s]
   and s.timeout = True) implies s'.anomaly = True

  (s.extend_gears_electro_valve = True
   and not(gears_extended[s])
   and s.timeout = True) implies s'.anomaly = True
}

pred toggle_handle[s, s': State] {
  s.handle = UP implies s'.handle = DOWN else s'.handle = UP
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_extended = s.f_gears_extended
  s'.f_gears_retracted = s.f_gears_retracted
  s'.f_doors_closed = s.f_doors_closed
  s'.f_doors_open = s.f_doors_open
}

pred toggle_gears_extended[s, s': State, ls: LandingSet] {
  s.f_gears_extended[ls] = True
  implies s'.f_gears_extended[ls] = False
  else s'.f_gears_extended[ls] = True

  s'.handle = s.handle
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_retracted[ls] = s.f_gears_retracted[ls]
  s'.f_doors_closed[ls] = s.f_doors_closed[ls]
  s'.f_doors_open[ls] = s.f_doors_open[ls]
}

pred toggle_gears_retracted[s, s': State, ls: LandingSet] {
  s.f_gears_retracted[ls] = True
  implies s'.f_gears_retracted[ls] = False
  else s'.f_gears_retracted[ls] = True

  s'.handle = s.handle
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_extended[ls] = s.f_gears_extended[ls]
  s'.f_doors_closed[ls] = s.f_doors_closed[ls]
  s'.f_doors_open[ls] = s.f_doors_open[ls]
}

pred toggle_doors_closed[s, s': State, ls: LandingSet] {
  s.f_doors_closed[ls] = True
  implies s'.f_doors_closed[ls] = False
  else s'.f_doors_closed[ls] = True

  s'.handle = s.handle
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_extended[ls] = s.f_gears_extended[ls]
  s'.f_gears_retracted[ls] = s.f_gears_retracted[ls]
  s'.f_doors_open[ls] = s.f_doors_open[ls]
}

pred toggle_doors_open[s, s': State, ls: LandingSet] {
  s.f_doors_open[ls] = True
  implies s'.f_doors_open[ls] = False
  else s'.f_doors_open[ls] = True

  s'.handle = s.handle
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_extended[ls] = s.f_gears_extended[ls]
  s'.f_gears_retracted[ls] = s.f_gears_retracted[ls]
  s'.f_doors_closed[ls] = s.f_doors_closed[ls]
}

pred toggle_timeout[s, s': State] {
  s.timeout = True
  implies s'.timeout = False
  else s'.timeout = True

  s'.handle = s.handle
  s'.doors = s.doors
  s'.gears = s.gears
  s'.general_electro_valve = s.general_electro_valve
  s'.open_doors_electro_valve = s.open_doors_electro_valve
  s'.close_doors_electro_valve = s.close_doors_electro_valve
  s'.retract_gears_electro_valve = s.retract_gears_electro_valve
  s'.extend_gears_electro_valve = s.extend_gears_electro_valve
  s'.f_gears_extended = s.f_gears_extended
  s'.f_gears_retracted = s.f_gears_retracted
  s'.f_doors_closed = s.f_doors_closed
  s'.f_doors_open = s.f_doors_open
}


pred init[s: State] {
  s.doors = CLOSED
  s.gears = EXTENDED
  s.general_electro_valve = False
  s.open_doors_electro_valve = False
  s.close_doors_electro_valve = False
  s.retract_gears_electro_valve = False
  s.extend_gears_electro_valve = False
  s.anomaly = False
}

pred next[s, s': State, ls: LandingSet] {
  health_monitoring[s, s']
  not(s.anomaly = True) implies {
    retraction_sequence[s, s']
    or outgoing_sequence[s, s']
    or toggle_handle[s, s']
    or toggle_gears_extended[s, s', ls]
    or toggle_gears_retracted[s, s', ls]
    or toggle_doors_closed[s, s', ls]
    or toggle_doors_open[s, s', ls]
    or toggle_timeout[s, s']
  }
}


fact traces {
  init[StateOrdering/first]
  all s: State-StateOrdering/last, ls: LandingSet |
    let s' = s.StateOrdering/next |
      next[s, s', ls]
}

check {
  all s: State |
    (s.gears = EXTENDING or s.gears = RETRACTING) implies s.doors = OPEN
}

check {
  all s: State |
    s.doors = CLOSED implies (s.gears = EXTENDED or s.gears = RETRACTED)
}

check R11_bis {
  all s: State-StateOrdering/last |
    (s.handle = DOWN) implies {
       some s': s.*StateOrdering/next |
         s'.gears = EXTENDED and s'.doors = CLOSED
     }
}

/*
check R12_bis_not_exactly {
  all s: State-StateOrdering/last |
    (s.handle = UP) implies {
       some s': s.*StateOrdering/next |
         s'.gears = RETRACTED and s'.doors = CLOSED
     }
} for 5 State
*/

check R21 {
  all s: State-StateOrdering/last |
    (s.handle = DOWN) implies {
       s.StateOrdering/next.gears != RETRACTING
     }
}

check R22 {
  all s: State-StateOrdering/last |
    (s.handle = UP) implies {
       s.StateOrdering/next.gears != EXTENDING
     }
}

check R31 {
  all s: State |
    (s.extend_gears_electro_valve = True
     or s.retract_gears_electro_valve = True) implies s.doors = OPEN
}

check R32 {
  all s: State |
    (s.open_doors_electro_valve = True
     or s.close_doors_electro_valve = True) implies
     { s.gears = RETRACTED or s.gears = EXTENDED }
}

check R41 {
  all s: State |
    not(s.open_doors_electro_valve = True
        and s.close_doors_electro_valve = True)
}

check R42 {
  all s: State |
    not(s.extend_gears_electro_valve = True
        and s.retract_gears_electro_valve = True)
}

check R51 {
  all s: State |
    (s.open_doors_electro_valve = True
     or s.close_doors_electro_valve = True
     or s.extend_gears_electro_valve = True
     or s.retract_gears_electro_valve = True) implies
     { s.general_electro_valve = True }
}

check R61 {
  all s: State |
    (s.open_doors_electro_valve = True
     and a_door_closed[s]
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R62 {
  all s: State |
    (s.close_doors_electro_valve = True
     and a_door_open[s]
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R63 {
  all s: State |
    (s.retract_gears_electro_valve = True
     and a_gear_extended[s]
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R63 {
  all s: State |
    (s.extend_gears_electro_valve = True
     and a_gear_retracted[s]
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R71 {
  all s: State-StateOrdering/last |
    (s.open_doors_electro_valve = True
     and not(doors_open[s])
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R72 {
  all s: State-StateOrdering/last |
    (s.close_doors_electro_valve = True
     and not(doors_closed[s])
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R73 {
  all s: State-StateOrdering/last |
    (s.retract_gears_electro_valve = True
     and not(gears_retracted[s])
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

check R74 {
  all s: State-StateOrdering/last |
    (s.extend_gears_electro_valve = True
     and not(gears_extended[s])
     and s.timeout = True) implies {
       all s': s.^StateOrdering/next | s'.anomaly = True
     }
}

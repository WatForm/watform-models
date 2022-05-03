// R11_bis
AG(AG({handle = down}) => AF({gears = extended & doors = closed}))
// R12_bis
AG(AG({handle = up}) => AF({gears = retracted & doors = closed}))
// R21
AG(AG({handle = down}) => AX(AG({gears /= retracting})))
// R22
AG(AG({handle = up}) => AX(AG({gears /= extending})))

// R31
AG({(extend_gears_electro_valve = TRUE or retract_gears_electro_valve = TRUE) => doors = open})
// R32
AG({(open_doors_electro_valve = TRUE or close_doors_electro_valve = TRUE) => (gears = retracted or gears = extended)})
// R41
AG({not(open_doors_electro_valve = TRUE & close_doors_electro_valve = TRUE)})
// R42
AG({not(extend_gears_electro_valve = TRUE & retract_gears_electro_valve = TRUE)})
// R51
AG({(open_doors_electro_valve = TRUE or close_doors_electro_valve = TRUE or extend_gears_electro_valve = TRUE or retract_gears_electro_valve = TRUE) => general_electro_valve = TRUE})

// R61
AG({open_doors_electro_valve = TRUE & a_door_closed & timeout} => AX(AG({anomaly = TRUE})))
// R62
AG({close_doors_electro_valve = TRUE & a_door_open & timeout} => AX(AG({anomaly = TRUE})))
// R63
AG({retract_gears_electro_valve = TRUE & a_gear_extended & timeout} => AX(AG({anomaly = TRUE})))
// R64
AG({extend_gears_electro_valve = TRUE & a_gear_retracted & timeout} => AX(AG({anomaly = TRUE})))

// R71
AG({open_doors_electro_valve = TRUE & not(doors_open) & timeout} => AX(AG({anomaly = TRUE})))
// R72
AG({close_doors_electro_valve = TRUE & not(doors_closed) & timeout} => AX(AG({anomaly = TRUE})))
// R73
AG({retract_gears_electro_valve = TRUE & not(gears_retracted) & timeout} => AX(AG({anomaly = TRUE})))
// R74
AG({extend_gears_electro_valve = TRUE & not(gears_extended) & timeout} => AX(AG({anomaly = TRUE})))

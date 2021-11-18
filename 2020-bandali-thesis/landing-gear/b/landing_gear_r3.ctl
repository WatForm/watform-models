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

---- MODULE MC ----
EXTENDS musical_chairs_pluscal, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2, p3, p4
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT definitions PLAYERS
const_1577081127668130000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions CHAIRS
const_1577081127668131000 == 
{c1, c2, c3}
----

\* PROPERTY definition @modelCorrectnessProperties:3
prop_1577081127668137000 ==
<>[](state = "Sitting" /\ Cardinality(activePlayers) = 1)
----
=============================================================================
\* Modification History
\* Created Mon Dec 23 01:05:27 EST 2019 by bandali

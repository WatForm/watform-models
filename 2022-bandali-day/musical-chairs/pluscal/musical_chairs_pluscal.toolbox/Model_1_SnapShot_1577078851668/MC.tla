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
const_157707884965058000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions CHAIRS
const_157707884965059000 == 
{c1, c2, c3}
----

=============================================================================
\* Modification History
\* Created Mon Dec 23 00:27:29 EST 2019 by bandali

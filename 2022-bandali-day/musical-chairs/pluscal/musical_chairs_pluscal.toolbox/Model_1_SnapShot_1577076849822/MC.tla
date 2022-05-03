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
const_157707684781037000 == 
{p1, p2, p3, p4}
----

\* MV CONSTANT definitions CHAIRS
const_157707684781038000 == 
{c1, c2, c3}
----

=============================================================================
\* Modification History
\* Created Sun Dec 22 23:54:07 EST 2019 by bandali

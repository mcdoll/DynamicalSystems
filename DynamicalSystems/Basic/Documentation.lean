import VersoManual

import DynamicalSystems.Basic.Autonomous
import DynamicalSystems.Basic.ComparisonFunctions
import DynamicalSystems.Basic.LpLoc
import DynamicalSystems.Basic.NonAutonomous

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Basics" =>
%%%
tag := "basics"
htmlSplit := .never
%%%

In this section, we collect definitions and results needed for the abstract treatment of dynamical
systems, which are not yet in mathlib. The previous section was concerned with properties of
differential equations, but here we take the view that a

# Local `Lp` spaces
%%%
tag := "lploc"
%%%

{docstring MeasureTheory.MemLpLoc}

# Abstract solution operators

For autonomous equations, the solution operator can be represented using {name}`Flow` as a map
`ℝ → E → E`.
For non-autonomous systems, the solution operator is not time-covariant, therefore one has to take
the initial time into account. We prove a bundled map

{docstring NonautonomousFlow}

Note that this does not automatically imply {name}`Flow` in the autonomous case, because we do not
assume continuity here.

# Comparison functions

{docstring MemK}
{docstring MemKOn}

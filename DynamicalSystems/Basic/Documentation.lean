import VersoManual

import DynamicalSystems.Basic.Autonomous
import DynamicalSystems.Basic.ComparisonFunctions
import DynamicalSystems.Basic.LpLoc
import DynamicalSystems.Basic.NonAutonomous

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Prerequirements" =>

In this section, we collect definitions and results needed for the abstract treatment of dynamical
systems, which are not yet in mathlib. The previous section was concerned with properties of
differential equations, but here we take the view that a

import VersoManual

import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall
import DynamicalSystems.Mathlib.Analysis.ODE.PicardLindelof
import DynamicalSystems.Mathlib.Analysis.ODE.Transform
import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Ordinary differential equations" =>

In this section, we will recall the required theory of ordinary differential equations.
Most of this should end up in mathlib.

We consider the initial value problem
$$`\dot{x} &= f(x, t)\\x(0) &= x_0`
with various assumptions on the regularity of `f`.

- local existence and uniqueness (already in mathlib)
- global existence
- fundamental solution
- Peano existence result
- Caratheodory existence result

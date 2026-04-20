import VersoManual

import DynamicalSystems.Mathlib.Analysis.ODE.Basic
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

- local existence and uniqueness
- global existence
- fundamental solution

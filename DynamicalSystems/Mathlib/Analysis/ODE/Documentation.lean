import VersoManual

import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory
import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Ordinary differential equations" =>

In this section, we will recall the required theory of ordinary differential equations.
Most of this should end up in mathlib.

We consider the initial value problem
$$`\begin{aligned}
  \dot{x} &= f(x, t)\\
  x(0) &= x_0
\end{aligned}`
with various assumptions on the regularity of `f`.

# Local existence and uniqueness

{docstring IsPicardLindelof.exists_forall_mem_closedBall_eq_isIntegralCurveOn}

{docstring IsIntegralCurveOn.eqOn_inter}

## Uniformly locally Lipschitz maps

We define functions `f : ℝ → E → E` that are locally uniformly Lipschitz.

{docstring UniformlyLocallyLipschitzOn}
{docstring UniformlyLocallyLipschitz}

We prove that locally uniformly Lipschitz functions satisfy the Picard--Lindelöf conditions

{docstring UniformlyLocallyLipschitzOn.isPicardLindelof}

# Global existence

# Peano existence

# Caratheodory existence

{docstring IsAEIntegralCurve}

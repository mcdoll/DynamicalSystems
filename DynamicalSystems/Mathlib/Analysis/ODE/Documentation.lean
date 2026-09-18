import VersoManual

import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory
import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory.Picard
import DynamicalSystems.Mathlib.Analysis.ODE.Caratheodory.Global
import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitz

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false
set_option verso.docstring.allowMissing true

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

For control systems with non-smooth or measurable inputs (e.g. $`L^1` or $`L^p_{\mathrm{loc}}`
controls), the vector field is no longer continuous in time. We formalize Carathéodory
differential equations following the classical theory of Pražák (2024), Carvalho-Neto et
al. (2025), and O'Regan (1997).

## Carathéodory regularity and Lipschitz bounds

{docstring IsCaratheodory}
{docstring IsCaratheodoryLipschitz}
{docstring IsCaratheodorySolutionOn}
{docstring IsAEIntegralCurve}
{docstring IsCaratheodorySolutionOn.ae_hasDerivWithinAt}
{docstring IsCaratheodorySolutionOn.isAEIntegralCurve}

## Generalized Picard Contraction

On any compact interval where $`\int_a^b \ell(s) \, ds < 1`, the Picard operator defines
a strict contraction on $`C([a, b], E)`:

{docstring caratheodoryPicardCM}
{docstring dist_caratheodoryPicardCM_le}
{docstring exists_unique_caratheodory_solution_of_small_integral}
{docstring isCaratheodorySolutionOn_unique_of_small_integral}

## Linear Carathéodory systems and Global Patching

Linear time-dependent systems $`x \mapsto A(t)x + b(t)` are automatically Carathéodory-Lipschitz,
and local solutions on expanding intervals patch into global solutions on $`\mathbb{R}`:

{docstring isCaratheodoryLinear}
{docstring isCaratheodoryLipschitz_linear}
{docstring isCaratheodorySolutionOn_patching}
{docstring exists_unique_caratheodory_solution_global}

import VersoManual
import Lean

import DynamicalSystems.Stability.Basic
import DynamicalSystems.Stability.Example
import DynamicalSystems.Stability.InputToState
import DynamicalSystems.Stability.LaSalle
import DynamicalSystems.Stability.Lyapunov

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false

#doc (Manual) "Stability" =>

# Basic stability

We start by introducing the most basic notions of stability and how to use them in Lean.
This will include Lyapunov stability and asymptotic stability. We will illustrate how to
employ LaSalle's invariance principle to prove asymptotic stability even if the Lyapunov
function is not strictly decreasing everywhere.

```lean -show
variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Topology
open Filter Set Metric

variable {Φ : ℝ → E → E} {x₀ : E} {s : Set E}
```
Throughout this document, we will assume that `E` is a normed space over `ℝ`.


## Lyapunov stability
Consider a dynamical system $`\dot{x} = f(x)` a subset $`s` is called stable if all trajectories
that are close to $`s` stay close to $`s`. This condition can be naturally phrased in terms of
{lean}`Filter`:

{docstring Filter.IsStableOn}

The typical case is that `l` is given by the neighbourhood filter {lean}`nhds x₀`. Then we recover
the usual definition:
```lean
example (x₀ : E) : (𝓝 x₀).IsStableOn Φ (Ici 0) ↔
    ∀ ε > 0, ∀ t₀ ≥ 0, ∃ δ > 0, ∀ x,
    ‖x - x₀‖ < δ → ∀ t ≥ t₀, dist ‖Φ t x - x₀‖ < ε := by
  sorry
```

More generally, we can take the set neighbourhood filter {lean}`nhdsSet s`, then we have
```lean
example (s : Set E) : (𝓝ˢ s).IsStableOn Φ (Ici 0) ↔
    ∀ ε > 0, ∀ t₀ ≥ 0, ∃ δ > 0, ∀ x,
    infDist x s < δ → ∀ t ≥ t₀, infDist (Φ t x) s < ε := by
  sorry
```

## Asymptotic stability
Global asymptotic stability requires that an equilibrium point is Lyapunov stable and all
trajectories converge to the equilibrium point. In Lean, we are not defining a predicate for this,
so to state that a point is asymptotic stable, one simply writes that it is stable and all
trajectories converge. We note that in the case of the filter {lean}`nhdsSet s`, we can check
convergence similarly to the convergence of points
```lean
variable {f : α → E} {l : Filter α}

example (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s) :
    Tendsto f l (𝓝ˢ s) ↔
    ∀ ε > 0, ∀ᶠ x in l, infDist (f x) s < ε := by
  exact tendsto_nhdsSet hs₁ hs₂
```

Local asymptotic stability is defined being locally attractive and stable, where locally attractive
means that the flow of points close to the set converge to the set:

{docstring Filter.IsAttractive}

## Lyapunov functions
The most common way to prove stability of equilibrium points (or limit cycles) is to employ
_Lyapunov's direct method_, also known as the method of Lyapunov functions. A Lyapunov function
is a continuous function that is
1) strictly positive except at the equilibrium point,
2) zero at the equilibrium point,
3) decreasing along the flow.

Lyapunov's theorem asserts that if such a function exists, then the equilibrium point is stable.
In addition if the Lyapunov function is _strictly_ decreasing along the flow, then the equilibrium
is asymptotically stable.

Currently, we only prove Lyapunov's theorem for Lyapunov functions that are independent of the time
variable.

We provide a local and a global version of a Lyapunov function:

{docstring IsLyapunovOn}
{docstring IsLyapunov}

Lyapunov's theorem can be stated as

{docstring IsLyapunovOn.isStableOn_nhdsSet}
{docstring IsLyapunovOn.isStableOn_nhds}
{docstring IsLyapunov.isStableOn_nhdsSet}
{docstring IsLyapunov.isStableOn_nhds}

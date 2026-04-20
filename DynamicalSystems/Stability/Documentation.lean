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

We introduce several notions of stability.

```lean -show
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Topology
open Filter Set

variable {Φ : ℝ → E → E}
```
Throught this document, we will assume that `E` is a normed space over `ℝ`.

- Lyapunov stability
- input to state stability

Let $`l` be a {lean}`Filter` and $`Φ` be a map from $`ℝ × E` to $`E`.
Then $`Φ` is {lean}`Filter.IsStableOn` the filter $`l` if for every `s ∈ l` there exists `s' ∈ l`,
such that for all `x ∈ s'` the flow of `x` is contained in `s`.

The typical case is that `l` is given by the neighbourhood filter of `x₀ : E`. Then we recover the
usual definition:
```lean
example (x₀ : E) : (𝓝 x₀).IsStableOn Φ (Ici 0) ↔
    ∀ ε > 0, ∀ t₀ ≥ 0, ∃ δ > 0, ∀ x,
    ‖x - x₀‖ < δ → ∀ t ≥ t₀, dist ‖Φ t x - x₀‖ < ε := by
  sorry
```

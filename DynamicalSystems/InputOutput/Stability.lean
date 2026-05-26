/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Causal

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [Bornology α] [MeasurableSpace α]

variable {f : (α → E) → α → E}
variable {k β : ℝ≥0} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

/-- Not clear what is the right definition, Sastry and Khalil don't agree on whether causality
is part of finite gain stability. -/
structure IsFiniteGainStableWith (f : (α → E) → α → F) (k β : ℝ≥0) (s : ι → Set α) (p : ℝ≥0∞)
    (μ : Measure α) where
  memLpLoc : ∀ u, MemLpLoc u p μ → MemLpLoc (f u) p μ
  stableWith : ∀ t u (_hu : MemLpLoc u p μ),
    eLpNorm (f u) p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

/-- A map is called `Lp`-stable if it maps `Lp` to `Lp`. -/
structure IsLpStable (f : (α → E) → α → F) (p : ℝ≥0∞) (μ : Measure α) where
  memLp : ∀ u, MemLp u p μ → MemLp (f u) p μ

namespace IsFiniteGainStableWith

theorem isLpStable (hf : IsFiniteGainStableWith f k β s p μ)
    (hfu : ∀ u (hu : MemLp u p μ), AEStronglyMeasurable (f u) μ) :
    IsLpStable f p μ := by
  refine ⟨fun u hu ↦ ⟨hfu u hu, ?_⟩⟩
  sorry

end IsFiniteGainStableWith

/-- Proposition 1.2.2 in van der Schaft. -/
theorem IsCausal.isFiniteGainStableWith (hf : IsCausal f s p μ) (k β : ℝ≥0)
    (h : ∀ u (hu : MemLp u p μ), eLpNorm (f u) p μ ≤ k * eLpNorm u p μ + β) :
    IsFiniteGainStableWith f k β s p μ := by
  constructor
  · intro u hu
    apply hf.1 u hu
  · intro t u hu
    sorry

/- Todo: define the gain -/

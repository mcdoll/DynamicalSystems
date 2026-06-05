/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Causal

/-! # Stability of input-output maps -/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [MeasurableSpace α]

section IsLpStable

/-! ## `Lp` stability -/

namespace SetRel

/-- A relation is called `Lp`-stable if it maps `Lp` to `Lp`. -/
structure IsLpStable (f : SetRel (α → E) (α → F)) (p : ℝ≥0∞) (μ : Measure α) where
  /-- For every pair `(u, y) ∈ f` if `u` is in `Lp` then `y` is also in `Lp`. -/
  memLp : ∀ ⦃u⦄, MemLp u p μ → ∀ y, (u, y) ∈ f → MemLp y p μ

variable {f : SetRel (α → E) (α → E)} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

end SetRel

namespace Function

/-- A map is called `Lp`-stable if it maps `Lp` to `Lp`. -/
@[fun_prop]
structure IsLpStable (f : (α → E) → α → F) (p : ℝ≥0∞) (μ : Measure α) where
  /-- Every `u` in `Lp` gets mapped to `Lp`. -/
  memLp : ∀ ⦃u⦄, MemLp u p μ → MemLp (f u) p μ

variable {f : (α → E) → α → E} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

theorem graph_isLpStable_iff_isLpStable : f.graph.IsLpStable p μ ↔ f.IsLpStable p μ := by
  constructor
  · intro h
    refine ⟨fun u hu ↦ ?_⟩
    apply h.memLp hu (f u)
    exact mem_graph.mpr rfl
  · intro h
    refine ⟨fun u hu y hy ↦ ?_⟩
    simp only [mem_graph] at hy
    rw [← hy]
    exact h.memLp hu

end Function

end IsLpStable

section IsFiniteGainStable

/-! ## Finite gain stability -/

variable [Bornology α]

namespace SetRel

variable (f : SetRel (α → E) (α → E))

/-- A map is called finite gain stable with gain less than `k` if there exists `β` such that
for all local `Lp` functions `u`, we have the `Lp`-norm estimate `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β`.

Version for relations. -/
structure IsFiniteGainStableWith (f : SetRel (α → E) (α → E)) (k β : ℝ≥0) (s : ι → Set α) (p : ℝ≥0∞)
    (μ : Measure α) where
  /-- For every pair `(u, y) ∈ f` if `u` is in `LpLoc` then `y` is also in `LpLoc`. -/
  memLpLoc : ∀ u, MemLpLoc u p μ → ∀ y, (u, y) ∈ f → MemLpLoc y p μ
  /-- For every pair `(u, y) ∈ f` with `u` in `LpLoc`, we have `‖yₜ‖ ≤ k * ‖uₜ‖ + β`. -/
  stableWith : ∀ t u y (_hu : MemLpLoc u p μ) (_hy : MemLpLoc y p μ) (_h : (u, y) ∈ f),
    eLpNorm y p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

end SetRel

namespace Function

variable {f : (α → E) → α → E}
variable {k β : ℝ≥0} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

/-- A map is called finite gain stable with gain less than `k` if there exists `β` such that
for all local `Lp` functions `u`, we have the `Lp`-norm estimate `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β`. -/
structure IsFiniteGainStableWith (f : (α → E) → α → F) (k β : ℝ≥0) (s : ι → Set α) (p : ℝ≥0∞)
    (μ : Measure α) where
  /-- Every `u` in `Lp` gets mapped to `Lp`. -/
  memLpLoc : ∀ ⦃u⦄, MemLpLoc u p μ → MemLpLoc (f u) p μ
  /-- For every `u` in `LpLoc`, we have `‖yₜ‖ ≤ k * ‖(f u)ₜ‖ + β`. -/
  stableWith : ∀ t u (_hu : MemLpLoc u p μ),
    eLpNorm (f u) p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

namespace IsFiniteGainStableWith

theorem isLpStable (hf : IsFiniteGainStableWith f k β s p μ)
    (hfu : ∀ u (hu : MemLp u p μ), AEStronglyMeasurable (f u) μ) :
    IsLpStable f p μ := by
  refine ⟨fun u hu ↦ ⟨hfu u hu, ?_⟩⟩
  -- there exists a countable subset of ι, such that `⋃₀ t ∈ I, s t = Set.univ`
  sorry

end IsFiniteGainStableWith

/-- Proposition 1.2.2 in van der Schaft. -/
theorem IsCausal.isFiniteGainStableWith (hf : IsCausal f s p μ) (k β : ℝ≥0)
    (h : ∀ u (hu : MemLp u p μ), eLpNorm (f u) p μ ≤ k * eLpNorm u p μ + β) :
    IsFiniteGainStableWith f k β s p μ := by
  constructor
  · intro u hu
    apply hf.1 hu
  · intro t u hu
    sorry

/- Todo: define the gain -/

-- def eLpGain (f : (α → E) → α → F) (p : ℝ≥0∞) : ℝ≥0∞ := ⨅ i, sorry

end Function

end IsFiniteGainStable

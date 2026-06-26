/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.InputOutput.Causal
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Stability of input-output maps -/

public section

open MeasureTheory Filter Bornology Set
open scoped NNReal ENNReal

variable {ι α E F G : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [MeasurableSpace α]

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

namespace SetRel

variable [TopologicalSpace α]

variable (f : SetRel (α → E) (α → E))

/-- A map is called finite gain stable with gain less than `k` if there exists `β` such that
for all local `Lp` functions `u`, we have the `Lp`-norm estimate `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β`.

Version for relations. -/
@[expose]
def IsFiniteGainStableWith (f : SetRel (α → E) (α → F)) (k β : ℝ≥0) (s : ι → Set α) (p : ℝ≥0∞)
    (μ : Measure α) : Prop :=
  ∀ t u y (_hu : MemLpLoc u p μ) (_hy : MemLpLoc y p μ) (_h : (u, y) ∈ f),
    eLpNorm y p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

/-- A map is called finite gain stable with gain less than `k` if there exists `β` such that
for all local `Lp` functions `u`, we have the `Lp`-norm estimate `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β`.

Version for relations. -/
structure IsFiniteGainStableWith' (f : SetRel (α → E) (α → F)) (k β : ℝ≥0) (s : ι → Set α)
    (p : ℝ≥0∞) (μ : Measure α) where
  /-- For every pair `(u, y) ∈ f` if `u` is in `LpLoc` then `y` is also in `LpLoc`. -/
  memLpLoc : ∀ u, MemLpLoc u p μ → ∀ y, (u, y) ∈ f → MemLpLoc y p μ
  /-- For every pair `(u, y) ∈ f` with `u` in `LpLoc`, we have `‖yₜ‖ ≤ k * ‖uₜ‖ + β`. -/
  stableWith : ∀ t u y (_hu : MemLpLoc u p μ) (_hy : MemLpLoc y p μ) (_h : (u, y) ∈ f),
    eLpNorm y p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

end SetRel

namespace Function

variable {f : (α → E) → α → F} {g : (α → F) → (α → G)}
variable {k k' β β' : ℝ≥0} {s : ι → Set α} {p : ℝ≥0∞} {μ : Measure α}

/-- A map is called finite gain stable with gain less than `k` if there exists `β` such that
for all local `Lp` functions `u`, we have the `Lp`-norm estimate `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β`. -/
structure IsFiniteGainStableWith [TopologicalSpace α] (f : (α → E) → α → F) (k β : ℝ≥0)
    (s : ι → Set α) (p : ℝ≥0∞) (μ : Measure α) where
  /-- Every `u` in `Lp` gets mapped to `Lp`. -/
  memLpLoc : ∀ ⦃u⦄, MemLpLoc u p μ → MemLpLoc (f u) p μ
  /-- For every `u` in `LpLoc`, we have `‖yₜ‖ ≤ k * ‖(f u)ₜ‖ + β`. -/
  stableWith : ∀ t u (_hu : MemLpLoc u p μ),
    eLpNorm (f u) p (μ.restrict <| s t) ≤ k * eLpNorm u p (μ.restrict <| s t) + β

namespace IsFiniteGainStableWith

variable [TopologicalSpace α]

theorem graph (h : f.IsFiniteGainStableWith k β s p μ) :
    f.graph.IsFiniteGainStableWith k β s p μ := by
  intro t u y hu hy huy
  rw [mem_graph] at huy
  rw [← huy]
  apply h.stableWith t u hu

/-- The composition of two finite gain stable maps is finite gain stable. -/
theorem comp (hg : g.IsFiniteGainStableWith k' β' s p μ) (hf : f.IsFiniteGainStableWith k β s p μ) :
    (g ∘ f).IsFiniteGainStableWith (k * k') (β * k' + β') s p μ where
  memLpLoc u hu := hg.memLpLoc (hf.memLpLoc hu)
  stableWith t u hu := calc
    _ ≤ k' * eLpNorm (f u) p _ + β' :=
      hg.stableWith t (f u) (hf.memLpLoc hu)
    _ ≤ k' * (k * eLpNorm u p _ + β) + β' := by
      gcongr; exact hf.stableWith t u hu
    _ = _ := by
      push_cast; ring

/-- The addition of two finite gain stable maps is finite gain stable. -/
theorem add {f : (α → E) → α → F} {g : (α → E) → (α → F)} (hp : 1 ≤ p)
    (hs : ∀ t, IsCompact (s t))
    (hf : f.IsFiniteGainStableWith k β s p μ) (hg : g.IsFiniteGainStableWith k' β' s p μ) :
    (f + g).IsFiniteGainStableWith (k + k') (β + β') s p μ where
  memLpLoc u hu := (hf.memLpLoc hu).add (hg.memLpLoc hu)
  stableWith t u hu := calc
    _ ≤ eLpNorm (f u) p _ + eLpNorm (g u) p _ := by
      apply eLpNorm_add_le _ _ hp
      · exact (hf.memLpLoc hu).aestronglyMeasurable (hs t)
      · exact (hg.memLpLoc hu).aestronglyMeasurable (hs t)
    _ ≤ (k * eLpNorm u p _ + β) + (k' * eLpNorm u p _ + β') := by
      gcongr
      · exact hf.stableWith t u hu
      · exact hg.stableWith t u hu
    _ = _ := by
      push_cast; ring

/-- The subtraction of two finite gain stable maps is finite gain stable. -/
theorem sub {f : (α → E) → α → F} {g : (α → E) → (α → F)} (hp : 1 ≤ p)
    (hs : ∀ t, IsCompact (s t))
    (hf : f.IsFiniteGainStableWith k β s p μ) (hg : g.IsFiniteGainStableWith k' β' s p μ) :
    (f - g).IsFiniteGainStableWith (k + k') (β + β') s p μ where
  memLpLoc u hu := (hf.memLpLoc hu).sub (hg.memLpLoc hu)
  stableWith t u hu := calc
    _ ≤ eLpNorm (f u) p _ + eLpNorm (g u) p _ := by
      apply eLpNorm_sub_le _ _ hp
      · exact (hf.memLpLoc hu).aestronglyMeasurable (hs t)
      · exact (hg.memLpLoc hu).aestronglyMeasurable (hs t)
    _ ≤ (k * eLpNorm u p _ + β) + (k' * eLpNorm u p _ + β') := by
      gcongr
      · exact hf.stableWith t u hu
      · exact hg.stableWith t u hu
    _ = _ := by
      push_cast; ring

variable [Preorder ι] [Countable ι] [Nonempty ι] [IsDirectedOrder ι]

/-- Every finite gain stable system is `Lp` stable. -/
theorem isLpStable (hf : IsFiniteGainStableWith f k β s p μ)
    (hfu : ∀ u (_hu : MemLp u p μ), AEStronglyMeasurable (f u) μ)
    (hs : AECover μ atTop s) :
    IsLpStable f p μ := by
  refine ⟨fun u hu ↦ ⟨hfu u hu, ?_⟩⟩
  /- For every `t ∈ I`, we have that `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β ≤ k * ‖u‖ + β`-/
  have : ∀ᶠ t in atTop, eLpNorm ((s t).indicator (f u)) p μ ≤ k * eLpNorm u p μ + β := by
    filter_upwards with t
    calc
      _ = eLpNorm (f u)  p (μ.restrict (s t)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (hs.measurableSet t)
      _ ≤ k * eLpNorm u p (μ.restrict <| s t) + β := hf.stableWith t u hu.memLpLoc
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  calc
    _ ≤ k * eLpNorm u p μ + β := by
      apply MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto this
      · intro t
        exact (hfu u hu).indicator (hs.measurableSet t)
      · apply hs.ae_tendsto_indicator
    _ < _ := by
      simp [MemLp.eLpNorm_lt_top hu, ENNReal.mul_lt_top_iff]

end IsFiniteGainStableWith

variable [PseudoMetricSpace α] [OpensMeasurableSpace α] [T2Space α] {k β : ℝ≥0}

/-- Every system that is causal and satisfies the finite gain estimate is for `Lp` functions is
finite gain stable.

Proposition 1.2.3 in van der Schaft. -/
theorem IsCausal.isFiniteGainStableWith (hf : IsCausal f s p μ) (hs : ∀ t, IsCompact (s t))
    (h : ∀ u (_hu : MemLp u p μ), eLpNorm (f u) p μ ≤ k * eLpNorm u p μ + β) :
    IsFiniteGainStableWith f k β s p μ := by
  constructor
  · intro u hu
    apply hf.1 hu
  · intro t u hu
    calc
      _ = eLpNorm ((s t).indicator (f u)) p μ :=
        (eLpNorm_indicator_eq_eLpNorm_restrict (hs t).measurableSet).symm
      _ = eLpNorm ((s t).indicator (f <| (s t).indicator u)) p μ := by
        rw [← hf.causal t u hu]
      _ ≤ eLpNorm (f <| (s t).indicator u) p μ :=
        eLpNorm_indicator_le (f ((s t).indicator u))
      _ ≤ ↑k * eLpNorm ((s t).indicator u) p μ + β := by
        apply h
        exact hu.memLp_indicator (hs t)
      _ = _ := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict (hs t).measurableSet]

/- Todo: define the gain -/

-- def eLpGain (f : (α → E) → α → F) (p : ℝ≥0∞) : ℝ≥0∞ := ⨅ i, sorry

end Function

end IsFiniteGainStable

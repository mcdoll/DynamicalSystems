/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Local `Lp` functions
- define restriction of Lp functions
- locally Lp functions

-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

variable {α 𝕜 𝕜' E F : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace MeasureTheory

variable {s : Set α} {f : α →ₘ[μ] E}

open Bornology

section MemLpLoc

/-! ## Local `Lp` functions
In this section we define local `Lp` functions and prove elementary properties

-/

/-- A function `u` is locally in `Lp` if for every bounded measurable set `s`, `u` is in `Lp` with
respect to measure `μ` restricted to `s`. -/
@[fun_prop]
def MemLpLoc [Bornology α] (u : α → E) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  ∀ s : Set α, MeasurableSet s ∧ IsBounded s → MemLp u p (μ.restrict s)

section Bornology

variable [Bornology α]

theorem memLpLoc_prod_iff {u : α → E × F} :
    MemLpLoc u p μ ↔ MemLpLoc (fun x ↦ (u x).1) p μ ∧ MemLpLoc (fun x ↦ (u x).2) p μ := by
  constructor
  · intro h
    exact ⟨(h · · |>.fst), (h · · |>.snd)⟩
  · intro ⟨h₁, h₂⟩ s hs
    exact MemLp.of_fst_snd ⟨h₁ s hs, h₂ s hs⟩

theorem memLpLoc_withLp_prod_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : α → WithLp p (E × F)} :
    MemLpLoc u p μ ↔ MemLpLoc (WithLp.fst <| u ·) p μ ∧ MemLpLoc (WithLp.snd <| u ·) p μ := by
  constructor
  · intro h
    exact ⟨(h · · |>.prodLp_fst), (h · · |>.prodLp_snd)⟩
  · intro ⟨h₁, h₂⟩ s hs
    exact MemLp.of_fst_of_snd_prodLp ⟨h₁ s hs, h₂ s hs⟩

variable {u v : α → E}

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.add (hu : MemLpLoc u p μ) (hv : MemLpLoc v p μ) : MemLpLoc (u + v) p μ := by
  intro s hs
  exact (hu s hs).add (hv s hs)

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.sub (hu : MemLpLoc u p μ) (hv : MemLpLoc v p μ) : MemLpLoc (u - v) p μ := by
  intro s hs
  exact (hu s hs).sub (hv s hs)

@[to_fun (attr := fun_prop)]
theorem MemLpLoc.neg (hu : MemLpLoc u p μ) : MemLpLoc (-u) p μ := by
  intro s hs
  exact (hu s hs).neg

@[to_fun (attr := fun_prop)]
theorem memLpLoc_finsetSum {ι} (s₀ : Finset ι) {u : ι → α → E} (hu : ∀ i ∈ s₀, MemLpLoc (u i) p μ) :
    MemLpLoc (∑ i ∈ s₀, u i) p μ := by
  intro s hs
  exact memLp_finsetSum' s₀ (hu · · s hs)

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E] {c : 𝕜}

@[fun_prop]
theorem MemLpLoc.const_smul (hu : MemLpLoc u p μ) : MemLpLoc (c • u) p μ := by
  intro s hs
  exact (hu s hs).const_smul c

theorem memLpLoc_iff_memLp_indicator :
    MemLpLoc u p μ ↔ ∀ s : Set α, MeasurableSet s ∧ IsBounded s → MemLp (s.indicator u) p μ := by
  congrm (∀ s, (hs : _) → ?_)
  rw [memLp_indicator_iff_restrict hs.1]

theorem MemLpLoc.memLp_indicator {s₀ : Set α} (hs₀ : MeasurableSet s₀) (hs₀' : IsBounded s₀)
    (hu : MemLpLoc u p μ) : MemLp (s₀.indicator u) p μ := by
  rw [memLpLoc_iff_memLp_indicator] at hu
  exact hu s₀ ⟨hs₀, hs₀'⟩

@[fun_prop]
theorem MemLpLoc.indicator {s₀ : Set α} (hs₀ : MeasurableSet s₀) (hu : MemLpLoc u p μ) :
    MemLpLoc (s₀.indicator u) p μ := by
  intro s hs
  exact (hu s hs).indicator hs₀

@[fun_prop]
theorem MemLp.memLpLoc (hu : MemLp u p μ) : MemLpLoc u p μ := by
  intro s _
  exact hu.restrict s

/-- In a bounded space, local `Lp` functions are in `Lp`. -/
@[simp]
theorem memLpLoc_iff_memLp [BoundedSpace α] : MemLpLoc u p μ ↔ MemLp u p μ := by
  constructor
  · intro h
    rw [← MeasureTheory.Measure.restrict_univ (μ := μ)]
    exact h Set.univ ⟨MeasurableSet.univ, BoundedSpace.bounded_univ⟩
  · apply MemLp.memLpLoc

end Bornology

section MetricSpace

variable [PseudoMetricSpace α] [ProperSpace α] [OpensMeasurableSpace α]
  [IsFiniteMeasureOnCompacts μ]

variable {u : α → E}

/-- Every continuous function is locally `Lp` -/
theorem Continuous.memLpLoc (hp : p ≠ 0) (h : Continuous u) :
    MemLpLoc u p μ := by
  intro s ⟨hs₁, hs₂⟩
  by_cases hp₂ : p = ∞
  · rw [hp₂]
    obtain ⟨C, hC⟩ := hs₂.isCompact_closure.exists_bound_of_continuousOn (f := u) (by fun_prop)
    apply memLp_top_of_bound (by fun_prop) C (ae_restrict_of_forall_mem hs₁ ?_)
    intro x hx
    exact hC _ (subset_closure hx)
  · rw [← MeasureTheory.integrable_norm_rpow_iff (by fun_prop) hp hp₂,
      ← MeasureTheory.IntegrableOn]
    apply ContinuousOn.integrableOn_of_subset_isCompact (K := closure s)
    · apply Continuous.continuousOn
      apply Continuous.rpow_const (by fun_prop)
      intro; right; positivity
    · apply hs₂.isCompact_closure
    · exact hs₁
    · exact subset_closure
    · rw [← lt_top_iff_ne_top]
      exact IsBounded.measure_lt_top hs₂

end MetricSpace

end MemLpLoc

variable [Bornology α]

variable (E p) in
/-- The space of locally Lp functions

Not clear whether the condition should be `eLpNorm (s.indicator f) p μ < ∞` instead. They are
equivalent. -/
def LpLoc (μ : Measure α := by volume_tac) : AddSubgroup (α →ₘ[μ] E) where
  carrier := { f | ∀ s : Set α, Measurable s ∧ IsBounded s → eLpNorm f p (μ.restrict s) < ∞ }
  zero_mem' := by
    intro s ⟨hs₁, hs₂⟩
    have : eLpNorm (0 : α → E) p (μ.restrict s) < ∞ := by simp
    convert this using 1
    apply eLpNorm_congr_ae
    apply Filter.EventuallyEq.restrict
    apply AEEqFun.coeFn_zero
  add_mem' {f g} hf hg := by
    intro s hs
    convert eLpNorm_add_lt_top
      ⟨f.aestronglyMeasurable.restrict, hf s hs⟩ ⟨g.aestronglyMeasurable.restrict, hg s hs⟩ using 1
    apply eLpNorm_congr_ae
    apply Filter.EventuallyEq.restrict
    filter_upwards [AEEqFun.coeFn_add f g] with x h
    simp [h]
  neg_mem' {f} hf := by
    intro s hs
    convert hf s hs using 1
    rw [← eLpNorm_neg]
    apply eLpNorm_congr_ae
    apply Filter.EventuallyEq.restrict
    filter_upwards [AEEqFun.coeFn_neg f] with x h
    simp [h]


end MeasureTheory

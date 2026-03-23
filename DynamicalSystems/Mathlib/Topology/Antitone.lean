/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

variable {ι α : Type*}
  [Preorder ι] [TopologicalSpace α]
  [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α]

open scoped Topology

/-- A bounded antitone function converges to some point. -/
theorem Antitone.exists_tendsto {f : ι → α} (h_anti : Antitone f) (hbdd : BddBelow (Set.range f)) :
    ∃ c, Filter.Tendsto f Filter.atTop (𝓝 c) :=
  ⟨iInf f, tendsto_atTop_ciInf h_anti hbdd⟩

/-- A bounded antitone function converges to some point.

Version where we only assume boundedness and monotonicity on an interval. -/
theorem AntitoneOn.exists_tendsto [IsDirectedOrder ι] {f : ι → α} {i : ι}
    (h_anti : AntitoneOn f (Set.Ici i)) (hbdd : ∃ c, ∀ t ∈ Set.Ici i, c ≤ f t) :
    ∃ c, Filter.Tendsto f Filter.atTop (𝓝 c) := by
  classical
  set f' : ι → α := fun t ↦ if i ≤ t then f t else f i
  have h_anti' : Antitone f' := by
    intro t₀ t₁ ht
    by_cases ht₀ : i ≤ t₀
    · have ht₁ : i ≤ t₁ := ht₀.trans ht
      simpa [f', ht₀, ht₁] using h_anti ht₀ ht₁ ht
    · by_cases ht₁ : i ≤ t₁
      · simpa [f', ht₀, ht₁] using h_anti (le_refl _) ht₁ ht₁
      · simp [f', ht₀, ht₁]
  have hbdd' : BddBelow (Set.range f') := by
    obtain ⟨c, h⟩ := hbdd
    use c
    simp_rw [mem_lowerBounds, Set.mem_range]
    rintro _ ⟨t, rfl⟩
    by_cases ht : i ≤ t
    all_goals { simp [f', ht, h] }
  obtain ⟨c, hc⟩ := h_anti'.exists_tendsto hbdd'
  use c
  apply hc.congr'
  haveI : Nonempty ι := ⟨i⟩
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  use i
  intro t ht
  simp [f', ht]

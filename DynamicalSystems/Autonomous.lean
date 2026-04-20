/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

--public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution
public import DynamicalSystems.Mathlib.Dynamics.Basic
public import DynamicalSystems.Mathlib.Topology.LimitSet

/-!
# Invariant sets and semigroups

This file should be retired in favour of mathlib definitions.
-/


@[expose] public section

variable {ι E F : Type*}

namespace Filter

variable (Φ : ι → E → E)

/-- A set `s` is invariant under the (positive) flow if for all `x ∈ s` we have that `Φ t x ∈ s`. -/
def IsInvariantSetOn (s : Set E) (I : Set ι) : Prop :=
  ∀ x ∈ s, ∀ t ∈ I, Φ t x ∈ s

end Filter

section Semigroup

/-- Deprecated in favour of Flow -/
structure IsSemigroupOn [Add ι] [Zero ι] (Φ : ι → E → E) (s : Set E) : Prop where
  zero : ∀ x ∈ s, Φ 0 x = x
  add : ∀ t₀ t₁, ∀ x ∈ s, Φ (t₀ + t₁) x = Φ t₀ (Φ t₁ x)

/-- Deprecated in favour of Flow -/
structure IsSemigroup [Add ι] [Zero ι] (Φ : ι → E → E) : Prop where
  zero : ∀ x, Φ 0 x = x
  add : ∀ t₀ t₁ x, Φ (t₀ + t₁) x = Φ t₀ (Φ t₁ x)

variable {Φ : ι → E → E} {s : Set E} {y : E}

theorem IsSemigroupOn.mono [Add ι] [Zero ι] {s₁ s₂ : Set E}
    (hs₁ : IsSemigroupOn Φ s₂) (hs₂ : s₁ ⊆ s₂) : IsSemigroupOn Φ s₁ :=
  ⟨(hs₁.zero · <| hs₂ ·), (hs₁.add · · · <| hs₂ ·)⟩

@[simp]
theorem isSemigroup_univ [Add ι] [Zero ι] : IsSemigroupOn Φ Set.univ ↔ IsSemigroup Φ := by
  sorry

theorem IsSemigroupOn.comm [AddCommMagma ι] [Zero ι] (hΦ : IsSemigroupOn Φ s) {x : E} (hx : x ∈ s)
    (t₀ t₁ : ι) :
    Φ t₀ (Φ t₁ x) = Φ t₁ (Φ t₀ x) := by
  rw [← hΦ.add t₀ t₁ x hx, ← hΦ.add t₁ t₀ x hx, add_comm]

variable [TopologicalSpace E] [AddCommMonoid ι] [Preorder ι] [IsDirectedOrder ι] [AddLeftMono ι]
  [TopologicalSpace ι] [ContinuousAdd ι]


open Filter

variable {Φ : Flow ι E}

/-- The limit set is monotone in the flow parameter. -/
theorem limitSet_mono {t : ι} (ht : 0 ≤ t) :
    atTop.limitSet (Φ · (Φ t y)) ⊆ atTop.limitSet (Φ · y) := by
  intro x hx
  rw [mem_limitSet_iff, mapClusterPt_iff_frequently] at *
  simp only [Filter.frequently_atTop] at *
  intro s' hs' t₀
  obtain ⟨t', ht', h⟩ := hx s' hs' t₀
  use t' + t
  constructor
  · grw [ht']
    exact le_add_of_nonneg_right ht
  · rwa [Flow.map_add]

-- Todo: more general version

/-- If `Φ` is a semigroup and `Φ t` is continuous for every `t`, then the limit set is invariant. -/
theorem isInvariantSet_limitSet {y : E} {s : Set E} (hs' : atTop.limitSet (Φ · y) ⊆ s)
    (hΦ₂ : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    IsInvariantSetOn Φ (atTop.limitSet (Φ · y)) (Set.Ici 0) := by
  intro x hx t (ht : 0 ≤ t)
  have hx' : x ∈ s := hs' hx
  apply limitSet_mono ht
  rw [mem_limitSet_iff] at *
  have : (fun s ↦ Φ t (Φ s y)) =ᶠ[Filter.atTop] fun s ↦ Φ s (Φ t y) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 0
    intro s hs
    simp_rw [← Flow.map_add, add_comm]
  exact (hx.tendsto_comp (hΦ₂ t ht x hx')).congrFun this


end Semigroup

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution
public import DynamicalSystems.Mathlib.Topology.Antitone
public import DynamicalSystems.Mathlib.Topology.LimitSet
public import DynamicalSystems.Stability

@[expose] public section

section Antitone

variable {ι E : Type*}

namespace Filter

variable (Φ : ι → E → E)

/-- A set `s` is invariant under the (positive) flow if for all `x ∈ s` we have that `Φ t x ∈ s`. -/
def IsInvariantSetOn (s : Set E) (I : Set ι) : Prop :=
  ∀ x ∈ s, ∀ t ∈ I, Φ t x ∈ s

end Filter

section Semigroup

structure IsSemigroupOn [Add ι] [Zero ι] (Φ : ι → E → E) (s : Set E) : Prop where
  zero : ∀ x ∈ s, Φ 0 x = x
  add : ∀ t₀ t₁, ∀ x ∈ s, Φ (t₀ + t₁) x = Φ t₀ (Φ t₁ x)

structure IsSemigroup [Add ι] [Zero ι] (Φ : ι → E → E) : Prop where
  zero : ∀ x, Φ 0 x = x
  add : ∀ t₀ t₁ x, Φ (t₀ + t₁) x = Φ t₀ (Φ t₁ x)

variable {Φ : ι → E → E} {s : Set E} {y : E}

theorem IsSemigroupOn.mono [Add ι] [Zero ι] {s₁ s₂ : Set E} (hs : s₁ ⊆ s₂)
    (hs : IsSemigroupOn Φ s₂) : IsSemigroupOn Φ s₁ := by
  sorry

@[simp]
theorem isSemigroup_univ [Add ι] [Zero ι] : IsSemigroupOn Φ Set.univ ↔ IsSemigroup Φ := by
  sorry

theorem IsSemigroupOn.comm [AddCommMagma ι] [Zero ι] (hΦ : IsSemigroupOn Φ s) {x : E} (hx : x ∈ s)
    (t₀ t₁ : ι) :
    Φ t₀ (Φ t₁ x) = Φ t₁ (Φ t₀ x) := by
  rw [← hΦ.add t₀ t₁ x hx, ← hΦ.add t₁ t₀ x hx, add_comm]

variable [TopologicalSpace E] [AddCommMonoid ι] [Preorder ι] [IsDirectedOrder ι] [AddLeftMono ι]

open Filter

/-- The limit set is monotone in the flow parameter. -/
theorem limitSet_mono (hy : y ∈ s) (hΦ : IsSemigroupOn Φ s) {t : ι}
    (ht : 0 ≤ t) :
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
  · rwa [hΦ.add t' t y hy]

-- Todo: more general version

/-- If `Φ` is a semigroup and `Φ t` is continuous for every `t`, then the limit set is invariant. -/
theorem isInvariantSet_limitSet {y : E} {s : Set E} (hs' : atTop.limitSet (Φ · y) ⊆ s)
    (hΦ₁ : IsSemigroupOn Φ {y}) (hΦ₂ : ∀ t ∈ Set.Ici 0, ∀ x ∈ s, ContinuousAt (Φ t) x) :
    IsInvariantSetOn Φ (atTop.limitSet (Φ · y)) (Set.Ici 0) := by
  intro x hx t (ht : 0 ≤ t)
  have hx' : x ∈ s := hs' hx
  apply limitSet_mono (by rfl) hΦ₁ ht
  rw [mem_limitSet_iff] at *
  have : (fun s ↦ Φ t (Φ s y)) =ᶠ[Filter.atTop] fun s ↦ Φ s (Φ t y) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 0
    intro s hs
    apply IsSemigroupOn.comm hΦ₁ rfl
  exact (hx.tendsto_comp (hΦ₂ t ht x hx')).congrFun this


end Semigroup

section TopologicalSpace

open scoped Topology

variable [TopologicalSpace E]

structure IsLyapunovOn [Preorder ι] (v : E → ℝ) (Φ : ι → E → E) (s : Set E) : Prop where
  pos : ∀ x, 0 ≤ v x
  cont : Continuous v
  antitone : ∀ x t₀ t₁ (_ht₀ : Φ t₀ x ∈ s) (_ht₁ : Φ t₁ x ∈ s) (_ht : t₀ ≤ t₁),
    v (Φ t₁ x) ≤ v (Φ t₀ x)

structure IsLyapunov [Preorder ι] (v : E → ℝ) (Φ : ι → E → E) : Prop where
  pos : ∀ x, 0 ≤ v x
  antitone : ∀ x t₀ t₁ (_ht : t₀ ≤ t₁), v (Φ t₁ x) ≤ v (Φ t₀ x)
  cont : Continuous v

variable {Φ : ℝ → E → E} {v : E → ℝ} {x₀ : E} {s : Set E}

open Filter

/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto {x : E} {t₀ : ℝ} (h_lya : IsLyapunovOn v Φ s)
    (hx : ∀ t ∈ Set.Ici t₀, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone x t t' (hx t ht) (hx t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto_of_eventually {x : E} (h_lya : IsLyapunovOn v Φ s)
    (hx : ∀ᶠ t in atTop, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  rw [Filter.eventually_atTop] at hx
  obtain ⟨t₀, hx⟩ := hx
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone x t t' (hx t ht) (hx t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

/-- The sublevel sets of `v` are contained in neighborhoods of `x₀`. -/
theorem foo'' (h_cont : Continuous v) (hvx₀ : v x₀ = 0)
    {δ : ℝ} (hδ : 0 < δ) : { p | v p ≤ δ } ∈ 𝓝 x₀ := by
  have : {p | v p < δ } ⊆ interior {p | v p ≤ δ } :=
    lt_subset_interior_le h_cont continuous_const
  rw [← mem_interior_iff_mem_nhds]
  apply this
  simp [hvx₀, hδ]

variable [FirstCountableTopology E]

theorem foo' (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x) (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    ∃ δ > 0, {p | v p ≤ δ } ⊆ s := by
  by_contra!
  simp only [gt_iff_lt] at this
  simp_rw [Set.not_subset] at this
  choose r hδ using this
  simp only [Set.mem_setOf_eq] at hδ
  let a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have ha : ∀ n, 0 < a n := by intro; positivity
  have ha' : Filter.Tendsto a Filter.atTop (𝓝 0) := by
    rw [NormedAddCommGroup.tendsto_atTop]
    intro ε hε
    simp only [sub_zero, Real.norm_eq_abs]
    obtain ⟨N, hN₀, hN⟩ := Real.exists_nat_pos_inv_lt hε
    use N
    intro n hn
    grw [← hN]
    simp only [abs_inv, a]
    field_simp
    norm_cast
    grw [hn]
    simp
  let b : ℕ → E := fun n ↦ r (a n) (ha n)
  have hb₁ : ∀ n, v (b n) ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n
    exact (hδ (a n) (ha n)).1
  have hb₂ : ∀ n, b n ∉ s := by
    intro n
    exact (hδ (a n) (ha n)).2
  have hb₃ : ∃ᶠ n in Filter.atTop, b n ∈ { p | v p ≤ δ₀ } := by
    apply Filter.Eventually.frequently
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN₀, hN⟩ := Real.exists_nat_pos_inv_lt hδ₀
    use N
    intro n hn
    simp only [Set.mem_setOf_eq]
    grw [hb₁ n, ← hN, hn]
    field_simp
    simp
  obtain ⟨y, hy, k, hk, h⟩ := h_cpt.tendsto_subseq' hb₃
  have hb₁' : Filter.Tendsto (fun n ↦ v (b (k n))) Filter.atTop (𝓝 0) := by
    apply squeeze_zero _ _ ha'
    · intro n
      apply h_pos (b (k n))
    · intro n
      grw [hb₁]
      simp only [a]
      field_simp
      simpa using hk.le_apply
  have hy' : y = x₀ := by
    rw [← hvx₀]
    apply tendsto_nhds_unique (h_cont.tendsto y |>.comp h) hb₁'
  rw [hy'] at h
  obtain ⟨n₀, hn₀⟩ := h.eventually_mem hs |>.exists_forall_of_atTop
  exact hb₂ (k n₀) (hn₀ n₀ <| le_refl _)

/-- The sublevel sets of a Lyapunov function form a basis of the neighbourhood filter of `x₀`. -/
theorem hasBasis_setOf_le (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝 x₀).HasBasis (0 < ·) ({ p | v p ≤ · }) := by
  rw [hasBasis_iff]
  intro s
  constructor
  · intro hs
    apply foo' h_cont h_pos hvx₀ hs hδ₀ h_cpt
  · intro ⟨δ, hδ, h⟩
    exact mem_of_superset (foo'' h_cont (hvx₀ x₀ |>.mpr rfl) hδ) h

/-- Lyapunov stability for autonomous systems. -/
theorem IsLyapunov.isStableOn (h_lya : IsLyapunov v Φ) (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ 0 x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  apply (hasBasis_setOf_le h_lya.cont h_lya.pos hvx₀ hδ₀ h_cpt).isStableOn
  intro δ hδ
  use δ, hδ
  intro t (ht : 0 ≤ t) x (hx : v x ≤ δ)
  simp only [Set.mem_setOf_eq]
  grw [h_lya.antitone x 0 t ht, h_id x, hx]

/-- Lyapunov stability for autonomous systems. -/
theorem IsLyapunovOn.isStableOn (h_lya : IsLyapunovOn v Φ s) (h_cpt : IsCompact s)
    (hs : ∀ x ∈ s, ∀ t ∈ Set.Ici 0, Φ t x ∈ s)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ 0 x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  have h_cpt' : IsCompact { p | v p ≤ δ₀ } := by
    apply h_cpt.of_isClosed_subset _ h_subset
    refine isClosed_le h_lya.cont continuous_const
  apply (hasBasis_setOf_le h_lya.cont h_lya.pos hvx₀ hδ₀ h_cpt').isStableOn
  intro δ hδ
  use min δ δ₀, lt_min hδ hδ₀
  intro t (ht : 0 ≤ t) x (hx : v x ≤ min δ δ₀)
  have hx' : x ∈ s := by
    apply h_subset
    simp only [Set.mem_setOf_eq]
    grw [hx]
    exact Std.min_le_right
  simp only [Set.mem_setOf_eq]
  have hx0 : Φ 0 x ∈ s := hs _ hx' _ (by simp)
  have hxt : Φ t x ∈ s := hs _ hx' _ ht
  grw [h_lya.antitone x 0 t hx0 hxt ht, h_id x, hx]
  exact Std.min_le_left

end TopologicalSpace

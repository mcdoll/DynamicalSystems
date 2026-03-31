/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Topology.Antitone
public import DynamicalSystems.Stability
public import DynamicalSystems.Mathlib.Dynamics.Basic

@[expose] public section

variable {ι α E F : Type*}

section TopologicalSpace

open scoped Topology

section Definition

variable [TopologicalSpace E]
  [Preorder F] [Zero F] [TopologicalSpace F]

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow. -/
@[fun_prop]
structure IsLyapunovOn [Preorder ι] (v : E → F) (Φ : ι → E → E) (s : Set E) : Prop where
  pos : ∀ x, 0 ≤ v x
  cont : Continuous v
  antitone : ∀ ⦃x t₀ t₁⦄ (_ht₀ : Φ t₀ x ∈ s) (_ht₁ : Φ t₁ x ∈ s) (_ht : t₀ ≤ t₁),
    v (Φ t₁ x) ≤ v (Φ t₀ x)

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow. -/
@[fun_prop]
structure IsLyapunov [Preorder ι] (v : E → F) (Φ : ι → E → E) : Prop where
  pos : ∀ x, 0 ≤ v x
  cont : Continuous v
  antitone : ∀ ⦃x t₀ t₁⦄ (_ht : t₀ ≤ t₁), v (Φ t₁ x) ≤ v (Φ t₀ x)

end Definition

open Filter


variable {Φ : ι → E → E} {v : E → F} {x₀ : E} {s : Set E}

section blubb

variable [Preorder ι] [IsDirectedOrder ι] [TopologicalSpace E]

variable
  [Zero F] [TopologicalSpace F] [ConditionallyCompletePartialOrderInf F]
  [InfConvergenceClass F]


/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto {x : E} {t₀ : ι} (h_lya : IsLyapunovOn v Φ s)
    (hx : ∀ t ∈ Set.Ici t₀, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone (hx t ht) (hx t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

variable [Nonempty ι]

/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto_of_eventually {x : E} (h_lya : IsLyapunovOn v Φ s)
    (hx : ∀ᶠ t in atTop, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  rw [Filter.eventually_atTop] at hx
  obtain ⟨t₀, hx⟩ := hx
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone (hx t ht) (hx t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

variable {v : E → ℝ}

/-- The sublevel sets of `v` are contained in neighborhoods of `x₀`. -/
theorem setOf_fun_le_mem_nhds (h_cont : Continuous v) (hvx₀ : v x₀ = 0)
    {δ : ℝ} (hδ : 0 < δ) : { p | v p ≤ δ } ∈ 𝓝 x₀ := by
  have : {p | v p < δ } ⊆ interior {p | v p ≤ δ } :=
    lt_subset_interior_le h_cont continuous_const
  rw [← mem_interior_iff_mem_nhds]
  apply this
  simp [hvx₀, hδ]

variable [FirstCountableTopology E]

theorem exists_setOf_fun_le_subset (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
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
  have hb₃ : ∃ᶠ n in atTop, b n ∈ { p | v p ≤ δ₀ } := by
    apply Filter.Eventually.frequently
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN₀, hN⟩ := Real.exists_nat_pos_inv_lt hδ₀
    use N
    intro n hn
    simp only [Set.mem_setOf_eq]
    grw [hb₁ n, ← hN, hn]
    field_simp
    simp
  obtain ⟨y, _hy, k, hk, h⟩ := h_cpt.tendsto_subseq' hb₃
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
    apply exists_setOf_fun_le_subset h_cont h_pos hvx₀ hs hδ₀ h_cpt
  · intro ⟨δ, hδ, h⟩
    exact mem_of_superset (setOf_fun_le_mem_nhds h_cont (hvx₀ x₀ |>.mpr rfl) hδ) h

end blubb

variable [TopologicalSpace E] [Preorder ι] [Zero ι] [FirstCountableTopology E]

variable {v : E → ℝ}

/-- Lyapunov stability for time-independent Lyapunov functions. -/
theorem IsLyapunov.isStableOn (h_lya : IsLyapunov v Φ) (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ 0 x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  apply (hasBasis_setOf_le h_lya.cont h_lya.pos hvx₀ hδ₀ h_cpt).isStableOn
  intro δ hδ
  use δ, hδ
  intro t (ht : 0 ≤ t) x (hx : v x ≤ δ)
  simp only [Set.mem_setOf_eq]
  grw [h_lya.antitone ht, h_id x, hx]

/-- Lyapunov stability for time-independent Lyapunov functions. -/
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
  grw [h_lya.antitone hx0 hxt ht, h_id x, hx]
  exact Std.min_le_left

end TopologicalSpace

section Continuous

variable [NormedAddCommGroup E]

variable {f : E → E} {Φ : ℝ → E → E} {v : E → ℝ} (s : Set E)

theorem isLyapunov_of_deriv
    (hv : ∀ x, 0 ≤ v x)
    (h_cont : Continuous v) (h_diff : ∀ x, Differentiable ℝ (v <| Φ · x))
    (h_deriv : ∀ x, deriv (v <| Φ · x) ≤ 0) :
    IsLyapunov v Φ where
  pos := hv
  cont := h_cont
  antitone := fun x ↦ antitone_of_deriv_nonpos (h_diff x) (h_deriv x)

variable [NormedSpace ℝ E]

theorem Flow.isLyapunovOn_of_deriv (hf : IsFundamentalSolution Φ (fun _ ↦ f)) (hv : ∀ x, 0 ≤ v x)
    (h_cont : Continuous v) (h_deriv : sorry) :
    IsLyapunovOn v Φ s where
  pos := hv
  cont := h_cont
  antitone := by
    intro x t₀ t₁ ht₀ ht₁ ht
    have : AntitoneOn (v <| Φ · x) (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · sorry
      · sorry
      · sorry
    --specialize this t₀
    sorry

open scoped NNReal

variable {K : ℝ≥0}

theorem Flow.isLyapunov (hf : IsCompleteVectorField f) (hK : LipschitzWith K f) (hv : ∀ x, 0 ≤ v x)
    (hv_diff : Differentiable ℝ v) (h_deriv : ∀ x, fderiv ℝ v x (f x) ≤ 0) :
    IsLyapunov v (hf.flow hK) :=
  isLyapunov_of_deriv hv hv_diff.continuous ?_ ?_
where finally
  · intro x
    apply hv_diff.comp (hf.differentiable_flow hK _)
  · intro x t
    convert h_deriv (hf.flow hK t x)
    calc
      deriv (v <| hf.flow hK · x) t = (fderiv ℝ v (hf.flow hK t x)) (deriv (hf.flow hK · x) t) := by
        apply fderiv_comp_deriv _ (by fun_prop)
        apply hf.differentiable_flow
      _ = (fderiv ℝ v (hf.flow hK t x)) (f (hf.flow hK t x)) := by
        congr
        apply hf.deriv_flow hK t x

end Continuous

/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Basic.Autonomous
public import DynamicalSystems.Mathlib.Topology.Antitone
public import DynamicalSystems.Stability.Basic
public import DynamicalSystems.Mathlib.Analysis.Calculus.Flow
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Lyapunov functions and stability -/

@[expose] public section

variable {ι α E F : Type*}

section TopologicalSpace

open scoped Topology

section Definition

variable [TopologicalSpace E]
  [Preorder F] [Zero F] [TopologicalSpace F] [Preorder ι]

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow.

Note that we assume that `v` is non-negative and continuous everywhere, but only decreasing on
`s`. -/
@[fun_prop]
structure IsLyapunovOn (v : E → F) (Φ : ι → E → E) (s : Set E) : Prop where
  /-- A Lyapunov function is non-negative everywhere -/
  pos : ∀ x, 0 ≤ v x
  /-- A Lyapunov function is continuous everywhere -/
  cont : Continuous v
  /-- A Lyapunov function is monotonically decreasing along the flow for all values `t` such that
  `Φ t x` is contained in `s`. -/
  antitone : ∀ ⦃x t₀ t₁⦄ (_ht₀ : Φ t₀ x ∈ s) (_ht₁ : Φ t₁ x ∈ s) (_ht : t₀ ≤ t₁),
    v (Φ t₁ x) ≤ v (Φ t₀ x)

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow.

Note that we assume that `v` is non-negative and continuous everywhere, but only decreasing on
`s`. -/
@[fun_prop]
structure IsLyapunovOn' (v : E → F) (Φ : ι → E → E) (s : Set E) : Prop where
  /-- A Lyapunov function is non-negative everywhere -/
  pos : ∀ x, 0 ≤ v x
  /-- A Lyapunov function is continuous everywhere -/
  cont : Continuous v
  /-- A Lyapunov function is monotonically decreasing along the flow for all values `t` such that
  `Φ t x` is contained in `s`. -/
  antitone : ∀ ⦃x t₀ t₁⦄ (_hx : x ∈ s) (_ht₀ : Φ t₀ x ∈ s) (_ht₁ : Φ t₁ x ∈ s) (_ht : t₀ ≤ t₁),
    v (Φ t₁ x) ≤ v (Φ t₀ x)

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow.

Note that we assume that `v` is non-negative and continuous everywhere, but only decreasing on
`s`. -/
@[fun_prop]
structure IsLyapunovOnIn (v : E → F) (Φ : ι → E → E) (s : Set E) (s' : Set ι) : Prop where
  /-- A Lyapunov function is non-negative everywhere -/
  pos : ∀ x, 0 ≤ v x
  /-- A Lyapunov function is continuous everywhere -/
  cont : Continuous v
  /-- A Lyapunov function is monotonically decreasing along the flow for all values `t` such that
  `Φ t x` is contained in `s`. -/
  antitone : ∀ x ∈ s, ∀ t₀ ∈ s', ∀ t₁ ∈ s', t₀ ≤ t₁ → v (Φ t₁ x) ≤ v (Φ t₀ x)
  /-- the set `s` is invariant. -/
  mem : ∀ x ∈ s, ∀ t ∈ s', Φ t x ∈ s

/-- A Lyapunov function is a continuous non-negative function that is non-increasing with respect
to a given flow. -/
@[fun_prop]
structure IsLyapunov (v : E → F) (Φ : ι → E → E) : Prop where
  /-- A Lyapunov function is non-negative everywhere -/
  pos : ∀ x, 0 ≤ v x
  /-- A Lyapunov function is continuous everywhere -/
  cont : Continuous v
  /-- A Lyapunov function is monotonically decreasing along the flow. -/
  antitone : ∀ x ⦃t₀ t₁⦄, t₀ ≤ t₁ → v (Φ t₁ x) ≤ v (Φ t₀ x)

attribute [fun_prop] IsLyapunov.cont

variable {v : E → F} {Φ : ι → E → E} {s : Set E}

@[fun_prop]
theorem IsLyapunovOn.isLyapunovOn' (h : IsLyapunovOn v Φ s) : IsLyapunovOn' v Φ s where
  pos := h.pos
  cont := h.cont
  antitone _ _ _ _ ht₀ ht₁ ht := h.antitone ht₀ ht₁ ht

@[fun_prop]
theorem IsLyapunovOn.continuous (h : IsLyapunovOn v Φ s) : Continuous v := h.cont

@[fun_prop]
theorem IsLyapunovOn.continuousAt (h : IsLyapunovOn v Φ s) {x : E} : ContinuousAt v x :=
  h.cont.continuousAt

theorem IsLyapunov.isLyapunovOn' (h : IsLyapunov v Φ) (s : Set E) : IsLyapunovOn' v Φ s where
  pos := h.pos
  cont := h.cont
  antitone x _ _ _ _ _ ht := h.antitone x ht

theorem IsLyapunov.isLyapunovOn (h : IsLyapunov v Φ) (s : Set E) : IsLyapunovOn v Φ s where
  pos := h.pos
  cont := h.cont
  antitone x _ _ _ _ ht := h.antitone x ht

end Definition

open Filter


variable {Φ : ι → E → E} {v : E → F} {x₀ : E} {s : Set E} {t₀ : ι}

section IsInvariantOn

variable [Preorder ι] [TopologicalSpace E]
  [Zero F] [TopologicalSpace F] [PartialOrder F]

/-- If `v` is a global Lyapunov function and `s = {x | v x = 0}`, then `s` is invariant. -/
theorem IsLyapunov.isInvariantOn (h_lya : IsLyapunov v Φ) (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s)
    (h_id : ∀ x, Φ t₀ x = x) : s.IsInvariantOn Φ (Set.Ici t₀) := by
  intro t ht x hx
  simp_rw [← hvx₀] at hx ⊢
  rw [← h_id x] at hx
  apply le_antisymm _ (h_lya.pos (Φ t x))
  rw [← hx]
  exact h_lya.antitone x ht

end IsInvariantOn


section HasBasis

variable [Preorder ι] [IsDirectedOrder ι] [TopologicalSpace E]

variable
  [Zero F] [TopologicalSpace F] [ConditionallyCompletePartialOrderInf F]
  [InfConvergenceClass F]


/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto {x : E} {t₀ : ι} (h_lya : IsLyapunovOn v Φ s)
    (hΦ : ∀ t ∈ Set.Ici t₀, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone (hΦ t ht) (hΦ t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

variable [Nonempty ι]

/-- The flow composed with a Lyapunov function converges to some point. -/
theorem IsLyapunovOn.exists_tendsto_of_eventually {x : E} (h_lya : IsLyapunovOn v Φ s)
    (hΦ : ∀ᶠ t in atTop, Φ t x ∈ s) :
    ∃ c, Filter.Tendsto (v <| Φ · x) Filter.atTop (𝓝 c) := by
  rw [Filter.eventually_atTop] at hΦ
  obtain ⟨t₀, hΦ⟩ := hΦ
  have h_anti : AntitoneOn (v <| Φ · x) (Set.Ici t₀) := by
    intro t ht t' ht' h
    exact h_lya.antitone (hΦ t ht) (hΦ t' ht') h
  apply h_anti.exists_tendsto ⟨0, ?_⟩
  intro t ht
  exact h_lya.pos _

variable {v : E → ℝ}

variable {s s' : Set E}

theorem setOf_fun_le_mem_nhdsSet (h_cont : Continuous v) (hvs : ∀ x ∈ s, v x = 0)
    {δ : ℝ} (hδ : 0 < δ) : { p | v p ≤ δ } ∈ 𝓝ˢ s := by
  set s' := v ⁻¹' Set.Ioo (-δ) δ
  have hs' : IsOpen s' :=
    h_cont.isOpen_preimage _ isOpen_Ioo
  have hs'_subset : s' ⊆ { p | v p ≤ δ } := by
    intro x ⟨hx₁, hx₂⟩
    exact hx₂.le
  have hss' : s ⊆ s' := by
    intro x hx
    simp [s', hvs x hx, hδ]
  have hs'_nhdsSet : s' ∈ 𝓝ˢ s := by
    refine mem_nhdsSet_iff_exists.mpr ?_
    use s', hs'
  exact mem_of_superset hs'_nhdsSet hs'_subset

/-- The sublevel sets of `v` are contained in neighborhoods of `x₀`. -/
theorem setOf_fun_le_mem_nhds (h_cont : Continuous v) (hvx₀ : v x₀ = 0)
    {δ : ℝ} (hδ : 0 < δ) : { p | v p ≤ δ } ∈ 𝓝 x₀ := by
  simpa using setOf_fun_le_mem_nhdsSet (s := {x₀}) h_cont (by simp [hvx₀]) hδ

variable [FirstCountableTopology E]

theorem exists_setOf_fun_le_subset (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    {s : Set E} (hs : s ∈ 𝓝ˢ s') {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    ∃ δ > 0, {p | v p ≤ δ } ⊆ s := by
  by_contra!
  simp only [gt_iff_lt] at this
  simp_rw [Set.not_subset] at this
  choose r hδ using this
  simp only [Set.mem_ofPred_eq] at hδ
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
    simp only [Set.mem_ofPred_eq]
    grw [hb₁ n, ← hN, hn]
    field_simp [lt_of_lt_of_le hN₀ hn]
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
  have hy' : y ∈ s' := by
    rw [← hvx₀]
    apply tendsto_nhds_unique (h_cont.tendsto y |>.comp h) hb₁'
  have h := tendsto_nhdsSet_of_tendsto_nhds hy' h
  obtain ⟨n₀, hn₀⟩ := h.eventually_mem hs |>.exists_forall_of_atTop
  exact hb₂ (k n₀) (hn₀ n₀ <| le_refl _)

theorem exists_setOf_fun_le_subset' (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    ∃ δ > 0, {p | v p ≤ δ } ⊆ s :=
  exists_setOf_fun_le_subset (s' := {x₀}) h_cont h_pos (by simp [hvx₀]) (by simp [hs]) hδ₀ h_cpt

/-- The sublevel sets of a Lyapunov function form a basis of the neighbourhood filter of `s'`. -/
theorem hasBasis_nhdsSet_setOf_le (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝ˢ s').HasBasis (0 < ·) ({ p | v p ≤ · }) := by
  rw [hasBasis_iff]
  intro s
  constructor
  · intro hs
    apply exists_setOf_fun_le_subset h_cont h_pos hvx₀ hs hδ₀ h_cpt
  · intro ⟨δ, hδ, h⟩
    exact mem_of_superset (setOf_fun_le_mem_nhdsSet h_cont (fun x hx ↦ (hvx₀ x).mpr hx) hδ) h

/-- The sublevel sets of a Lyapunov function form a basis of the neighbourhood filter of `x₀`. -/
theorem hasBasis_setOf_le (h_cont : Continuous v) (h_pos : ∀ x, 0 ≤ v x)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝 x₀).HasBasis (0 < ·) ({ p | v p ≤ · }) := by
  simpa using hasBasis_nhdsSet_setOf_le (s' := {x₀}) h_cont h_pos (by simp [hvx₀]) hδ₀ h_cpt

end HasBasis

variable [TopologicalSpace E]

variable {v : E → ℝ} {t₀ : ι}

variable {s' : Set E} {x : E}

section ContinuityMethod

variable [ConditionallyCompleteLinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [DenselyOrdered ι]

variable [TopologicalSpace α]

theorem continuity_method {γ : ι → α} {p : Set α} {s : Set α} (hs : IsOpen s)
    (hγ : Continuous γ)
    (ht₀ : γ t₀ ∈ p) (ht₀' : γ t₀ ∈ s) (h_closed : IsClosed (s ∩ p))
    (h : ∀ t ∈ Set.Ici t₀, (∀ t' ∈ Set.Icc t₀ t, γ t' ∈ s) → γ t ∈ p)
    {t : ι} (ht : t₀ ≤ t) :
    γ t ∈ s ∩ p := by
  -- Assume there exists `t ≥ t₀` such that `γ t ∉ s ∩ p
  by_contra hgoal
  set B : Set ι := {u | u ∈ Set.Icc t₀ t ∧ γ u ∉ s ∩ p} with hB
  have htB : t ∈ B := by grind
  have hBne : B.Nonempty := Set.nonempty_of_mem htB
  have hbdd : BddBelow B := ⟨t₀, fun _ _ ↦ by grind⟩
  -- Let `τ` denote the inf of all `t` such that `γ t ∉ s ∩ p`
  set τ := sInf B with hτdef
  have hτ0 : t₀ ≤ τ := by grind [le_csInf]
  have hτt : τ ≤ t := by grind [csInf_le]
  -- forall `t ≤ τ` we have that `γ t ∈ s ∩ p`
  have hbelow : ∀ t ∈ Set.Ico t₀ τ, γ t ∈ s ∩ p := by
    intro t ⟨ht₁, ht₂⟩
    by_contra hc
    have htB : t ∈ B := by grind
    grind [csInf_le hbdd htB]
  -- at time `τ` the path is still in `s ∩ p`, by closedness
  have hKτ : γ τ ∈ s ∩ p := by
    rcases eq_or_lt_of_le hτ0 with heq | hlt
    · grind
    · have hclosed : IsClosed (γ ⁻¹' (s ∩ p)) := h_closed.preimage hγ
      have hsub : Set.Ico t₀ τ ⊆ γ ⁻¹' (s ∩ p) := hbelow
      have hmem : τ ∈ closure (Set.Ico t₀ τ) := by grind [closure_Ico, ne_of_lt]
      grind [hclosed.closure_eq, closure_mono hsub hmem]
  have hsτ : ∀ t ∈ Set.Icc t₀ τ, γ t ∈ s := by grind
  have hBgt : ∀ t ∈ B, τ < t := by grind
  -- `t₁` satisfies `τ < t₁` and `Set.Ico τ t₁ ⊆ γ ⁻¹' s`
  obtain ⟨t₁, ht₁, ht₁'⟩ := exists_Ico_subset_of_mem_nhds (hs.preimage hγ |>.mem_nhds hKτ.1)
    ⟨t, hBgt t htB⟩
  -- `τ₁` satisfies `τ₁ ∈ B` and `τ₁ < t₁`
  obtain ⟨τ₁, hτ₁B, hτ₁'⟩ := exists_lt_of_csInf_lt hBne ht₁
  have : ∀ t' ∈ Set.Icc t₀ τ₁, γ t' ∈ s := by
    intro t' ⟨ht'₁, ht'₂⟩
    rcases le_or_gt t' τ with hle | hgt
    · grind
    · exact ht₁' ⟨hgt.le, lt_of_le_of_lt ht'₂ hτ₁'⟩
  grind

theorem continuity_method' {γ : ι → α} {p : Set α} {s : Set α} (hs : IsOpen s) (hp : IsClosed p)
    (hsp : p ⊆ s) (hγ : Continuous γ) (ht₀ : γ t₀ ∈ p)
    (h : ∀ t ∈ Set.Ici t₀, (∀ t' ∈ Set.Icc t₀ t, γ t' ∈ s) → γ t ∈ p)
    {t : ι} (ht : t₀ ≤ t) :
    γ t ∈ p := by
  suffices γ t ∈ s ∩ p from Set.mem_of_mem_inter_right this
  refine continuity_method hs hγ ht₀ (hsp ht₀) ?_ h ht
  convert hp
  simp [hsp]

theorem IsLyapunovOn.isInvariantOn {δ : ℝ} (h_lya : IsLyapunovOn v Φ s) (hs : IsOpen s)
    (hΦ' : ∀ x, Continuous (Φ · x))
    (hv : IsClosed {p | v p ≤ δ ∧ p ∈ s}) (h_id : ∀ x, Φ t₀ x = x) :
    {p | v p ≤ δ ∧ p ∈ s}.IsInvariantOn Φ (Set.Ici t₀) := by
  rw [Set.isInvariantOn_iff]
  intro x ⟨hx₁, hx₂⟩ t (ht : t₀ ≤ t)
  simp only [Set.mem_ofPred_eq]
  rw [and_comm]
  have ht₀ : v (Φ t₀ x) ≤ δ := by rwa [h_id]
  have ht₀' : Φ t₀ x ∈ s := by rwa [h_id]
  have h_closed : IsClosed (s ∩ {x | v x ≤ δ}) := by
    convert hv
    ext; simp [and_comm]
  refine continuity_method hs (hΦ' x) ht₀ ht₀' h_closed ?_ ht
  intro t (ht : t₀ ≤ t) h
  have := @h_lya.antitone x t₀ t ht₀' (h t (by simp [ht])) ht
  simp only [Set.mem_ofPred_eq, ge_iff_le]
  grw [this, ht₀]

end ContinuityMethod

variable [Preorder ι] [FirstCountableTopology E]

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of subsets and local Lyapunov functions. -/
theorem IsLyapunovOn'.isStableOn_nhdsSet (h_lya : IsLyapunovOn' v Φ s) (h_cpt : IsCompact s)
    (hs : ∀ x ∈ s, ∀ t ∈ Set.Ici t₀, Φ t x ∈ s)
    (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝ˢ s').IsStableOn Φ (Set.Ici t₀) := by
  have h_cpt' : IsCompact { p | v p ≤ δ₀ } := by
    apply h_cpt.of_isClosed_subset _ h_subset
    refine isClosed_le h_lya.cont continuous_const
  apply (hasBasis_nhdsSet_setOf_le h_lya.cont h_lya.pos hvx₀ hδ₀ h_cpt').isStableOn
  intro δ hδ
  use min δ δ₀, lt_min hδ hδ₀
  intro t (ht : t₀ ≤ t) x (hx : v x ≤ min δ δ₀)
  have hx' : x ∈ s := by
    apply h_subset
    simp only [Set.mem_ofPred_eq]
    grw [hx]
    exact Std.min_le_right
  simp only [Set.mem_ofPred_eq]
  have hx0 : Φ t₀ x ∈ s := hs _ hx' _ (by simp)
  have hxt : Φ t x ∈ s := hs _ hx' _ ht
  grw [h_lya.antitone hx' hx0 hxt ht, h_id x, hx]
  exact Std.min_le_left

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of points and local Lyapunov functions. -/
theorem IsLyapunovOn'.isStableOn_nhds (h_lya : IsLyapunovOn' v Φ s) (h_cpt : IsCompact s)
    (hs : ∀ x ∈ s, ∀ t ∈ Set.Ici t₀, Φ t x ∈ s)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici t₀) := by
  simpa using h_lya.isStableOn_nhdsSet (s' := {x₀}) h_cpt hs (by simp [hvx₀]) h_id hδ₀ h_subset

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of subsets and local Lyapunov functions. -/
theorem IsLyapunovOn.isStableOn_nhdsSet (h_lya : IsLyapunovOn v Φ s) (h_cpt : IsCompact s)
    (hs : ∀ x ∈ s, ∀ t ∈ Set.Ici t₀, Φ t x ∈ s)
    (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝ˢ s').IsStableOn Φ (Set.Ici t₀) :=
  h_lya.isLyapunovOn'.isStableOn_nhdsSet h_cpt hs hvx₀ h_id hδ₀ h_subset

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of points and local Lyapunov functions. -/
theorem IsLyapunovOn.isStableOn_nhds (h_lya : IsLyapunovOn v Φ s) (h_cpt : IsCompact s)
    (hs : ∀ x ∈ s, ∀ t ∈ Set.Ici t₀, Φ t x ∈ s)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici t₀) := by
  simpa using h_lya.isStableOn_nhdsSet (s' := {x₀}) h_cpt hs (by simp [hvx₀]) h_id hδ₀ h_subset

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of subsets and local Lyapunov functions. -/
theorem IsLyapunovOnIn.isStableOn_nhdsSet (h_lya : IsLyapunovOnIn v Φ s (Set.Ici t₀))
    (h_cpt : IsCompact s) (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝ˢ s').IsStableOn Φ (Set.Ici t₀) := by
  have h_cpt' : IsCompact { p | v p ≤ δ₀ } := by
    apply h_cpt.of_isClosed_subset _ h_subset
    refine isClosed_le h_lya.cont continuous_const
  apply (hasBasis_nhdsSet_setOf_le h_lya.cont h_lya.pos hvx₀ hδ₀ h_cpt').isStableOn
  intro δ hδ
  use min δ δ₀, lt_min hδ hδ₀
  intro t (ht : t₀ ≤ t) x (hx : v x ≤ min δ δ₀)
  have hx' : x ∈ s := by
    apply h_subset
    simp only [Set.mem_ofPred_eq]
    grw [hx]
    exact Std.min_le_right
  simp only [Set.mem_ofPred_eq]
  grw [h_lya.antitone x hx' t₀ (by simp) t (by simp [ht]) ht, h_id x, hx]
  exact Std.min_le_left

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of points and local Lyapunov functions. -/
theorem IsLyapunovOnIn.isStableOn_nhds (h_lya : IsLyapunovOnIn v Φ s (Set.Ici t₀))
    (h_cpt : IsCompact s)
    (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_subset : { p | v p ≤ δ₀ } ⊆ s) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici t₀) := by
  simpa using h_lya.isStableOn_nhdsSet (s' := {x₀}) h_cpt (by simp [hvx₀]) h_id hδ₀ h_subset

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of a point and global Lyapunov functions. -/
theorem IsLyapunov.isStableOn_nhdsSet (h_lya : IsLyapunov v Φ) (hvx₀ : ∀ x, v x = 0 ↔ x ∈ s')
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝ˢ s').IsStableOn Φ (Set.Ici t₀) := by
  refine (h_lya.isLyapunovOn' { p | v p ≤ δ₀ }).isStableOn_nhdsSet h_cpt ?_ hvx₀ h_id hδ₀
    (le_refl _)
  intro x (hx : v x ≤ δ₀) t (ht : t₀ ≤ t)
  simp only [Set.mem_ofPred_eq]
  grw [h_lya.antitone x ht, h_id x, hx]

/-- Lyapunov stability for time-independent Lyapunov functions.

Version for stability of a point and global Lyapunov functions. -/
theorem IsLyapunov.isStableOn_nhds (h_lya : IsLyapunov v Φ) (hvx₀ : ∀ x, v x = 0 ↔ x = x₀)
    (h_id : ∀ x, Φ t₀ x = x) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | v p ≤ δ₀ }) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici t₀) := by
  refine (h_lya.isLyapunovOn' { p | v p ≤ δ₀ }).isStableOn_nhds h_cpt ?_ hvx₀ h_id hδ₀ (le_refl _)
  intro x (hx : v x ≤ δ₀) t (ht : t₀ ≤ t)
  simp only [Set.mem_ofPred_eq]
  grw [h_lya.antitone x ht, h_id x, hx]

end TopologicalSpace

section Continuous

variable [NormedAddCommGroup E]

variable {f : E → E} {Φ : ℝ → E → E} {v : E → ℝ} {s : Set E}

/-- A non-negative differentiable function with decreasing derivative along the flow is a Lyapunov
function for that flow. -/
theorem isLyapunov_of_deriv
    (hv : ∀ x, 0 ≤ v x)
    (h_cont : Continuous v) (h_diff : ∀ x, Differentiable ℝ (v <| Φ · x))
    (h_deriv : ∀ x, deriv (v <| Φ · x) ≤ 0) :
    IsLyapunov v Φ where
  pos := hv
  cont := h_cont
  antitone := fun x ↦ antitone_of_deriv_nonpos (h_diff x) (h_deriv x)

theorem isLyapunovOn'_of_deriv
    (hv : ∀ x, 0 ≤ v x)
    (hv_cont : Continuous v) (h_diff : ∀ x, Differentiable ℝ (v <| Φ · x))
    (h_deriv : ∀ x ∈ s, deriv (v <| Φ · x) ≤ 0) :
    IsLyapunovOn' v Φ s where
  pos := hv
  cont := hv_cont
  antitone := by
    intro x t₀ t₁ hx ht₀ ht₁ ht
    have : Antitone (v <| Φ · x) := by
      apply antitone_of_deriv_nonpos (h_diff x)
      intro t
      apply h_deriv x hx
    exact this ht

theorem isLyapunovOnIn_of_deriv {δ₀ : ℝ} (hΦ : ∀ x, Φ 0 x = x)
    (hv : ∀ x, 0 ≤ v x)
    (hv_cont : Continuous v) (h_diff : ∀ x, Differentiable ℝ (v <| Φ · x))
    (h_deriv : ∀ x, v x ≤ δ₀ → deriv (v <| Φ · x) ≤ 0) :
    IsLyapunovOnIn v Φ { p | v p ≤ δ₀ } (Set.Ici 0) where
  pos := hv
  cont := hv_cont
  antitone := by
    intro x hx t₀ ht₀ t₁ ht₁ ht
    have : AntitoneOn (v <| Φ · x) (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (h_diff x).continuous.continuousOn
        (h_diff x).differentiableOn
      intro t ht'
      apply h_deriv x hx
    exact this ht₀ ht₁ ht
  mem x hx t ht := by
    have : Antitone (v <| Φ · x) := by
      apply antitone_of_deriv_nonpos (h_diff x)
      intro t
      apply h_deriv x hx
    simp only [Set.mem_ofPred_eq, ge_iff_le] at ⊢ hx
    grw [← hx]
    nth_rewrite 2 [← hΦ x]
    exact this ht

variable [NormedSpace ℝ E]

namespace AutonomousFlow

variable {Φ : AutonomousFlow ℝ E}

private theorem mem_of_fderiv {δ₀ : ℝ}
    (hs : IsOpen s) (hsδ : { p | v p ≤ δ₀ } ⊆ s)
    (hv_diff : Differentiable ℝ v) (hΦ_diff : ∀ x, Differentiable ℝ (Φ · x))
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0)
    {x : E} (hx₁ : v x ≤ δ₀) {t : ℝ} (ht : 0 ≤ t) :
    v (Φ t x) ≤ δ₀ := by
  have hp_closed : IsClosed { p | v p ≤ δ₀ } := isClosed_le hv_diff.continuous (by fun_prop)
  have hΦ0 : Φ 0 x ∈ { p | v p ≤ δ₀} := by simpa
  apply continuity_method' hs hp_closed hsδ (hΦ_diff x).continuous hΦ0 _ ht
  intro t₀ ht₀ ht₀'
  suffices AntitoneOn (v <| Φ · x) (Set.Icc 0 t₀) by
    simp only [Set.mem_ofPred_eq, ge_iff_le] at hΦ0 ⊢
    grw [← hΦ0]
    exact this (by grind) (by grind) (by grind)
  have h_diff : ∀ x, Differentiable ℝ (v <| Φ · x) := by intro; fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t₀) (h_diff x).continuous.continuousOn
    (h_diff x).differentiableOn
  intro t' ht'
  rw [AutonomousFlow.deriv_comp_flow hv_diff hΦ_diff]
  grind [interior_Icc]

theorem isInvariantOn_of_fderiv {δ₀ : ℝ} (hs : IsOpen s) (hsδ : { p | v p ≤ δ₀ } ⊆ s)
    (hv_diff : Differentiable ℝ v) (hΦ_diff : ∀ x, Differentiable ℝ (Φ · x))
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0) :
    {x | v x ≤ δ₀}.IsInvariantOn Φ (Set.Ici 0) := by
  intro t ht x hx
  exact mem_of_fderiv hs hsδ hv_diff hΦ_diff h_deriv hx ht

theorem isLyapunovOnIn_of_fderiv {δ₀ : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hs : IsOpen s) (hsδ : { p | v p ≤ δ₀ } ⊆ s)
    (hv_diff : Differentiable ℝ v) (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0) :
    IsLyapunovOnIn v Φ { p | v p ≤ δ₀ } (Set.Ici 0) where
  pos := hv
  cont := hv_diff.continuous
  antitone := by
    intro x (hx : v x ≤ δ₀) t₀ ht₀ t₁ ht₁ ht
    have h_diff : ∀ x, Differentiable ℝ (v <| Φ · x) := by intro; fun_prop
    suffices AntitoneOn (v <| Φ · x) (Set.Ici 0) from this ht₀ ht₁ ht
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) (h_diff x).continuous.continuousOn
      (h_diff x).differentiableOn
    intro t ht'
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht'
    rw [AutonomousFlow.deriv_comp_flow hv_diff hΦ]
    apply h_deriv
    apply hsδ
    exact mem_of_fderiv hs hsδ hv_diff hΦ h_deriv hx ht'.le
  mem x (hx : v x ≤ δ₀) t (ht : 0 ≤ t) :=
    mem_of_fderiv hs hsδ hv_diff hΦ h_deriv hx ht

theorem isLyapunovOn' (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (hv : ∀ x, 0 ≤ v x)
    (hv_diff : Differentiable ℝ v)
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0)
    (hΦs : ∀ x ∈ s, ∀ t, Φ t x ∈ s) :
    IsLyapunovOn' v Φ s := by
  apply isLyapunovOn'_of_deriv hv hv_diff.continuous (fun _ ↦ by fun_prop)
  intro x hx t
  rw [AutonomousFlow.deriv_comp_flow hv_diff hΦ]
  exact h_deriv (Φ t x) (hΦs x hx t)

theorem isLyapunov (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (hv : ∀ x, 0 ≤ v x) (hv_diff : Differentiable ℝ v)
    (h_deriv : ∀ x, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0) :
    IsLyapunov v Φ := by
  apply isLyapunov_of_deriv hv hv_diff.continuous (fun _ ↦ by fun_prop)
  intro x t
  rw [AutonomousFlow.deriv_comp_flow hv_diff hΦ]
  exact h_deriv (Φ t x)

end AutonomousFlow

namespace Flow

variable {Φ : Flow ℝ E}

theorem isLyapunovOnIn_of_fderiv {δ₀ : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hs : IsOpen s) (hsδ : { p | v p ≤ δ₀ } ⊆ s)
    (hv_diff : Differentiable ℝ v) (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0) :
    IsLyapunovOnIn v Φ { p | v p ≤ δ₀ } (Set.Ici 0) := by
  have hΦ : ∀ x, Differentiable ℝ (Φ.toAutonomousFlow · x) := by simpa
  have h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ.toAutonomousFlow · x) 0) ≤ 0 := by simpa
  simpa using AutonomousFlow.isLyapunovOnIn_of_fderiv hv hs hsδ hv_diff hΦ h_deriv

theorem isLyapunovOn' (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (hv : ∀ x, 0 ≤ v x)
    (hv_diff : Differentiable ℝ v)
    (h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0)
    (hΦs : ∀ x ∈ s, ∀ t, Φ t x ∈ s) :
    IsLyapunovOn' v Φ s := by
  have hΦ : ∀ x, Differentiable ℝ (Φ.toAutonomousFlow · x) := by simpa
  have h_deriv : ∀ x ∈ s, fderiv ℝ v x (deriv (Φ.toAutonomousFlow · x) 0) ≤ 0 := by simpa
  have hΦs : ∀ x ∈ s, ∀ t, Φ.toAutonomousFlow t x ∈ s := by simpa
  simpa using AutonomousFlow.isLyapunovOn' hΦ hv hv_diff h_deriv hΦs

theorem isLyapunov (hΦ : ∀ x, Differentiable ℝ (Φ · x))
    (hv : ∀ x, 0 ≤ v x) (hv_diff : Differentiable ℝ v)
    (h_deriv : ∀ x, fderiv ℝ v x (deriv (Φ · x) 0) ≤ 0) :
    IsLyapunov v Φ := by
  have hΦ : ∀ x, Differentiable ℝ (Φ.toAutonomousFlow · x) := by simpa
  have h_deriv : ∀ x, fderiv ℝ v x (deriv (Φ.toAutonomousFlow · x) 0) ≤ 0 := by simpa
  simpa using AutonomousFlow.isLyapunov hΦ hv hv_diff h_deriv

end Flow

open scoped NNReal

end Continuous

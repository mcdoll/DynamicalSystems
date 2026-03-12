/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution

/-! # LaSalle's invariance principle -/


/-

La Salle:

Proposition 5.20
- Filter.TotallyBounded.isCompact_setOf_clusterPt
- IsCompact.exists_mapClusterPt_of_frequently
- IsCompact.tendsto_subseq'

Lemma: Trajectories are continuous in initial data (maybe just as an assumption - the Coq proof does
that)

Proposition 5.21
- previous lemma and 5.20

La Salle (5.22)
- Product rule, negative derivative implies non-increasing (seems missing,
  `Mathlib.Analysis.Calculus.DerivativeTest` almost gets there)
- monotone bounded sequences converge: `Mathlib.Topology.Order.MonotoneConvergence`


-/

@[expose] public noncomputable section

open scoped NNReal Topology

variable {E E' F : Type*}

section Semigroup

variable (Φ : ℝ≥0 → E → E) (s : Set E)

def IsSemigroupOn : Prop :=
  ∀ t t' {x} (_hx : x ∈ s), Φ t (Φ t' x) = Φ (t + t') x

def IsSemigroup : Prop :=
  ∀ t t' x, Φ t (Φ t' x) = Φ (t + t') x

variable {Φ s}

@[simp]
theorem isSemigroup_univ : IsSemigroupOn Φ Set.univ ↔ IsSemigroup Φ := by
  simp [IsSemigroup, IsSemigroupOn]

theorem IsSemigroupOn.mono {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) (hs₂ : IsSemigroupOn Φ s₂) :
    IsSemigroupOn Φ s₁ := by
  sorry

theorem IsSemigroupOn.comm (hs : IsSemigroupOn Φ s) {x : E} (hx : x ∈ s) (t t' : ℝ≥0) :
    Φ t (Φ t' x) = Φ t' (Φ t x) := by
  rw [hs t t' hx, hs t' t hx, add_comm]

theorem IsSemigroup.comm (hs : IsSemigroup Φ) (x : E) (t t' : ℝ≥0) :
    Φ t (Φ t' x) = Φ t' (Φ t x) := by
  rw [hs t t' x, hs t' t x, add_comm]

end Semigroup

section TopologicalSpace

variable [TopologicalSpace E]

variable (Φ : ℝ≥0 → E → E) (y : E)

/-- The limit set is the collection of all cluster points. -/
def limitSet : Set E := { p | MapClusterPt p Filter.atTop (Φ · y) }

/-- A set `s` is invariant under the (positive) flow if for all `x ∈ s` we have that `Φ t x ∈ s`. -/
def IsInvariantSet (s : Set E) : Prop :=
  ∀ x t, x ∈ s → Φ t x ∈ s

variable {Φ y}

theorem mem_limitSet_iff {x : E} : x ∈ limitSet Φ y ↔ MapClusterPt x Filter.atTop (Φ · y) := by
  simp [limitSet]

-- Todo: mem_limitSet_iff_exists_extraction


theorem nonempty_limitSet {K : Set E} (hK : IsCompact K)
    (h : ∃ᶠ (x : ℝ≥0) in Filter.atTop, Φ x y ∈ K) : ∃ x ∈ K, x ∈ (limitSet Φ y) := by
  apply hK.exists_mapClusterPt_of_frequently h

/-- The limit set is monotone in the flow parameter. -/
theorem limitSet_mono {s : Set E} (hy : y ∈ s) (hΦ₁ : IsSemigroupOn Φ s) (t : ℝ≥0) :
    limitSet Φ (Φ t y) ⊆ limitSet Φ y := by
  intro x hx
  rw [mem_limitSet_iff, mapClusterPt_iff_frequently] at *
  simp only [Filter.frequently_atTop'] at *
  intro t' ht' t₀
  obtain ⟨t', ht', h⟩ := hx t' ht' t₀
  use t' + t
  constructor
  · exact lt_add_of_lt_of_nonneg ht' t.2
  · rwa [← hΦ₁ t' t hy]

/-- If `Φ` is a semigroup and `Φ t` is continuous for every `t`, then the limit set is invariant. -/
theorem isInvariantSet_limitSet {s₁ s₂ : Set E} (hy : y ∈ s₁) (hs : limitSet Φ y ⊆ interior s₂)
    (hΦ₁ : IsSemigroupOn Φ s₁) (hΦ₂ : ∀ t, ContinuousOn (Φ t) s₂) :
    IsInvariantSet Φ (limitSet Φ y) := by
  intro x t hx
  have hx' : s₂ ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hs hx)
  apply limitSet_mono hy hΦ₁ t
  rw [mem_limitSet_iff] at *
  have : (fun s ↦ Φ t (Φ s y)) =ᶠ[Filter.atTop] fun s ↦ Φ s (Φ t y) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 0
    intro s hs
    apply IsSemigroupOn.comm hΦ₁ hy
  apply MapClusterPt.congrFun this
  exact hx.tendsto_comp ((hΦ₂ t).continuousAt hx')

/-- If `Φ` is a semigroup and `Φ t` is continuous for every `t`, then the limit set is invariant. -/
theorem isInvariantSet_limitSet' {s : Set E} (hs : limitSet Φ y ⊆ interior s)
    (hΦ₁ : IsSemigroupOn Φ {y}) (hΦ₂ : ∀ t, ContinuousOn (Φ t) s) :
    IsInvariantSet Φ (limitSet Φ y) := by
  intro x t hx
  have hx' : s ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (hs hx)
  apply limitSet_mono (by rfl) hΦ₁ t
  rw [mem_limitSet_iff] at *
  have : (fun s ↦ Φ t (Φ s y)) =ᶠ[Filter.atTop] fun s ↦ Φ s (Φ t y) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 0
    intro s hs
    apply IsSemigroupOn.comm hΦ₁ rfl
  apply MapClusterPt.congrFun this
  exact hx.tendsto_comp ((hΦ₂ t).continuousAt hx')

theorem thm520 : Filter.Tendsto (Φ · y) Filter.atTop (𝓝ˢ (limitSet Φ y)) := by
  unfold Filter.Tendsto
  -- probably needs a bit of development of limits to sets
  sorry

variable {v : E → ℝ}

/-- If `v (Φ t y)` converges to `c`, then `v x = c` for all limit points `x`. -/
theorem blubb' {c : ℝ} (h_tendsto : Filter.Tendsto (fun t ↦ v (Φ t y)) Filter.atTop (𝓝 c)) {x : E}
    (hx : x ∈ limitSet (Φ ·) y) (hvx : ContinuousAt v x) : v x = c := by
  -- this is some fairly basic result about composition of limits
  rw [mem_limitSet_iff] at hx
  have : MapClusterPt (v x) Filter.atTop fun t ↦ v (Φ t y) := by
    apply MapClusterPt.continuousAt_comp
    · apply hvx
    apply hx.of_comp
    -- this should be trivial (and its own lemma)
    refine Filter.tendsto_atTop_atTop_of_monotone (fun ⦃a b⦄ le ↦ le) ?_
    intro t
    use Real.toNNReal t
    simp
  -- the rest should be its own lemma
  rw [mapClusterPt_iff_ultrafilter] at this
  obtain ⟨U, hU, h⟩ := this
  apply tendsto_nhds_unique h (h_tendsto.mono_left hU)

end TopologicalSpace

section UniformSpace

variable [UniformSpace E] [CompleteSpace E]

variable {Φ : ℝ≥0 → E → E} {y : E}

theorem isCompact_limitSet' (hf : TotallyBounded (Set.range (Φ · y))) :
    IsCompact (limitSet Φ y) := by
  apply Filter.TotallyBounded.isCompact_setOf_clusterPt
  rw [← Filter.totallyBounded_principal_iff] at hf
  apply hf.mono
  intro s hs
  simp only [Filter.mem_principal] at hs
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  use 0
  intro t ht
  apply hs
  simp

/-- If the flow is contained in a compact set, then the limit set is compact. -/
theorem isCompact_limitSet {s : Set E} (hs : IsCompact s) (hf : ∀ t, Φ t y ∈ s) :
    IsCompact (limitSet Φ y) := by
  apply isCompact_limitSet'
  apply hs.totallyBounded.subset
  intro x ⟨t, (h : Φ t y = x)⟩
  rw [← h]
  exact hf t

end UniformSpace

section DynSys

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {f : E → E} (Φ : ℝ → E → E) (y : E) (f' : E) (t₀ : ℝ)

variable {v : E → ℝ}

theorem flow_deriv {x f' : E} (hv : DifferentiableAt ℝ v (Φ t₀ x)) (hΦ : HasDerivAt (Φ · x) f' t₀) :
    deriv (fun t ↦ v (Φ t x)) t₀ = fderiv ℝ v (Φ t₀ x) f' := calc
  _ = (fderiv ℝ v (Φ t₀ x)) (deriv (Φ · x) t₀) := fderiv_comp_deriv _ hv hΦ.differentiableAt
  _ = _ := by rw [hΦ.deriv]

/-- If a function `v` is constant on an invariant set, then `fderiv ℝ v x (f x)` vanishes for all
`x ∈ s`.

This is an easy consequence of the chain rule, but with the twist that we can only calculate
one-sided derivatives. -/
theorem blubb {x : E} (hv : DifferentiableAt ℝ v x) {s : Set E} (hx : x ∈ s)
    (hs : IsInvariantSet (Φ ·) s) (c : ℝ) (hsv : ∀ x ∈ s, v x = c) (hΦ : HasDerivAt (Φ · x) (f x) 0)
    (hΦ0 : Φ 0 x = x) :
    fderiv ℝ v x (f x) = 0 := calc
  fderiv ℝ v x (f x) = deriv (fun t ↦ v (Φ t x)) 0 := by
    -- Chain rule
    rw [Eq.comm]
    rw [flow_deriv (f' := f x)]
    · congr
    · rw [hΦ0]
      apply hv
    · exact hΦ
  _ = derivWithin (fun t ↦ v (Φ t x)) {t | 0 ≤ t} 0 := by
    -- If a function is differentiable, then it suffices to calculate a one-sided limit
    refine (DifferentiableAt.derivWithin ?_ (uniqueDiffWithinAt_Ici _)).symm
    -- need that `Φ` is differentiable
    apply DifferentiableAt.comp
    · rw [hΦ0]
      apply hv
    · exact hΦ.differentiableAt
  _ = derivWithin (fun (t : ℝ) ↦ c) {t | 0 ≤ t} 0 := by
    -- the function is constant for `t ≥ 0`
    apply derivWithin_congr
    · intro t (ht : 0 ≤ t)
      apply hsv
      exact hs x ⟨t, ht⟩ hx
    · apply hsv
      exact hs x 0 hx
  _ = 0 := by
    -- a constant function has vanishing derivative
    rw [derivWithin_fun_const, Pi.zero_apply]

/-- The limit set is contained in the zero set of the derivative of the Lyapunov function. -/
theorem foo'' (hv : Differentiable ℝ v) (h_neg : ∀ x, fderiv ℝ v x (f x) ≤ 0) {s : Set E}
    (hs : limitSet (Φ ·) y ⊆ interior s) (hΦs : ∀ t : ℝ≥0, ContinuousOn (Φ t) s)
    (hΦ : IsSemigroupOn (Φ ·) {y}) :
    limitSet (Φ ·) y ⊆ {x | fderiv ℝ v x (f x) = 0 } := by
  intro x hx
  simp only [Set.mem_setOf_eq]
  -- first show that v (Φ t y) → c₀ for some c₀
  let c : ℝ := 0
  apply blubb hv.differentiableAt (Φ := Φ) (s := limitSet (Φ ·) y) hx
    (isInvariantSet_limitSet' hs hΦ hΦs) c _ sorry sorry
  intro x' hx'
  apply blubb' _ hx' hv.continuous.continuousAt
  sorry

/-- The union of all limit sets is contained in the zero set of the Lyapunov function. -/
theorem foo₃ {s s' : Set E} (hs : IsCompact s) (hv : Differentiable ℝ v)
    (h_neg : ∀ x, fderiv ℝ v x (f x) ≤ 0) (hs : ∀ y ∈ s, limitSet (Φ ·) y ⊆ interior s')
    (hΦs' : ∀ t : ℝ≥0, ContinuousOn (Φ t) s') (hΦ : IsSemigroupOn (fun x ↦ Φ ↑x) s) :
    ⋃ y ∈ s, limitSet (Φ ·) y ⊆ {x | fderiv ℝ v x (f x) = 0 } := by
  apply Set.iUnion₂_subset
  intro y hy
  apply foo'' Φ y hv h_neg (hs y hy) hΦs'
  apply hΦ.mono (by simp [hy])

-- A fixed point is contained in `⋃ y ∈ s, limitSet (Φ ·) y`.
/- Let x ∈ K such that there exists a `t` with `Φ t x ∉ {x | fderiv ℝ v x (f x) = 0 }`, then
  `x ∉ ⋃ y ∈ s, limitSet (Φ ·) y`. -/

/-- If there exists no trajectories within the zero set of the Lyapunov function, then the limit
set consists only of the fixed point. -/
theorem foo₄ {s : Set E} (hs : IsCompact s) (hv : Differentiable ℝ v)
    (h_neg : ∀ x, fderiv ℝ v x (f x) ≤ 0) {x₀ : E} (hx₀s : x₀ ∈ s) (hx₀ : ∀ t, Φ t x₀ = x₀)
    (h : ∀ x ∈ s, x ≠ x₀ → ∃ t, Φ t x ∉ {x | fderiv ℝ v x (f x) = 0 }) :
    ⋃ y ∈ s, limitSet (Φ ·) y = {x₀} := by
  apply Set.Subset.antisymm
  · intro x
    contrapose
    intro (hx : x ≠ x₀) h'
    rw [Set.mem_iUnion₂] at h'
    obtain ⟨y, hy, h'⟩ := h'
    by_cases! hx' : x ∈ s
    · obtain ⟨t, ht⟩ := h x hx' hx
      have h'' : Φ t x ∈ limitSet (Φ ·) y := by
        -- this follows from the limit set being invariant
        --have := isInvariantSet_limitSet'
        sorry
      apply ht
      apply foo'' (s := s) Φ y hv h_neg sorry sorry sorry h''
    · apply hx'
      -- the flow maps `s` to `s`
      sorry
  intro x₀ rfl
  rw [Set.mem_iUnion₂]
  use x₀, hx₀s
  simp_rw [mem_limitSet_iff, hx₀]
  exact tendsto_const_nhds.mapClusterPt


end DynSys

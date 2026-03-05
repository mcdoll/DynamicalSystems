/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.Transform
public import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall
public import DynamicalSystems.Mathlib.Analysis.ODE.ExistUnique

/-! # Stability of ODEs -/


/- Plan:

- Equilibrium point means that if γ t₀ = x₀ then γ t = x₀ for all t
- If γ solves autonomous ODE then this is equivalent to f(x₀) = 0

- Solution operator: γ : initial data → time → solution point
- `Mathlib.Analysis.Calculus.Deriv.MeanValue`


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

variable {E E' F : Type*}

section uncurry

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- todo: generalize to `𝕜`
  {x : E} {y : E'}

theorem foo₀ {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E') :
    fderiv ℝ f (x, y) (0, v) = fderiv ℝ (fun z ↦ f (x, z)) y v := by
  have hg : DifferentiableAt ℝ (fun z ↦ (x, z)) y := by fun_prop
  have := fderiv_comp (x := y) hf hg
  have this' : ((fderiv ℝ (fun z ↦ (x, z)) y) v) = (0, v) := by
    simp [(differentiableAt_const x).fderiv_prodMk (differentiableAt_fun_id)]
  rw [ContinuousLinearMap.ext_iff] at this
  specialize this v
  simp at this
  rw [this'] at this
  exact this.symm

theorem foo₀' {f : E × E' → F} (hf : DifferentiableAt ℝ f (x, y)) (v : E) :
    fderiv ℝ f (x, y) (v, 0) = fderiv ℝ (fun z ↦ f (z, y)) x v := by
  -- this follows from either `flip` or the same argument as above
  sorry

theorem fderiv_uncurry (f : E → E' → F) (hf : DifferentiableAt ℝ f.uncurry (x, y)) :
    fderiv ℝ f.uncurry (x, y) = (fderiv ℝ (f · y) x).coprod (fderiv ℝ (f x) y) := by
  ext z
  · simp [foo₀' hf]
  · simp [foo₀ hf]

end uncurry

section Flow

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsFundamentalSolutionOn (Φ : ℝ → E → E) (f : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ x, IsIntegralCurveOn (Φ · x) f s

def IsFundamentalSolution (Φ : ℝ → E → E) (f : ℝ → E → E) : Prop :=
  ∀ x, IsIntegralCurve (Φ · x) f

structure IsFundamentalSolution' (Φ : ℝ → E → E) (f : ℝ → E → E) : Prop where
  isIntegralCurve : ∀ x, IsIntegralCurve (Φ · x) f
  zero : Φ 0 = id

variable {Φ : ℝ → E → E} {f : ℝ → E → E} (v : ℝ → E → E)  (x₀ : E) (s : Set ℝ)

theorem blubb (hΦ : IsFundamentalSolutionOn Φ f s) {t : ℝ} (ht : t ∈ s)
    (hs : UniqueDiffWithinAt ℝ s t) :
    derivWithin (Φ · x₀) s t = f t (Φ t x₀) :=
  (hΦ x₀ t ht).derivWithin hs

theorem blubb' (hΦ : IsFundamentalSolution Φ f) {t : ℝ} : deriv (Φ · x₀) t = f t (Φ t x₀) :=
  (hΦ x₀ t).deriv


#check (fun t ↦ v t (Φ t x₀))

variable (t : ℝ)

#check fun t ↦ deriv (v · (Φ t x₀)) t

#check fderiv ℝ (v t) (Φ t x₀) (deriv (Φ · x₀) t)
#check deriv (Φ · x₀) t

#check v.uncurry

variable (t : ℝ) (x : E)
-- d f x y = d/dx f, d/dy f
#check fderiv ℝ (v · x) t
#check fderiv ℝ (v t) x

#check (fderiv ℝ (v · x) t).prodMap (fderiv ℝ (v t) x)

theorem foo₁ (hv : Differentiable ℝ v.uncurry) (t : ℝ) : deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (deriv (Φ · x₀) t) := by
  have uc : ∀ s, v s (Φ s x₀) = v.uncurry (s, (Φ s x₀)) := by simp
  simp_rw [uc]
  have := fderiv_comp_deriv (𝕜 := ℝ) (f := fun s ↦ (s, (Φ s x₀))) (l := v.uncurry) t sorry sorry
  simp only at this
  rw [fderiv_uncurry v (hv.differentiableAt )] at this
  simp only [ContinuousLinearMap.coprod_apply, fderiv_eq_smul_deriv] at this
  sorry

theorem foo₂ (hΦ : IsFundamentalSolution Φ f) (hv : Differentiable ℝ v.uncurry) (t : ℝ) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (f t (Φ t x₀)) := by
  have : deriv (Φ · x₀) t = f t (Φ t x₀) := blubb' x₀ hΦ
  rw [foo₁ v x₀ hv, this]

-- Continuous dependence on initial data: `dist_le_of_trajectories_ODE_of_mem`

open scoped NNReal

variable {K : ℝ≥0} (a b : ℝ) {s : ℝ → Set E}
  (hv : ∀ t ∈ Set.Ico a b, LipschitzOnWith K (v t) (s t))

#check dist_le_of_trajectories_ODE_of_mem hv


/-- The fundamental solution is continuous in the initial datum. -/
theorem continuous_isFundamentalSolution {v : E → E} {s : Set E}
    (hv : LipschitzOnWith K v s)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution' Φ (fun _ ↦ v))
    (hΦ' : ∀ t x, Φ t x ∈ s) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (Φ t) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  use ε * Real.exp (- K * t - 1/2), by positivity
  intro y hy
  have hcont : ∀ x, ContinuousOn (Φ · x) (Set.Icc 0 t) :=
    fun x ↦ (hΦ.isIntegralCurve x).continuous.continuousOn
  have h : ∀ x, ∀ t' ∈ Set.Ico 0 t, HasDerivWithinAt (Φ · x) (v (Φ t' x)) (Set.Ici t') t' := by
    intro x t' ht'
    apply HasDerivAt.hasDerivWithinAt
    apply hΦ.isIntegralCurve
  have h' : ∀ x, ∀ t' ∈ Set.Ico 0 t, Φ t' x ∈ s := by
    intro x t' ht'
    apply hΦ' t' x
  have hdist : dist (Φ 0 y) (Φ 0 x) ≤ ε * Real.exp (- K * t - 1/2) := by
    convert hy.le
    · apply congrFun hΦ.zero
    · apply congrFun hΦ.zero
  have := dist_le_of_trajectories_ODE_of_mem (fun _ _ ↦ hv) (hcont y) (h y) (h' y) (hcont x) (h x)
    (h' x) hdist t (by simp [ht])
  grw [this]
  simp only [neg_mul, sub_zero, gt_iff_lt]
  have : (-(K * t) - 1/2 + ↑K * t) = -1/2 := by ring
  rw [mul_assoc, ← lt_div_iff₀' hε, div_self (by positivity), ← Real.exp_add, this,
    Real.exp_lt_one_iff]
  norm_num

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem add_isFundamentalSolution {v : E → E} {s : Set E}
    (hv : LipschitzOnWith K v s)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution' Φ (fun _ ↦ v))
    (hΦ' : ∀ t x, Φ t x ∈ s)
    {t t' : ℝ} :
    Φ t ∘ Φ t' = Φ (t + t') := by
  ext x
  set f := fun t ↦ Φ t (Φ t' x)
  set g := fun t ↦ Φ (t + t') x
  have hf : IsIntegralCurve f (fun _ ↦ v) := hΦ.isIntegralCurve (Φ t' x)
  have hg : IsIntegralCurve g (fun _ ↦ v) := (hΦ.isIntegralCurve x).comp_add t'
  have ht₀ : f 0 = g 0 := by
    unfold f g
    simp [hΦ.zero]
  have hf' : ∀ t, f t ∈ s := (hΦ' · (Φ t' x))
  have hg' : ∀ t, g t ∈ s := (fun t ↦ hΦ' (t + t') x)
  apply congrFun <| hf.eq (fun _ ↦ hv) hf' hg hg' ht₀

theorem foo {v : E → E} {s : Set E}
    (hv : LipschitzOnWith K v s)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution' Φ (fun _ ↦ v))
    (hΦ' : ∀ t x, Φ t x ∈ s)
    {t : ℝ} :
    (Φ (-t)) ∘ Φ t = id := by
  rw [add_isFundamentalSolution hv Φ hΦ hΦ']
  simp [hΦ.zero]


theorem add_isFundamentalSolutionOn (Φ : ℝ → E → E) (v : E → E) {a b : ℝ}
    (hΦ : IsFundamentalSolutionOn Φ (fun _ ↦ v) (Set.Ioo a b)) {t s : ℝ}
    (ht : t ∈ Set.Ioo a b) (hs : s ∈ Set.Ioo a b) (hts : t + s ∈ Set.Ioo a b) :
    Φ t ∘ Φ s = Φ (t + s) := by
  ext x
  simp only [Function.comp_apply]
  sorry

end Flow

section Energy

open NNReal Filter

def memK (f : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous f ∧ StrictMono f ∧ f 0 = 0

def memKR (f : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous f ∧ StrictMono f ∧ f 0 = 0 ∧ Tendsto f atTop atTop

variable [NormedAddCommGroup E]

def locPosDefFun (v : ℝ → E → ℝ) (x₀ : E) : Prop :=
  ∃ (r : ℝ) (_hr : 0 < r) (α : ℝ≥0 → ℝ≥0) (_hα : memK α),
  ∀ t, v t x₀ = 0 ∧ ∀ x ∈ Metric.ball (x₀ : E) r, α ‖x - x₀‖₊ ≤ v t x


end Energy

section Stable

variable [NormedAddCommGroup E]

def IsFixedPoint (v : ℝ → E → ℝ) (x₀ : E) : Prop :=
  ∀ t, v t x₀ = v 0 x₀

def IsLyapunovStable (v : ℝ → E → ℝ) (x₀ : E) (t₀ : ℝ) : Prop :=
  ∀ ε (_hε : 0 < ε), ∃ δ, ∀ x, ‖x - x₀‖ < δ → ∀ t (_ht : t₀ ≤ t), ‖v t x‖ < ε


end Stable

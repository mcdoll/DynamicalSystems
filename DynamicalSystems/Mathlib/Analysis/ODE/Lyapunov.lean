/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution
public import DynamicalSystems.Mathlib.Analysis.ODE.Gronwall2

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

section Flow

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {Φ : ℝ → E → E} {f : ℝ → E → E} {v : ℝ → E → E} {x₀ : E} (s : Set ℝ) {t : ℝ}

theorem foo₁ (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) (hΦ : DifferentiableAt ℝ (Φ · x₀) t) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (deriv (Φ · x₀) t) := by
  calc
    _ = deriv (fun s ↦ v.uncurry (s, (Φ s x₀))) t := by simp
    _ = (fderiv ℝ (Function.uncurry v) (t, Φ t x₀)) (deriv (fun s ↦ (s, Φ s x₀)) t) := by
      have hΦ' : DifferentiableAt ℝ (fun s ↦ (s, Φ s x₀)) t := by fun_prop
      apply fderiv_comp_deriv t hv hΦ'
    _ = deriv (fun x ↦ v x (Φ t x₀)) t + (fderiv ℝ (v t) (Φ t x₀)) (deriv (fun x ↦ Φ x x₀) t) := by
      rw [fderiv_uncurry v hv]
      simp only [ContinuousLinearMap.coprod_apply, fderiv_eq_smul_deriv]
      congr
      · simp [hΦ]
      · simp [hΦ]

theorem foo₂ (hΦ : IsFundamentalSolution Φ f) (hv : DifferentiableAt ℝ v.uncurry (t, Φ t x₀)) :
    deriv (fun s ↦ v s (Φ s x₀)) t =
    deriv (v · (Φ t x₀)) t + fderiv ℝ (v t) (Φ t x₀) (f t (Φ t x₀)) := by
  rw [foo₁ hv (hΦ.isIntegralCurve x₀ t).differentiableAt, hΦ.deriv x₀]

-- Continuous dependence on initial data: `dist_le_of_trajectories_ODE_of_mem`

open scoped NNReal

variable {K : ℝ≥0} (a b : ℝ) {s : ℝ → Set E}
  (hv : ∀ t ∈ Set.Ico a b, LipschitzOnWith K (v t) (s t))

/-- The fundamental solution is continuous in the initial datum. -/
theorem continuous_isFundamentalSolution {v : E → E} {s : Set E}
    (hv : LipschitzOnWith K v s)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution Φ (fun _ ↦ v))
    (hΦ' : ∀ t (_ht : 0 ≤ t) x, Φ t x ∈ s) {t : ℝ} (ht : 0 ≤ t) :
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
    intro x t' ⟨ht', _⟩
    apply hΦ' t' ht' x
  have hdist : dist (Φ 0 y) (Φ 0 x) ≤ ε * Real.exp (- K * t - 1/2) := by
    convert hy.le
    · apply hΦ.zero_apply
    · apply hΦ.zero_apply
  have := dist_le_of_trajectories_ODE_of_mem (fun _ _ ↦ hv) (hcont y) (h y) (h' y) (hcont x) (h x)
    (h' x) hdist t (by simp [ht])
  grw [this]
  simp only [neg_mul, sub_zero, gt_iff_lt]
  have : (-(K * t) - 1/2 + ↑K * t) = -1/2 := by ring
  rw [mul_assoc, ← lt_div_iff₀' hε, div_self (by positivity), ← Real.exp_add, this,
    Real.exp_lt_one_iff]
  norm_num

/-- The fundamental solution is continuous in the initial datum. -/
theorem continuous_isFundamentalSolution' {v : E → E}
    (hv : LipschitzWith K v)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution Φ (fun _ ↦ v)) :
    Continuous Φ.uncurry := by
  rw [Metric.continuous_iff]
  intro ⟨t₀, x₀⟩ ε hε
  have h_cont_x₀ : ContinuousAt (Φ · x₀) t₀ :=
    (hΦ.isIntegralCurve x₀).continuous.continuousAt
  rw [Metric.continuousAt_iff] at h_cont_x₀
  obtain ⟨δ₀, hδ₀, h_cont_x₀⟩ := h_cont_x₀ (ε / 2) (by positivity)
  use min δ₀ ((ε / 2) * Real.exp (- K * (|t₀| + δ₀) - 1/2)), by positivity
  intro ⟨t, x⟩ hy
  rw [Prod.dist_eq, max_lt_iff] at hy
  simp only [neg_mul, one_div] at hy
  obtain ⟨ht, hx⟩ := hy
  calc
    _ = dist (Φ t x) (Φ t₀ x₀) := by simp
    _ ≤ dist (Φ t x) (Φ t x₀) + dist (Φ t x₀) (Φ t₀ x₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := by
      gcongr
      · have hcont : ∀ x, ContinuousOn (Φ · x) (Set.uIcc 0 t) :=
          fun x ↦ (hΦ.isIntegralCurve x).continuous.continuousOn
        have h : ∀ x, ∀ t' ∈ Set.uIcc 0 t, HasDerivAt (Φ · x) (v (Φ t' x)) t' := by
          intro x t' ht'
          apply hΦ.isIntegralCurve
        have hdist : dist (Φ 0 x) (Φ 0 x₀) ≤ (ε / 2) * Real.exp (- K * |t| - 2⁻¹) := by
          rw [hΦ.zero_apply, hΦ.zero_apply]
          grw [hx, Std.min_le_right]
          gcongr
          simp only [neg_mul, neg_le_neg_iff]
          gcongr
          calc
            _ = |t₀ + (t - t₀)| := by congr; ring
            _ ≤ |t₀| + |t - t₀| := by apply abs_add_le
            _ ≤ |t₀| + δ₀ := by
              gcongr
              rw [← Real.norm_eq_abs, ← dist_eq_norm]
              grw [ht, Std.min_le_left]
        have := dist_le_of_trajectories_ODE' (fun _ _ ↦ hv) (hcont x) (h x) (hcont x₀) (h x₀) hdist
          t (by simp)
        simp only [neg_mul, sub_zero] at this
        grw [this]
        rw [mul_assoc, ← lt_div_iff₀' (by positivity), div_self (by positivity), ← Real.exp_add,
          Real.exp_lt_one_iff]
        grind
      · apply h_cont_x₀
        apply lt_of_lt_of_le ht Std.min_le_left
    _ = _ := by ring

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem add_isFundamentalSolution {v : E → E} {s : Set E}
    (hv : LipschitzOnWith K v s)
    (Φ : ℝ → E → E)
    (hΦ : IsFundamentalSolution Φ (fun _ ↦ v))
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
    (hΦ : IsFundamentalSolution Φ (fun _ ↦ v))
    (hΦ' : ∀ t x, Φ t x ∈ s)
    {t : ℝ} :
    (Φ (-t)) ∘ Φ t = id := by
  rw [add_isFundamentalSolution hv Φ hΦ hΦ']
  simp [hΦ.zero]

end Flow

section Energy

open NNReal Filter

/-- A function of class `K`. -/
def memK (f : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous f ∧ StrictMono f ∧ f 0 = 0

/-- A function of class `KR`. -/
def memKR (f : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous f ∧ StrictMono f ∧ f 0 = 0 ∧ Tendsto f atTop atTop

variable [NormedAddCommGroup E]

/-- A function is locally positive definite at `x₀` if .. -/
def locPosDefFun (v : ℝ → E → ℝ) (x₀ : E) : Prop :=
  ∃ (r : ℝ) (_hr : 0 < r) (α : ℝ≥0 → ℝ≥0) (_hα : memK α),
  ∀ t, v t x₀ = 0 ∧ ∀ x ∈ Metric.ball (x₀ : E) r, α ‖x - x₀‖₊ ≤ v t x


end Energy

section Stable

variable [NormedAddCommGroup E]

/-- A fixed point -/
def IsFixedPoint (v : ℝ → E → ℝ) (x₀ : E) : Prop :=
  ∀ t, v t x₀ = v 0 x₀

/-- A Lyapunov stable point -/
def IsLyapunovStable (v : ℝ → E → ℝ) (x₀ : E) (t₀ : ℝ) : Prop :=
  ∀ ε (_hε : 0 < ε), ∃ δ, ∀ x, ‖x - x₀‖ < δ → ∀ t (_ht : t₀ ≤ t), ‖v t x‖ < ε


end Stable

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Mathlib.Analysis.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # Basic definitions of Euler-Lagrange equations -/

@[expose] public noncomputable section

variable {D E F : Type*}

section EL

variable
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {L : ℝ → E → E → ℝ} {q : ℝ → E} {p : ℝ → E} {t : ℝ}

def eulerLagrangeOp (L : ℝ → E → E → ℝ) (t : ℝ) (q : ℝ → E) (p : ℝ → E) : E →L[ℝ] ℝ :=
  deriv (fun t ↦ fderiv ℝ (L t (q t)) (p t)) t - fderiv ℝ (L t · (p t)) (q t)

attribute [fun_prop] ContDiffAt.differentiableAt ContDiffAt.fderiv

@[fun_prop]
theorem ContDiff.differentiableAt {n : WithTop ℕ∞} (hq : ContDiff ℝ n q) (hn : n ≠ 0) :
    DifferentiableAt ℝ q t := (hq.differentiable hn).differentiableAt

theorem deriv_foo (hL : ContDiff ℝ 2 (fun t ↦ (L t ·).uncurry).uncurry) (hq : ContDiff ℝ 2 q) :
    deriv (fun s ↦ fderiv ℝ (L s (q s)) (deriv q s) (deriv q s) - L s (q s) (deriv q s)) t =
    (eulerLagrangeOp L t q (deriv q)) (deriv q t) - deriv (L · (q t) (deriv q t)) t := calc
  _ = deriv (fun s ↦ fderiv ℝ (L s (q s)) (deriv q s)) t (deriv q t) +
      fderiv ℝ (L t (q t)) (deriv q t) (deriv (deriv q) t) -
      deriv (fun s ↦ L s (q s) (deriv q s)) t := by
    have h_diff : DifferentiableAt ℝ (fun s ↦ fderiv ℝ (L s (q s)) (deriv q s)) t := by
      apply Differentiable.differentiableAt
      -- refine Differentiable.fderiv_two ?_ ?_ -- need a `ContDiffAt` version
      fun_prop
    have : DifferentiableAt ℝ (fun s ↦ (fderiv ℝ (L s (q s)) (deriv q s)) (deriv q s)) t := by
      fun_prop (maxTransitionDepth := 2)
    rw [deriv_fun_sub this]
    · rw [deriv_clm_apply h_diff (by fun_prop)]
    · have : (fun s ↦ L s (q s) (deriv q s)) =
          (fun t ↦ (L t ·).uncurry).uncurry ∘ (fun t ↦ (t, q t, deriv q t)) := by
        ext y
        simp
      rw [this]
      fun_prop (maxTransitionDepth := 2) (disch := positivity)
  _ = _ := by
    rw [foo₂' (f := L) ?_ ?_ (by fun_prop), eulerLagrangeOp, sub_apply]
    · ring
    · fun_prop (maxTransitionDepth := 2) (disch := positivity)
      /-apply Differentiable.differentiableAt
      apply hL.differentiable (by positivity)-/
    · fun_prop (disch := positivity)
      /- apply Differentiable.differentiableAt
      apply hq.differentiable (by positivity) -/

theorem blubb {f : E →L[ℝ] E →L[ℝ] ℝ} (v : E) : fderiv ℝ (fun x ↦ f x x) v = f v + f.flip v := calc
  _ = (f.precompR E v) (fderiv ℝ id v) + (f.precompL E (fderiv ℝ id v)) v := by
    exact f.fderiv_of_bilinear (by fun_prop) (by fun_prop)
  _ = _ := by
    ext; simp

def Function.hamiltonian (L : ℝ → E → F → ℝ) (t : ℝ) (x : E) (v : F) : ℝ :=
  fderiv ℝ (L t x) v v - L t x v

theorem deriv_hamiltonian (hL : ContDiff ℝ 2 (fun t ↦ (L t ·).uncurry).uncurry)
    (hq : ContDiff ℝ 2 q) :
    deriv (fun s ↦ L.hamiltonian s (q s) (deriv q s)) t =
    (eulerLagrangeOp L t q (deriv q)) (deriv q t) - deriv (L · (q t) (deriv q t)) t :=
  deriv_foo hL hq

theorem baz {γ : ℝ → E} (hγ : ContDiff ℝ 2 γ) (hL : ContDiff ℝ 2 (fun t ↦ (L t ·).uncurry).uncurry)
    {f : ℝ → E → (E →L[ℝ] ℝ)} (ht : 0 ≤ t)
    (hf : ∀ s ∈ Set.Icc 0 t, eulerLagrangeOp L s γ (deriv γ) (deriv γ s) ≤ f s (γ s) (deriv γ s)) :
    L.hamiltonian t (γ t) (deriv γ t) - L.hamiltonian 0 (γ 0) (deriv γ 0) ≤
      ∫ s in 0..t, f s (γ s) (deriv γ s) - deriv (L · (γ s) (deriv γ s)) s := calc
  _ = ∫ s' in 0..t, deriv (fun s ↦ L.hamiltonian s (γ s) (deriv γ s)) s' := by
    rw [intervalIntegral.integral_deriv_eq_sub_uIoo]
    · sorry
    · intro s hs
      sorry
    · apply Continuous.intervalIntegrable
      refine ContDiff.continuous_deriv_one ?_
      sorry
  _ ≤ _ := by
    apply intervalIntegral.integral_mono_on ht sorry sorry
    intro s hs
    rw [deriv_hamiltonian hL hγ]
    grw [hf s hs]

end EL

variable
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
structure Lagrangian where
  /-- The kinetic energy -/
  protected T : ℝ → E → F →L[ℝ] F →L[ℝ] ℝ
  /-- The potential energy -/
  protected V : ℝ → E → ℝ
  contDiff_T : ContDiff ℝ 2 T.uncurry
  contDiff_V : ContDiff ℝ 2 V.uncurry

namespace Lagrangian

variable (L : Lagrangian E F) {t : ℝ}

/-- The Lagrangian function, `L = T - V` -/
@[coe]
protected
def toFun (L : Lagrangian E F) (t : ℝ) (q : E) (p : F) : ℝ := L.T t q p p - L.V t q

instance : CoeFun (Lagrangian E F) (fun _ ↦ ℝ → E → F → ℝ) where
  coe L := L.toFun

/-- The Hamiltonian function, `H = T + V`.

Note that this Hamiltonian is in the Lagrangian coordinates, `q, d/dt q`. -/
def H (L : Lagrangian E F) (t : ℝ) (q : E) (p : F) : ℝ := L.T t q p p + L.V t q

@[fun_prop]
theorem contDiff_L : ContDiff ℝ 2 (fun t ↦ (L t ·).uncurry).uncurry := by
  unfold Lagrangian.toFun
  sorry

@[fun_prop]
theorem contDiff_H : ContDiff ℝ 2 (fun t ↦ (L.H t ·).uncurry).uncurry := by
  sorry

theorem fderiv_eq {q : E} {p : F} : fderiv ℝ (L t q) p = fderiv ℝ (fun p ↦ L.T t q p p) p := by
  apply fderiv_sub_const

variable (L' : Lagrangian E E)

theorem fderiv_sub_eq_H {q p : E} : fderiv ℝ (L' t q) p p - L' t q p = L'.H t q p := by
  rw [fderiv_eq, blubb]
  simp [H, Lagrangian.toFun]

theorem hamiltonian_eq_H : Function.hamiltonian L' = L'.H := by
  ext t q p
  apply fderiv_sub_eq_H

/-- `d/dt H = f d/dt q - ∂_t L` if `f` is the inhomogeneity of the Euler-Lagrange equation.

In particular, if `f = 0` and `L` is time-independent, then `d/dt H = 0`. -/
theorem deriv_H {q : ℝ → E} (hq : ContDiff ℝ 2 q) :
    deriv (fun s ↦ L'.H s (q s) (deriv q s)) t = eulerLagrangeOp L' t q (deriv q) (deriv q t) -
    deriv (L' · (q t) (deriv q t)) t := by
  simp_rw [← fderiv_sub_eq_H]
  rw [deriv_foo ?_ hq]
  apply contDiff_L

end Lagrangian

variable {γ : ℝ → E} {Φ : NonautonomousFlow ℝ E} {L : Lagrangian E E} {f : ℝ → E → (E →L[ℝ] ℝ)}

variable (γ L f) in
/-- A curve is Lagrangian if it is differentiable and satisfies
`d/dt (∂_p L t (Φ t) (Φ' t)) - ∂_q L t (Φ t) (Φ' t) = f t (Φ t)` for a given
Lagrangian `L` and inhomogeneity `f`. -/
def IsLagrangianCurve : Prop :=
  ContDiff ℝ 2 γ ∧ ∀ t, eulerLagrangeOp L t γ (deriv γ) = f t (γ t)

variable {t : ℝ} {x : E} {y : F}

variable (Φ L f) in
def IsLagrangianFlow : Prop := ∀ t₀ x₀, IsLagrangianCurve (Φ t₀ x₀) L f

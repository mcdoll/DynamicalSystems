/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.Lyapunov
public import DynamicalSystems.Mathlib.Analysis.Calculus
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-! # Stability of Hamiltonian systems -/

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {H : WithLp 2 (E × E) → ℝ} (ζ : WithLp 2 (E × E))

/-- The Hamilton vector field associated to a Hamiltonian. -/
def hamiltonvf (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) : WithLp 2 (E × E) :=
  LinearEquiv.withLpCongr 2 (LinearEquiv.skewSwap ℝ E E) (gradient H ζ)

@[simp]
theorem fst_hamiltonvf (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) :
    (hamiltonvf H ζ).fst = -(gradient H ζ).snd := by
  simp [hamiltonvf]

@[simp]
theorem snd_hamiltonvf (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) :
    (hamiltonvf H ζ).snd = (gradient H ζ).fst := by
  simp [hamiltonvf]

theorem norm_hamiltonvf_eq_norm_gradient (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) :
    ‖hamiltonvf H ζ‖ = ‖gradient H ζ‖ := by
  suffices ‖hamiltonvf H ζ‖ ^ 2 = ‖gradient H ζ‖ ^ 2 by
    simpa using this
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), WithLp.prod_inner_apply]
  simp [add_comm]

theorem exists_hamiltonvf_autonomousFlow (hbdd : ∃ C, LipschitzWith C (gradient H)) :
    ∃ Φ : AutonomousFlow ℝ (WithLp 2 (E × E)), Φ.IsFundamentalSolution (hamiltonvf H) := by
  obtain ⟨C, hC⟩ := hbdd
  suffices LipschitzWith C (hamiltonvf H) from this.exists_autonomousFlow
  suffices Isometry (LinearEquiv.withLpCongr 2 (LinearEquiv.skewSwap ℝ E E)) by
    apply (this.lipschitzWith_iff C).mpr hC
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  suffices ‖WithLp.toLp 2 (-x.snd, x.fst)‖ ^ 2 = ‖x‖ ^ 2 by
    simpa using this
  simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), WithLp.prod_inner_apply]
  simp [add_comm]

theorem fderiv_apply_hamiltonvf (x : WithLp 2 (E × E)) :
    fderiv ℝ H x (hamiltonvf H x) = 0 := by
  rw [← inner_gradient_left, WithLp.prod_inner_apply]
  simp [hamiltonvf, real_inner_comm]

open Topology

variable {Φ : AutonomousFlow ℝ (WithLp 2 (E × E))}

/-- The Hamiltonian is a Lyapunov function for the Hamilton flow. -/
theorem isLyapunov_hamiltonian (hΦ : Φ.IsFundamentalSolution (hamiltonvf H))
    (hH : Differentiable ℝ H) (h₁ : ∀ x, 0 ≤ H x) :
    IsLyapunov H Φ := by
  apply AutonomousFlow.isLyapunov (by fun_prop) h₁ hH
  intro x
  rw [hΦ.deriv, fderiv_apply_hamiltonvf]

theorem isStableOn_nhdsSet_of_hamiltonvf (s : Set (WithLp 2 (E × E)))
    (hΦ : Φ.IsFundamentalSolution (hamiltonvf H))
    (hH : Differentiable ℝ H)
    (h₁ : ∀ x, 0 ≤ H x) (h₂ : ∀ x, H x = 0 ↔ x ∈ s)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | H p ≤ δ₀ }) :
    (𝓝ˢ s).IsStableOn Φ (Set.Ici 0) := by
  apply IsLyapunov.isStableOn_nhdsSet ?_ h₂ Φ.map_id hδ₀ h_cpt
  apply isLyapunov_hamiltonian hΦ hH h₁

theorem isStableOn_nhds_of_hamiltonvf (x₀ : WithLp 2 (E × E))
    (hΦ : Φ.IsFundamentalSolution (hamiltonvf H))
    (hH : Differentiable ℝ H)
    (h₁ : ∀ x, 0 ≤ H x) (h₂ : ∀ x, H x = 0 ↔ x = x₀)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | H p ≤ δ₀ }) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  apply IsLyapunov.isStableOn_nhds ?_ h₂ Φ.map_id hδ₀ h_cpt
  apply isLyapunov_hamiltonian hΦ hH h₁

section oscillator

theorem gradient_sq_norm (ζ : E) :
    gradient (fun x : E ↦ ‖x‖ ^ 2) ζ = 2 • ζ := by
  have hf := (hasStrictFDerivAt_norm_sq (F := E) ζ).hasFDerivAt
  have hg : HasGradientAt (fun x : E ↦ ‖x‖ ^ 2) (2 • ζ) ζ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hf using 1
    ext y
    simp
  exact hg.gradient

variable (E) in
/-- The vector field of the harmonic oscillator -/
abbrev harmonicOscillatorVf (ζ : WithLp 2 (E × E)) : WithLp 2 (E × E) :=
  hamiltonvf (fun x : WithLp 2 (E × E) ↦ ‖x‖ ^ 2) ζ

@[simp]
theorem fst_harmonicOscillatorVf (ζ : WithLp 2 (E × E)) :
    (harmonicOscillatorVf E ζ).fst = -2 • ζ.snd := by
  simp [harmonicOscillatorVf, gradient_sq_norm]
  norm_cast

@[simp]
theorem snd_harmonicOscillatorVf (ζ : WithLp 2 (E × E)) :
    (harmonicOscillatorVf E ζ).snd = 2 • ζ.fst := by
  simp [harmonicOscillatorVf, gradient_sq_norm]

private
theorem lipschitzWith_two_grad_norm_sq :
    LipschitzWith 2 (gradient fun x : E ↦ ‖x‖ ^ 2) := by
  have h : (gradient fun x : E ↦ ‖x‖ ^ 2) = fun x : E ↦ (2 : ℝ) • x := by
    funext x
    simp [gradient_sq_norm, two_smul]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp [h, dist_eq_norm, ← smul_sub, norm_smul, dist_eq_norm]

variable (E) in
/-- The flow of the harmonic oscillator -/
@[no_expose]
def harmonicOscillatorFlow : AutonomousFlow ℝ (WithLp 2 (E × E)) :=
  (exists_hamiltonvf_autonomousFlow (H := (fun x : WithLp 2 (E × E) ↦ ‖x‖ ^ 2))
    ⟨2, lipschitzWith_two_grad_norm_sq⟩).choose

/-- The harmonic oscillator flow is the fundamental solution of the harmonic oscillator vector
field. -/
theorem isFundamentalSolution_harmonicOscillatorFlow :
    (harmonicOscillatorFlow E).IsFundamentalSolution (harmonicOscillatorVf E) :=
  (exists_hamiltonvf_autonomousFlow (H := (fun x : WithLp 2 (E × E) ↦ ‖x‖ ^ 2))
    ⟨2, lipschitzWith_two_grad_norm_sq⟩).choose_spec

/-- The origin of the harmonic oscillator is stable. -/
theorem isStableOn_harmonicOscillatorFlow [FiniteDimensional ℝ E] :
    (𝓝 0).IsStableOn (harmonicOscillatorFlow E) (Set.Ici 0) := by
  apply isStableOn_nhds_of_hamiltonvf (δ₀ := 1) 0 isFundamentalSolution_harmonicOscillatorFlow
    (differentiable_id.norm_sq ℝ) (by intro; positivity) (by simp) (by simp)
  have : {p : WithLp 2 (E × E) | ‖p‖ ^ 2 ≤ 1} = Metric.closedBall 0 1 := by
    ext; simp
  rw [this]
  exact isCompact_closedBall 0 1

end oscillator

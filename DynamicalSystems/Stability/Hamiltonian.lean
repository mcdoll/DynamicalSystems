/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.Lyapunov
public import DynamicalSystems.Mathlib.Analysis.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public noncomputable section

/-! # Stability of Hamiltonian systems -/


section AutFundSoln

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fundamental solution for autonomous systems. -/
structure IsFundamentalSolution' (Φ : ℝ → E → E) (f : E → E) : Prop where
  isIntegralCurve : ∀ x, IsIntegralCurve (Φ · x) (fun _ ↦ f)
  initial : ∀ x₀, Φ 0 x₀ = x₀

variable {Φ : ℝ → E → E} {f : E → E}

theorem deriv_isFundamentalSolution' (h : IsFundamentalSolution' Φ f) (x : E) :
    deriv (Φ · x) 0 = f x := by
  refine HasDerivAt.deriv ?_
  convert h.isIntegralCurve x 0
  simp [h.initial]

end AutFundSoln

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {H : WithLp 2 (E × E) → ℝ} (ζ : WithLp 2 (E × E))

/-- The Hamilton vector field associated to a Hamiltonian. -/
def hamiltonvf (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) : WithLp 2 (E × E) :=
  LinearEquiv.withLpCongr 2 (LinearEquiv.skewSwap ℝ E E) (gradient H ζ)

theorem fderiv_apply_hamiltonvf (h : Differentiable ℝ H) (x : WithLp 2 (E × E)) :
    (fderiv ℝ H x) (hamiltonvf H x) = 0 := by
  unfold hamiltonvf
  simp
  -- need `fderiv_prod` for `WithLp`
  sorry

open Topology

variable {Φ : Flow ℝ (WithLp 2 (E × E))}

/-- The Hamiltonian is a Lyapunov function for the Hamilton flow. -/
theorem isLyapunov_hamiltonian (hΦ : IsFundamentalSolution' Φ (hamiltonvf H))
    (hH : Differentiable ℝ H) (h₁ : ∀ x, 0 ≤ H x) :
    IsLyapunov H Φ := by
  apply Flow.isLyapunov (by intro x t; exact (hΦ.isIntegralCurve x t).differentiableAt) h₁ hH
  intro x
  rw [deriv_isFundamentalSolution' hΦ, fderiv_apply_hamiltonvf hH]


theorem isStableOn (x₀ : WithLp 2 (E × E))
    (hΦ : IsFundamentalSolution' Φ (hamiltonvf H))
    (hH : Differentiable ℝ H)
    (h₁ : ∀ x, 0 ≤ H x) (h₂ : ∀ x, H x = 0 ↔ x = x₀)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h_cpt : IsCompact { p | H p ≤ δ₀ }) :
    (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  apply IsLyapunov.isStableOn_nhds ?_ h₂ hΦ.initial hδ₀ h_cpt
  apply isLyapunov_hamiltonian hΦ hH h₁

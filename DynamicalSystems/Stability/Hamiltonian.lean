/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Stability.Lyapunov
public import DynamicalSystems.Mathlib.Analysis.Calculus
public import DynamicalSystems.Mathlib.Analysis.ODE.FundamentalSolution
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Stability of Hamiltonian systems -/

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {H : WithLp 2 (E × E) → ℝ} (ζ : WithLp 2 (E × E))

/-- The Hamilton vector field associated to a Hamiltonian. -/
def hamiltonvf (H : WithLp 2 (E × E) → ℝ) (ζ : WithLp 2 (E × E)) : WithLp 2 (E × E) :=
  LinearEquiv.withLpCongr 2 (LinearEquiv.skewSwap ℝ E E) (gradient H ζ)

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

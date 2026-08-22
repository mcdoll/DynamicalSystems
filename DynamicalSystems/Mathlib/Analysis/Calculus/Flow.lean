/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Dynamics.Flow

/-! # Derivative of flows -/

public section


variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {Φ Φ' : Flow ℝ E} {x : E} {t : ℝ}

theorem DifferentiableAt.deriv_eq_deriv_zero (h : ∀ x, DifferentiableAt ℝ (Φ · x) 0) :
    deriv (Φ · x) t = deriv (Φ · (Φ t x)) 0 := calc
  _ = deriv (fun s ↦ (Φ (s - t) (Φ t x))) t := by
    congr
    ext s
    rw [← Φ.map_add']
    grind
  _ = deriv (fun s : ℝ ↦ s - t) t • deriv (Φ · (Φ t x)) ((fun s : ℝ ↦ s - t) t) :=
    deriv.scomp (h := (· - t)) (g₁ := (Φ · (Φ t x))) t (by simp [h (Φ t x)]) (by fun_prop)
  _ = _ := by
    simp

theorem deriv_comp_flow {v : E → F} (hv : Differentiable ℝ v) (h : ∀ x, Differentiable ℝ (Φ · x))
    (t : ℝ) (x : E) :
    deriv (v <| Φ · x) t = fderiv ℝ v (Φ t x) (deriv (Φ · (Φ t x)) 0) := calc
  _ = (fderiv ℝ v (Φ t x)) (deriv (Φ · x) t) :=
    fderiv_comp_deriv t (by fun_prop) (by fun_prop)
  _ = _ := by rw [DifferentiableAt.deriv_eq_deriv_zero (by fun_prop)]

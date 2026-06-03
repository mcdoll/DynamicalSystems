/-
Copyright (c) 2026 Inacio Vasquez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inacio Vasquez
-/

module public import DynamicalSystems.Stability.Example

/-!
# Minimal Lyapunov certificate example

This file records a small downstream certificate surface for the existing
one-dimensional linear-decay example.

It does not introduce a new stability theorem.  It gives a named, testable
certificate layer over the existing Lyapunov example:
`x ↦ x ^ 2` for the flow `x' = -r x`, with `0 ≤ r`.
-/

@[expose] public noncomputable section

open scoped Topology

namespace DynamicalSystems

/-- Minimal certificate: `x ↦ x ^ 2` is a Lyapunov function for the
one-dimensional linear decay flow `x' = -r x`, assuming `0 ≤ r`. -/
theorem minimalLyapunovCertificate_linear_decay {r : ℝ} (hr : 0 ≤ r) :
    IsLyapunov (fun x : ℝ => x ^ 2) (smulFlow (-r)) :=
  _root_.isLyapunov_sq_smulFlow hr

/-- Minimal certified consequence: the origin is forward stable for the same
one-dimensional linear decay flow. -/
theorem minimalLyapunovCertificate_linear_decay_stable {r : ℝ} (hr : 0 ≤ r) :
    (𝓝 (0 : ℝ)).IsStableOn (smulFlow (-r)) (Set.Ici (0 : ℝ)) :=
  _root_.isStableOn_smulFlow hr

end DynamicalSystems

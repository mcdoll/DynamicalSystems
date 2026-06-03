# Minimal Lyapunov Certificate Example

STATUS: MINIMAL_EXAMPLE_REEXPORT_ONLY

Lean module:

- `DynamicalSystems.Stability.MinimalCertificate`

Closed objects:

- `DynamicalSystems.minimalLyapunovCertificate_linear_decay`
- `DynamicalSystems.minimalLyapunovCertificate_linear_decay_stable`

What this proves:

- For `r >= 0`, `x ↦ x^2` is an `IsLyapunov` function for the existing one-dimensional flow `smulFlow (-r)`.
- For `r >= 0`, the origin is forward stable for the existing one-dimensional flow `smulFlow (-r)`.

Does not prove:

- new stability theorem
- global stability for arbitrary nonlinear systems
- global asymptotic stability for arbitrary nonlinear systems
- exponential stability
- converse Lyapunov theorem
- LaSalle theorem generalization
- mathlib upstream acceptance
- control-theory maintainership resolution
- new applied-dynamics result

Minimal next object:

`MaintainerFeedbackOrConcreteNonlinearCertificateExample`

import VersoManual

import DynamicalSystems.InputOutput.Causal
import DynamicalSystems.InputOutput.ClosedLoop
import DynamicalSystems.InputOutput.Dissipative
import DynamicalSystems.InputOutput.FiniteGain
import DynamicalSystems.InputOutput.Stability

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Input-output analysis" =>

In the previous section, we investigated stability of dynamical systems. In applications however,
we are interested in the following setting: we have have an input function that feeds into the ODE
and we extract an output from the state.

This section follows the book "L2-gain and Passivity Techniques in Nonlinear Control" by Arjen van
der Schaft, in particular Chapter 1 and Chapter 2.

# Input-output maps

{ref "lploc"}[Previously] we recalled the fundamentals of `Lp` spaces.

## Relations

The analysis of input-output systems usually involves chaining multiple systems together in a
feedback loop. While all practical application the feedback connection is again a well-defined
input-output map, this is not necessarily the case in general. It would be possible to always
assume that the feedback connection is well-defined, but this means that artificial looking
assumptions have to be carried around for proofs that do not require them.
To avoid talking about well-definedness, instead of using input-output maps, we use relations.

A relation is simply a subset of the cartesian product of two sets.

{docstring SetRel}

Every function defines a relation via its graph {name}`Function.graph`.

## Unbundled functions

There are different ways of writing $`L^p` functions in mathlib. The space of $`L^p` functions is
given by {name}`MeasureTheory.Lp` and consists of all _equivalence classes_ of functions together
with the property that their $`L^p` norm is finite. Proving theorems with equivalence classes
can be rather tedious, because all equalities only hold almost everywhere and one has to use
{tactic}`filter_upwards` to prove equalities such as `(f + g) x = f x + g x`.

To circumvent these issues, we use functions directly and also we do not bundle in the property
that we are dealing with (local) $`L^p` functions, but rather assume these properties separately.
So a nonlinear operator is just a map `f : (α → E) → (α → F)` and implicitly we use junk values for
`f u` in the case that `u : α → E` is not a local $`L^p` function.

# Causality

We have two definitions for causal maps: one for relations and one for functions:

{docstring SetRel.IsCausal}
{docstring Function.IsCausal}

and if a relation is induced by a function, then these definitions agree:

{docstring Function.graph_isCausal_iff_isCausal}

# Stability

We have two notions of stability, `Lp`-stability and finite gain stability.

A nonlinear operator `f` is called `Lp` stable if for every `u : Lp` the output is again in
`Lp`. We use unbundled `Lp` functions using `MemLp`.

{docstring SetRel.IsLpStable}
{docstring Function.IsLpStable}

The second notion is _finite gain stability_. A map `f` is finite gain stable if there exist
`k` and `β` such that  `‖(f u)ₜ‖ ≤ k * ‖uₜ‖ + β` for all local `Lp` functions `u`.

{docstring SetRel.IsFiniteGainStableWith}
{docstring Function.IsFiniteGainStableWith}

It can easily be shown that every finite gain stable system is `Lp` stable

{docstring Function.IsFiniteGainStableWith.isLpStable}

and every causal system that satisfies for every $`u : L^p$` the estimate
$$`‖f u‖ ≤ k * ‖u‖ + β`
is finite gain stable:

{docstring Function.IsCausal.isFiniteGainStableWith}

## Small gains theorems

# Dissipation inequalities and passivity

{docstring SetRel.IsDissipativeWith}
{docstring Function.IsDissipativeWith}

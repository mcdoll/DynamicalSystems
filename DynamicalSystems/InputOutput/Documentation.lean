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

## Causal maps

We have two definitions for causal maps: one for relations and one for functions:

{docstring Function.IsCausal}
{docstring SetRel.IsCausal}

and if a relation is induced by a function, then these definitions agree:

{docstring Function.graph_isCausal_iff_isCausal}

## Finite gain stability

## Dissipation inequalities

{docstring IsDissipativeWith}

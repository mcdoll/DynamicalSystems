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

In {ref "Basics"}[Basics] we recalled the fundamentals of `Lp` spaces.

## Technical preliminaries

### Relations



### Unbundled functions

## Causal maps

We have two definitions for causal maps: one for relations and one for functions:

{docstring Function.IsCausal}
{docstring SetRel.IsCausal}

and if a relation is induced by a function, then these definitions agree:

{docstring Function.graph_isCausal_iff_isCausal}

## Finite gain stability

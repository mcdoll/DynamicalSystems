import VersoManual

import DynamicalSystems.InputOutput.Dissipative
import DynamicalSystems.InputOutput.FiniteGain

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

#doc (Manual) "Input-output analysis" =>

In the previous section, we investigated stability of dynamical systems. In applications however,
we are interested in the following setting: we have have an input function that feeds into the ODE
and we extract an output from the state.

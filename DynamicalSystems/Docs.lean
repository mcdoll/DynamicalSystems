import VersoManual
import DynamicalSystems.Stability

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.style.setOption false
set_option linter.hashCommand false

set_option pp.rawOnError true

#doc (Manual) "Nonlinear dynamical systems & control theory" =>

%%%
authors := ["Moritz Doll", "Iman Shames"]
%%%

test {lean}`Filter.IsStableOn`

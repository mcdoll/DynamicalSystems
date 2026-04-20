import VersoManual
import DynamicalSystems.Stability.Documentation
import DynamicalSystems.Mathlib.Analysis.ODE.Documentation

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

This repository develops the mathematical foundations of nonlinear dynamical systems and control
theory.

{include 1 DynamicalSystems.Mathlib.Analysis.ODE.Documentation}
{include 1 DynamicalSystems.Stability.Documentation}

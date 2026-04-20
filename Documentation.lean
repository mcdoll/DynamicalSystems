import VersoManual
import DynamicalSystems.Documentation

open Verso.Genre Manual

def main := manualMain (%doc DynamicalSystems.Documentation) (options := ["--output", "html"])

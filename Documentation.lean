import VersoManual
import DynamicalSystems.Docs

open Verso.Genre Manual

def main := manualMain (%doc DynamicalSystems.Docs) (options := ["--output", "html"])

import VersoManual
import VersoBlueprint.PreviewManifest
import Probability.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc Probability.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)

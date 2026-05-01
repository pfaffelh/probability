import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Probability.Chapters.Introduction
import Probability.Chapters.DiscreteMeasure

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Probability Blueprint" =>

This Blueprint describes results in probability theory formalized in Lean and
Mathlib. Each chapter pairs informal mathematical exposition with links to the
corresponding formal declarations.

{include 0 Probability.Chapters.Introduction}

{include 0 Probability.Chapters.DiscreteMeasure}

{blueprint_graph}
{blueprint_summary}

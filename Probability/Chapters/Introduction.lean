import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>

:::group "probability_basics"
Foundational notions for probability spaces in Mathlib.
:::

:::author "project_author" (name := "Peter Pfaffelhuber")
:::

:::definition "probability_measure" (parent := "probability_basics")
A *probability measure* on a measurable space $`(\Omega, \mathcal{F})` is a
measure $`\mathbb{P}` satisfying $`\mathbb{P}(\Omega) = 1`. In Mathlib this is
captured by the typeclass `MeasureTheory.IsProbabilityMeasure`.
:::

:::theorem "prob_measure_univ" (parent := "probability_basics") (lean := "MeasureTheory.measure_univ") (tags := "starter, foundations") (effort := "small")
For every probability measure $`\mathbb{P}` on $`\Omega`,
$`\mathbb{P}(\Omega) = 1`. This is the defining property of
{uses "probability_measure"}[].
:::

:::proof "prob_measure_univ"
Direct from the definition of `IsProbabilityMeasure`. The Mathlib lemma
`MeasureTheory.measure_univ` provides this fact.
:::

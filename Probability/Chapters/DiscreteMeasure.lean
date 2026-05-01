import Verso
import VersoManual
import VersoBlueprint

import Probability.DiscreteMeasure.Basic
import Probability.DiscreteMeasure.Monad
import Probability.DiscreteMeasure.Sequence
import Probability.DiscreteMeasure.Uniform
import Probability.DiscreteMeasure.Bernoulli
import Probability.DiscreteMeasure.Binomial
import Probability.DiscreteMeasure.Multinomial
import Probability.DiscreteMeasure.Hypergeometric

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Discrete measures" =>

:::group "discrete_measure"
A `DiscreteMeasure α` is parametrised by a weight function $`w : α \to \mathbb{R}_{\geq 0}^{\infty}`,
and induces a `Measure α` as the weighted sum of Dirac masses
$`\mu_w = \sum_{a \in \alpha} w(a)\, \delta_a`. This setup is an alternative to Mathlib's `PMF`:
the coercion to `Measure` is available from the start, so the standard `Measure` library
(integration, `map`, `bind`, `dirac`) applies directly.
:::

:::definition "discrete_measure" (parent := "discrete_measure")
A *discrete measure* on a type $`α` is given by a weight function
$`w : α \to \mathbb{R}_{\geq 0}^{\infty}`. Given a measurable space structure on $`α`,
the associated measure is
$$`\mu_w(A) = \sum_{a \in α} w(a)\, \delta_a(A).`
:::

:::theorem "dm_to_measure_singleton" (parent := "discrete_measure") (lean := "MeasureTheory.DiscreteMeasure.toMeasure_apply_singleton") (effort := "small")
For every $`a \in α`, $`\mu_w(\{a\}) = w(a)`.
:::

:::theorem "dm_additive" (parent := "discrete_measure") (lean := "MeasureTheory.DiscreteMeasure.toMeasure_additive") (effort := "medium")
The induced measure $`\mu_w` is additive over arbitrary (not just countable) pairwise disjoint
unions of measurable sets: for any family $`(s_d)_{d \in D}` indexed by an arbitrary type $`D`
with the $`s_d` measurable and pairwise disjoint, and $`\bigcup_d s_d` measurable,
$$`\mu_w\Bigl(\bigcup_{d \in D} s_d\Bigr) = \sum_{d \in D} \mu_w(s_d).`
:::

:::theorem "dm_to_measure_injective" (parent := "discrete_measure") (lean := "MeasureTheory.DiscreteMeasure.toMeasure_injective") (effort := "small")
Under `MeasurableSingletonClass α`, the coercion `DiscreteMeasure α → Measure α` is injective.
:::

:::theorem "dm_isProbabilityMeasure_iff" (parent := "discrete_measure") (lean := "MeasureTheory.DiscreteMeasure.isProbabilityMeasure_iff_tsumOne") (effort := "small")
The induced measure $`\mu_w` is a probability measure if and only if $`\sum_a w(a) = 1`.
:::

:::theorem "dm_support_countable" (parent := "discrete_measure") (lean := "MeasureTheory.DiscreteMeasure.support_countable") (effort := "small")
If $`\mu_w` is finite, then the support of the weight function $`w` is countable.
:::

:::group "discrete_measure_monad"
`DiscreteMeasure` carries a lawful monad structure, with `pure`, `bind`, `map`, `join`, and `seq`.
This enables `do`-notation when describing distributions built from simpler ones.
:::

:::definition "dm_pure" (parent := "discrete_measure_monad")
The unit `pure : α → DiscreteMeasure α` puts mass $`1` at a single point: `pure a` has weight
$`\mathbf{1}_{\{a\}}`. Its associated measure is `Measure.dirac a`.
:::

:::definition "dm_map" (parent := "discrete_measure_monad")
The functor action `map : (α → β) → DiscreteMeasure α → DiscreteMeasure β` pushes the weight
forward along $`g`: $`(\text{map}\ g\ \mu)(b) = \sum_{a \in g^{-1}\{b\}} \mu(a)`.
:::

:::definition "dm_bind" (parent := "discrete_measure_monad")
The bind `bind : DiscreteMeasure α → (α → DiscreteMeasure β) → DiscreteMeasure β` is the discrete
analogue of conditional sampling: $`(\mu \gg\!= g)(b) = \sum_{a \in α} \mu(a) \cdot g(a)(b)`.
It coincides with `Measure.bind` after coercing to `Measure`.
:::

:::theorem "dm_hasSum_bind" (parent := "discrete_measure_monad") (lean := "MeasureTheory.DiscreteMeasure.hasSum_bind") (effort := "medium")
If $`\mu` is a probability measure (i.e. $`\sum_a \mu(a) = 1`) and each $`g(a)` (for $`a` in the
support of $`\mu`) is a probability measure, then so is $`\mu \gg\!= g`.
:::

:::group "iid_sequence"
The iid-sequence construction takes a `DiscreteMeasure α` and a length $`n` and returns the
distribution on `List α` of $`n` independent draws.
:::

:::definition "dm_iidSequence" (parent := "iid_sequence")
For $`\mu : \text{DiscreteMeasure}\ α` and $`n \in \mathbb{N}`, the iid sequence
$`\text{iidSequence}\ n\ \mu` is the distribution on `List α` of length-$`n` independent samples
from $`\mu`. It is defined by the monadic `sequence` of $`n` copies of $`\mu`.
:::

:::theorem "dm_iidSequence_apply" (parent := "iid_sequence") (lean := "MeasureTheory.DiscreteMeasure.iidSequence_apply") (effort := "small")
For a list $`l : \text{List}\ α` of length $`n`,
$$`(\text{iidSequence}\ n\ \mu)(l) = \prod_{i < n} \mu(l_i).`
:::

:::group "uniform_distribution"
The uniform distribution on a nonempty finite subset.
:::

:::definition "dm_uniformOfFinset" (parent := "uniform_distribution")
For a nonempty `Finset s : Finset ι`, $`\text{uniformOfFinset}\ s` is the discrete measure with
weight $`(\#s)^{-1}` on every $`i \in s` and weight $`0` outside.
:::

:::theorem "dm_uniformOfFinset_apply_toMeasure" (parent := "uniform_distribution") (lean := "MeasureTheory.DiscreteMeasure.uniformOfFinset_apply_toMeasure") (effort := "small")
For a nonempty Finset $`s` and a measurable set $`t`,
$$`(\text{uniformOfFinset}\ s)(t) = \frac{\#(s \cap t)}{\#s}.`
:::

:::group "bernoulli"
The Bernoulli distribution on `Bool` with success probability $`p`.
:::

:::definition "dm_coin" (parent := "bernoulli")
For $`p \in [0,1]`, $`\text{coin}\ p : \text{DiscreteMeasure}\ \text{Bool}` puts weight $`p` on
`true` and weight $`1 - p` on `false`. {uses "discrete_measure"}[]
:::

:::theorem "dm_isProbabilityMeasure_coin" (parent := "bernoulli") (lean := "MeasureTheory.DiscreteMeasure.hasSum_coin") (effort := "small")
$`\text{coin}\ p` is a probability measure: $`p + (1-p) = 1`. {uses "dm_isProbabilityMeasure_iff"}[]
:::

:::theorem "dm_twoCoins_and_eq_coin" (parent := "bernoulli") (lean := "MeasureTheory.DiscreteMeasure.twoCoins_and_eq_coin") (effort := "small")
The conjunction of two independent coins is again a coin:
$$`\text{Bool.and} \langle \text{coin}\ p, \text{coin}\ q \rangle = \text{coin}\ (p \cdot q).`
:::

:::group "binomial"
The binomial distribution.
:::

:::definition "dm_binom" (parent := "binomial")
For $`p \in [0,1]` and $`n \in \mathbb{N}`, $`\text{binom}\ p\ n : \text{DiscreteMeasure}\ \mathbb{N}`
is the distribution of the number of successes in $`n` independent Bernoulli$`(p)` trials. It is
defined inductively: $`\text{binom}\ p\ 0 = \text{pure}\ 0`, and
$$`\text{binom}\ p\ (n+1) = \text{coin}\ p \gg\!= \lambda X.\ \text{binom}\ p\ n \gg\!= \lambda Y.\ \text{pure}\ (\mathbf{1}\{X\} + Y).`
{uses "dm_coin"}[]{uses "dm_bind"}[]
:::

:::theorem "dm_binom_eq_count_true" (parent := "binomial") (lean := "MeasureTheory.DiscreteMeasure.binom_eq_count_true") (effort := "medium")
$`\text{binom}\ p\ n` equals the pushforward of $`\text{iidSequence}\ n\ (\text{coin}\ p)` under
`List.count true`. {uses "dm_iidSequence"}[]
:::

:::theorem "dm_binom_formula" (parent := "binomial") (lean := "MeasureTheory.DiscreteMeasure.binom_formula") (effort := "medium")
The closed form: for $`p \in [0,1]` and $`n, k \in \mathbb{N}`,
$$`\text{binom}\ p\ n\ k = \binom{n}{k}\, p^k\, (1-p)^{n-k}.`
{uses "dm_binom_eq_count_true"}[]
:::

:::group "multinomial"
The multinomial distribution generalizes the binomial: the underlying single-trial law is now an
arbitrary `DiscreteMeasure α` rather than `coin p`, and the result is the count function
$`α \to \mathbb{N}` recording how many of the $`n` trials produced each value.
:::

:::definition "dm_multinom" (parent := "multinomial")
For $`\mu : \text{DiscreteMeasure}\ α` (with `[DecidableEq α]`) and $`n \in \mathbb{N}`,
$`\text{multinom}\ \mu\ n : \text{DiscreteMeasure}\ (α \to \mathbb{N})` is defined inductively:
$`\text{multinom}\ \mu\ 0 = \text{pure}\ 0`, and
$$`\text{multinom}\ \mu\ (n+1) = \mu \gg\!= \lambda X.\ \text{multinom}\ \mu\ n \gg\!= \lambda Y.\ \text{pure}\ (Y + \mathbf{1}_{\{X\}}).`
{uses "dm_bind"}[]
:::

:::theorem "dm_multinom_eq_count" (parent := "multinomial") (lean := "MeasureTheory.DiscreteMeasure.multinom_eq_count") (effort := "medium")
$`\text{multinom}\ \mu\ n` is the pushforward of $`\text{iidSequence}\ n\ \mu` under the
count map $`l \mapsto (a \mapsto \#\{i < n : l_i = a\})`. {uses "dm_iidSequence"}[]
:::

:::group "hypergeometric"
The (multi-color) hypergeometric distribution: drawing $`n` balls without replacement from an
urn with finitely many colors, recording the per-color counts.
:::

:::definition "urn" (parent := "hypergeometric")
An *urn* indexed by a `Fintype ι` of colors is a function `card : ι → ℕ` giving the number of
balls of each color $`i`. The total number of balls is $`N = \sum_i \text{card}(i)`.
:::

:::definition "dm_hypergeometric" (parent := "hypergeometric")
Given an urn $`u` and $`n \leq N`, the hypergeometric distribution
$`\text{hypergeometric}\ u\ n : \text{DiscreteMeasure}\ (ι \to \mathbb{N})` is the law of the
per-color count function obtained by drawing $`n` balls uniformly without replacement from $`u`.
{uses "urn"}[]{uses "dm_uniformOfFinset"}[]
:::

:::theorem "dm_hypergeometric_weight" (parent := "hypergeometric") (lean := "MeasureTheory.DiscreteMeasure.hypergeometric_weight") (effort := "medium")
For $`m : ι \to \mathbb{N}`, with $`n = \sum_i m(i)`,
$$`(\text{hypergeometric}\ u\ n)(m) = \binom{N}{n}^{-1} \prod_{i \in ι} \binom{\text{card}(i)}{m(i)},`
where $`N = \sum_i \text{card}(i)`.
{uses "dm_hypergeometric"}[]
:::

:::theorem "dm_hypergeometricBool_weight" (parent := "hypergeometric") (lean := "MeasureTheory.DiscreteMeasure.hypergeometricBool_weight") (effort := "small")
The classical two-color case: for an urn $`u : \text{urn}\ \text{Bool}` and $`k, l \in \mathbb{N}`,
$$`(\text{hypergeometric}\ u\ (k+l))(k, l) = \binom{N_T + N_F}{k+l}^{-1} \binom{N_T}{k}\binom{N_F}{l},`
where $`N_T = u.\text{card}\ \text{true}`, $`N_F = u.\text{card}\ \text{false}`.
{uses "dm_hypergeometric_weight"}[]
:::

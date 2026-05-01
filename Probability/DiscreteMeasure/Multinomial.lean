/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Bernoulli
import Probability.DiscreteMeasure.Sequence

/-!
# DiscreteMeasure: Multinomial distribution

We define the multinomial distribution `multinom μ n` as a `DiscreteMeasure (α → ℕ)`,
where for `f : α → ℕ`, the value `multinom μ n f` is the probability that, after `n`
independent trials with distribution `μ`, the number of trials with value `a` is
`f a` for each `a : α`.

The definition is inductive: `multinom μ 0 = pure 0` (the constant zero count function)
and `multinom μ (n+1) = μ >>= fun X => multinom μ n >>= fun Y => pure (Y + 𝟙_X)`,
where `𝟙_X` is the function that is `1` at `X` and `0` elsewhere.

This is the natural generalization of `binom`, replacing the Bernoulli `coin p` by an
arbitrary `DiscreteMeasure α`.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section multinom

variable {α : Type*} [DecidableEq α]

/-- The multinomial distribution: after `n` independent trials with distribution `μ`,
the count function `α → ℕ` records how many trials produced each value. -/
noncomputable def multinom (μ : DiscreteMeasure α) : ℕ → DiscreteMeasure (α → ℕ)
  | 0 => pure 0
  | n + 1 => do
    let X ← μ
    let Y ← multinom μ n
    pure (Y + Pi.single X 1)

@[simp]
lemma multinom_zero (μ : DiscreteMeasure α) : multinom μ 0 = pure 0 := rfl

lemma multinom_succ (μ : DiscreteMeasure α) (n : ℕ) :
    multinom μ (n + 1) = μ >>= fun X => multinom μ n >>= fun Y =>
      pure (Y + Pi.single X 1) := rfl

lemma hasSum_multinom (μ : DiscreteMeasure α) (hμ : HasSum μ 1) (n : ℕ) :
    HasSum (multinom μ n) 1 := by
  induction n with
  | zero => exact hasSum_pure 0
  | succ n hn =>
    exact hasSum_bind hμ (fun a _ => hasSum_bind hn (fun b _ => hasSum_pure _))

lemma isProbabilityMeasure_multinom (μ : DiscreteMeasure α) (hμ : HasSum μ 1) (n : ℕ) :
    letI : MeasurableSpace (α → ℕ) := ⊤
    IsProbabilityMeasure (multinom μ n).toMeasure := by
  letI : MeasurableSpace (α → ℕ) := ⊤
  exact isProbabilityMeasure_iff_hasSum.mpr (hasSum_multinom μ hμ n)

lemma multinom_seq (μ : DiscreteMeasure α) (n : ℕ) :
    multinom μ (n + 1) =
      (fun a y => y + Pi.single a 1) <$> μ <*> multinom μ n := by
  simp_rw [← seq_eq_seq, ← map_eq_map, multinom, ← bind_eq_bind, bind_map_eq_seq,
    ← bind_pure_comp, bind_bind, pure_bind]

/-- Pointwise: prepending `X` to `L` increments the count at `X` by one. -/
private lemma count_cons_eq_add_single (X : α) (L : List α) :
    (fun a => (X :: L).count a) = (fun a => L.count a) + Pi.single X 1 := by
  funext a
  rw [Pi.add_apply, Pi.single_apply, List.count_cons]
  by_cases h : a = X
  · subst h
    simp
  · have h' : ¬X = a := fun he => h he.symm
    simp [h, h']

/-- The multinomial distribution coincides with mapping the iid sample to its count function. -/
theorem multinom_eq_count (μ : DiscreteMeasure α) (n : ℕ) :
    multinom μ n = (iidSequence n μ).map (fun l a => l.count a) := by
  induction n with
  | zero => simp; rfl
  | succ n hn =>
    rw [multinom_succ, hn, ← iidSequence_cons]
    simp only [← bind_eq_bind]
    rw [DiscreteMeasure.map_bind]
    refine congrArg μ.bind (funext fun X => ?_)
    rw [DiscreteMeasure.bind_map, DiscreteMeasure.map_bind]
    refine congrArg (iidSequence n μ).bind (funext fun L => ?_)
    rw [map_pure]
    refine congrArg pure ?_
    rw [count_cons_eq_add_single]

end multinom

end DiscreteMeasure

end MeasureTheory

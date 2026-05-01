/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Monad
import Probability.DiscreteMeasure.Sequence

/-!
# DiscreteMeasure: Bernoulli distribution (coin) and uniform distribution

We define `coin p` as the Bernoulli distribution with parameter `p : unitInterval`, i.e., the
`DiscreteMeasure Bool` with `coin p true = ENNReal.ofReal p` and `coin p false = ENNReal.ofReal (1 - p)`.
We prove basic properties, including that it is a probability measure.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section coin

open Bool ENNReal NNReal unitInterval

noncomputable def coin (p : unitInterval) : DiscreteMeasure Bool where weight := fun
  | true => ENNReal.ofReal p
  | false => ENNReal.ofReal (σ p)

lemma coin_apply (p : unitInterval) (b : Bool) : (coin p) b = if b then ENNReal.ofReal p else ENNReal.ofReal (symm p) := by
  by_cases h : b <;> simp only [h] <;> rfl

lemma coin_apply_true (p : unitInterval) : (coin p) true = ENNReal.ofReal p := by
  rfl

lemma coin_apply_false (p : unitInterval) : (coin p) false = ENNReal.ofReal (σ p) := by
  rfl

@[simp]
lemma unitInterval.sum_symm_self {p : unitInterval} :
ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr p.prop.2) p.prop.1]
  simp [sub_add_cancel]

lemma hasSum_coin (p : unitInterval) : HasSum (coin p) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable, tsum_bool]
  rw [coin_apply, coin_apply]
  simp

instance isProbabilityMeasure_coin (p : unitInterval) : IsProbabilityMeasure (coin p).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr <| hasSum_coin p

lemma lintegral_coin_id (p : unitInterval) (g : Bool → ℝ≥0∞) : ∫⁻ (a : Bool), (g a) ∂ (coin p).toMeasure = ENNReal.ofReal (1 - p) * (g false) + ENNReal.ofReal p * (g true) := by
  rw [lintegral_eq_toMeasure]
  rw [tsum_bool, coin_apply, coin_apply]
  simp

lemma lintegral_coin (p : unitInterval) : ∫⁻ (a : Bool), ({true} : Set Bool).indicator 1 a ∂ (coin p).toMeasure = ENNReal.ofReal p := by
  rw [lintegral_coin_id]
  simp

lemma Bool_hasSum_not (μ : DiscreteMeasure Bool) (hμ : HasSum μ 1) (b : Bool) : μ (!b) = 1 - μ b := by
  refine ENNReal.eq_sub_of_add_eq' one_ne_top ?_
  rw [Summable.hasSum_iff ENNReal.summable, tsum_bool] at hμ
  cases' b with h
  · rw [add_comm] ; simp [hμ]
  · simp [hμ]

lemma Bool_ext {μ ν : DiscreteMeasure Bool} (hμ : HasSum μ 1) (hν : HasSum ν 1) (b : Bool) (h : μ b = ν b) : μ = ν := by
  ext a
  cases h' : decide (b = a)
  · rw [decide_eq_false_iff_not, ← ne_eq b a, ← not_eq] at h'
    rw [← h', Bool_hasSum_not μ hμ b, Bool_hasSum_not ν hν b, h]
  · simp only [decide_eq_true_eq] at h'
    rw [← h', h]

lemma coin_not' (p : unitInterval) : (coin p).map not = coin (unitInterval.symm p) := by
  apply Bool_ext (hasSum_map (hasSum_coin p) not) (hasSum_coin (unitInterval.symm p)) true
  change map not (coin p) true = _
  rw [coin_apply_true, map_eq_of_inj (coin p) not Bool.not_injective false true Bool.not_false]
  exact coin_apply_false p

/-- The only list of given length with `List.and` equal to `true` is the constant `true` list. -/
private lemma list_all_true_of_length {l : List Bool} {n : ℕ}
    (hlen : l.length = n) (h : List.and l = true) : l = List.replicate n true := by
  induction l generalizing n with
  | nil =>
    cases hlen
    rfl
  | cons b rest ih =>
    match n with
    | 0 => simp at hlen
    | k + 1 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.and_cons, Bool.and_eq_true] at h
      rw [List.replicate_succ, ih hlen h.2, h.1]

/-- `ENNReal.ofReal` distributes over `List.prod` for unitInterval values. -/
private lemma list_map_ofReal_prod (p : List unitInterval) :
    (p.map (fun q : unitInterval => ENNReal.ofReal ↑q)).prod = ENNReal.ofReal ↑p.prod := by
  induction p with
  | nil => simp
  | cons q rest ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, ← ENNReal.ofReal_mul q.2.1]
    rfl

lemma sequence_coin (p : List unitInterval) : map List.and (sequence (p.map coin)) = coin p.prod := by
  letI : MeasurableSpace (List Bool) := ⊤
  apply Bool_ext _ (hasSum_coin p.prod) true
  · rw [coin_apply_true, map_apply (hg := by measurability)]
    rw [toMeasure_apply_eq_of_inter_support_eq (μ := sequence (p.map coin))
        (s := List.and ⁻¹' {true}) (t := {List.replicate p.length true})
        (u := {l : List Bool | l.length = (p.map coin).length})
        (by measurability) (by measurability) (by measurability) sequence_support ?_]
    · rw [toMeasure_apply_singleton, ← List.length_map, sequence_apply_of_replicate, List.map_map]
      change (p.map (fun q : unitInterval => ENNReal.ofReal ↑q)).prod = _
      exact list_map_ofReal_prod p
    · ext l
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
        List.length_map]
      refine ⟨fun ⟨hand, hlen⟩ => ⟨list_all_true_of_length hlen hand, hlen⟩,
              fun ⟨heq, hlen⟩ => ⟨?_, hlen⟩⟩
      rw [heq]
      induction p.length with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, ih]
  · apply hasSum_map (hasSum_sequence (fun i => ?_)) List.and
    rw [List.get_eq_getElem, List.getElem_map]
    apply hasSum_coin _

lemma twoCoins_and_eq_coin (p q : unitInterval) :
    Bool.and <$> (coin p) <*> (coin q) = coin (p * q) := by
  simp [monad_norm]
  refine Bool_ext ?_ (hasSum_coin (p * q)) true ?_
  · -- HasSum for the LHS bind expression
    exact hasSum_bind (hasSum_coin p) (fun a _ =>
      hasSum_bind (hasSum_coin q) (fun b _ => hasSum_pure _))
  · -- value at `true`
    simp_rw [← bind_eq_bind, bind_apply, tsum_bool, coin_apply_false, coin_apply_true,
      ← pure_eq_pure, Function.comp_apply, pure_apply, Set.indicator]
    simp [ENNReal.ofReal_mul p.2.1]

lemma twoCoins_or_eq_coin (p q : unitInterval) :
    Bool.or <$> (coin p) <*> (coin q) = coin (σ ((σ p) * (σ q))) := by
  simp [monad_norm]
  refine Bool_ext ?_ (hasSum_coin _) false ?_
  · -- HasSum for the LHS bind expression
    exact hasSum_bind (hasSum_coin p) (fun a _ =>
      hasSum_bind (hasSum_coin q) (fun b _ => hasSum_pure _))
  · -- value at `false`
    simp_rw [← bind_eq_bind, bind_apply, tsum_bool, coin_apply_false, coin_apply_true,
      ← pure_eq_pure, Function.comp_apply, pure_apply, Set.indicator]
    simp [ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]


end coin

end DiscreteMeasure

end MeasureTheory

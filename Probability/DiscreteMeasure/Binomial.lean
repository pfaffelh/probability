/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Bernoulli
import Probability.DiscreteMeasure.Sequence

/-!
# DiscreteMeasure: Binomial distribution

We define the binomial distribution `binom p n` as a `DiscreteMeasure ℕ`,
where `binom p n k` is the probability of getting exactly `k` successes in `n`
independent coin flips with success probability `p`.

The definition is inductive: `binom p 0 = pure 0` and
`binom p (n+1) = coin p >>= fun X => binom p n >>= fun Y => pure (Bool.toNat X + Y)`.

We prove the classical binomial formula:
`binom p n k = p ^ k * (1 - p) ^ (n - k) * (n.choose k)`.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset unitInterval

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section binom

/-- The binomial distribution with parameters `p` and `n`, as a `DiscreteMeasure ℕ`. -/
noncomputable def binom (p : unitInterval) : ℕ → DiscreteMeasure ℕ
  | 0 => pure 0
  | n + 1 => do
    let X ← coin p
    let Y ← binom p n
    pure (X.toNat + Y)

@[simp]
lemma binom_zero (p : unitInterval) : binom p 0 = pure 0 := rfl

lemma binom_succ (p : unitInterval) (n : ℕ) :
    binom p (n + 1) = (coin p) >>= fun X => binom p n >>= fun Y => pure (X.toNat + Y) := rfl

lemma hasSum_binom (p : unitInterval) (n : ℕ) : HasSum (binom p n) 1 := by
  induction n with
  | zero => exact hasSum_pure 0
  | succ n hn =>
    exact hasSum_bind (hasSum_coin p) (fun a _ => hasSum_bind hn (fun b _ => hasSum_pure _))

lemma isProbabilityMeasure_binom (p : unitInterval) (n : ℕ) :
    IsProbabilityMeasure (binom p n).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr (hasSum_binom p n)

lemma binom_seq (p : unitInterval) (n : ℕ) : binom p (n + 1) =
(fun b x ↦ b.toNat + x) <$> (coin p) <*> (binom p n) := by
  simp_rw [← seq_eq_seq, ← map_eq_map, binom, ← bind_eq_bind, bind_map_eq_seq, ← bind_pure_comp, bind_bind, pure_bind]

theorem binom_eq_count_true (p : unitInterval) (n : ℕ) : binom p n = (iidSequence n (coin p)).map (List.count true) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [binom_seq, hn, ← iidSequence_cons]
    simp only [monad_norm]
    simp [Bool.toNat, Bool.cond_eq_ite, add_comm,
      List.count_cons]

/-- `binom p n k = 0` when `k > n`, since we can't get more successes than trials. -/
lemma binom_eq_zero_of_gt (p : unitInterval) (n k : ℕ) (hk : n < k) : binom p n k = 0 := by
  letI : MeasurableSpace (List Bool) := ⊤
  rw [binom_eq_count_true,  map_apply (hg := by measurability), iidSequence, toMeasure_apply_eq_zero_iff (hs := by measurability)]
  apply Set.disjoint_of_subset sequence_support (fun ⦃a⦄ a_1 => a_1)
  grind

open Finset

-- #34702
lemma List.card_idxsOf_toFinset_eq_count {α : Type*} [BEq α] (l : List α) (a : α) :
    (l.idxsOf a).toFinset.card = l.count a := by
  rw [List.card_toFinset, List.Nodup.dedup List.nodup_idxsOf, List.length_idxsOf]

-- #34702
lemma List.count_ofFn_eq_card [DecidableEq α] (n : ℕ) (f : Fin n → α) (a : α)
    [DecidablePred fun i ↦ f i = a] :
    List.count a (List.ofFn f) = Finset.card {i | f i = a} := by
  rw [← List.card_idxsOf_toFinset_eq_count]
  let s := {i | f i = a}.toFinset
  refine card_bij (fun b hb ↦ ⟨b, ?_⟩) (fun c hc ↦ ?_) (fun d hd1 hd2 hd3 ↦ ?_) (fun e he ↦ ?_)
  · aesop
  · simp only [List.mem_toFinset, List.mem_idxsOf_iff_getElem_sub_pos, Nat.zero_le, Nat.sub_zero,
    List.getElem_ofFn, beq_iff_eq, List.length_ofFn, true_and] at hc
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact Exists.elim hc fun a_1 a ↦ a
  · simp
  · aesop

-- #34702
/-- For some `Fintype ι`, there is (computably) a bijection `ι → Bool` and `Finset ι` by using
`s : Finset ι` as the set where the `f : ι → Bool` is `true`. -/
def Equiv.fnBool_finset {ι : Type*} [DecidableEq ι] [Fintype ι] : (ι → Bool) ≃ (Finset ι) where
  toFun := fun f ↦ Finset.univ.filter (f · = true)
  invFun := fun s i ↦ decide (i ∈ s)
  left_inv := fun l ↦ by simp
  right_inv := fun l ↦ by simp

-- #34702
lemma Equiv_fnBool_finset_mem_powersetCard_iff  {ι : Type*} [DecidableEq ι] [Fintype ι] (k : ℕ) (f : ι → Bool) :
    #{i | f i = true} = k ↔ (Equiv.fnBool_finset) f ∈ powersetCard k univ := by
  simp [Equiv.fnBool_finset]

-- #34702
/-- For some `Fintype ι`, the number of maps `f : ι → Bool` with `#{i | f i} = k` equals `n.choose k`. -/
lemma card_fnBool {ι : Type*} [DecidableEq ι] [Fintype ι] {k : ℕ} : #{ f : ι → Bool | #{i | f i} = k } = (univ : Finset ι).card.choose k := by
  rw [← card_powersetCard k (univ : Finset ι)]
  apply card_equiv (Equiv.fnBool_finset) (fun i ↦ ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact Equiv_fnBool_finset_mem_powersetCard_iff k i

-- #34702
lemma card_listVector_card {k n : ℕ} :
    #{v : List.Vector Bool n | v.toList.count true = k} = n.choose k := by
  rw [← card_fin n, ← card_fnBool, card_fin n]
  apply card_equiv (Equiv.vectorEquivFin _ n) (fun v ↦ ?_)
  simp only [mem_filter, mem_univ, true_and, Equiv.vectorEquivFin, Equiv.coe_fn_mk]
  refine ⟨fun h ↦ ?_,fun h ↦ ?_⟩ <;> rw [← h, ← List.count_ofFn_eq_card _ _ true] <;> congr <;>
  rw [← List.ofFn_get (l :=  v.toList)] <;> aesop



/-- The number of boolean lists of length `n` with exactly `k` trues is `n.choose k`. -/
lemma card_boolList_count {k n : ℕ} :
    ENat.card ↑({l : List Bool | l.length = n} ∩ {l | List.count true l = k}) = n.choose k := by
  have e1 : ↑({l : List Bool | l.length = n} ∩ {l | List.count true l = k}) ≃
      {v : List.Vector Bool n | v.toList.count true = k} :=
    { toFun := fun ⟨l, hl, hk⟩ => ⟨⟨l, hl⟩, hk⟩
      invFun := fun ⟨⟨l, hl⟩, hk⟩ => ⟨l, hl, hk⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  simp_rw [ENat.card_congr e1, ENat.card_eq_coe_fintype_card, Fintype.card_subtype, Set.mem_setOf_eq, ← card_listVector_card]

instance : MeasurableSpace (List Bool) := ⊤

theorem binom_eq_iidSequence'' (p : unitInterval) (n : ℕ) (k : ℕ) :
    binom p n k =
    (iidSequence n (coin p)).toMeasure {l | l.count true = k} := by
  rw [binom_eq_count_true, map_apply (hg := by measurability)]
  rfl

theorem binom_eq_iidSequence' (p : unitInterval) (n : ℕ) (k : ℕ) :
    binom p n k =
    (iidSequence n (coin p)).toMeasure ({l | l.length = n} ∩ {l | l.count true = k}) := by
  have h : n = List.length (List.replicate n (coin p)) := by
    rw [List.length_replicate]
  rw [binom_eq_iidSequence'', Set.inter_comm]
  rw [toMeasure_apply_inter_support (hs := by measurability) (hu := by measurability), iidSequence]
  apply h ▸ sequence_support

/-- The binomial formula: `binom p n k = C(n,k) * p^k * (1-p)^(n-k)`. -/
theorem binom_formula (p : unitInterval) (n k : ℕ) :
    binom p n k = (ENNReal.ofReal p) ^ k * (ENNReal.ofReal (symm p)) ^ (n - k) * (Nat.choose n k) := by
  have h : ∀ (a : ↑({l : List Bool | l.length = n} ∩ {l | List.count true l = k})),
      iidSequence n (coin p) a.val = iidSequence a.val.length (coin p) a.val ∧
      List.count true a.val = k ∧ List.count false a.val = n - k := by
    rintro ⟨a, ⟨h1, h2⟩⟩; grind
  rw [binom_eq_iidSequence', toMeasure_apply_eq_tsum_subtype (hs := by measurability)]
  simp_rw [mul_comm (a:= ENNReal.ofReal ↑p ^ k), h, iidSequence_apply₂, tprod_bool,
    coin_apply_false, coin_apply_true, h, ENNReal.tsum_const, card_boolList_count,
    mul_comm (ENat.toENNReal _), ENat.toENNReal_coe]

end binom

end DiscreteMeasure

end MeasureTheory

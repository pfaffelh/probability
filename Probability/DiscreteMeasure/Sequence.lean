/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Monad

/-!
# DiscreteMeasure: Sequences and i.i.d. sequences

We define `sequence` for `DiscreteMeasure`s on `List`s, and `iidSequence` for
independent and identically distributed sequences. We prove formulas for
evaluating these at specific vectors.
-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

variable {α : Type*}

section misc

lemma prod_zipWith_cons (f : DiscreteMeasure α) (g : List (DiscreteMeasure α)) (a : α) (l : List α) : List.prod ((f::g).zipWith (·.weight ·) (a::l)) = f a * List.prod (g.zipWith (· ·) l) := by
  rfl

end misc

namespace MeasureTheory

namespace DiscreteMeasure

section sequence

-- MF
lemma cons_map_seq_apply (μs : DiscreteMeasure (List α)) (ν : DiscreteMeasure α) (l : List α): (List.cons <$> ν <*> μs) l = ∑' (a' : α), ν a' * ∑' (l' : List α), μs l' * pure (a' :: l') l := by
  simp [monad_norm]
  rw [← bind_eq_bind, bind_apply]
  simp_rw [← bind_eq_bind, bind_apply]
  simp_rw [← pure_eq_pure, comp_apply]

lemma pure_cons_apply_cons [DecidableEq α] (a a' : α) (l l' : List α) : pure (a' :: l') (a :: l) = (pure a' a) * (pure l' l) := by
  repeat rw [pure_apply, Set.indicator]
  aesop

-- MF
lemma cons_map_seq_apply_cons [DecidableEq α] (μs : DiscreteMeasure (List α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (List.cons <$> ν <*> μs) (a :: l) = ν a * (μs l) := by
  rw [cons_map_seq_apply]
  simp_rw [pure_cons_apply_cons, ← mul_assoc, pure_comm]
  conv => left; left; intro a'; right; left; intro l'; rw [mul_assoc]; right; rw [mul_comm]
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ← mul_assoc, tsum_pure]

-- MF
lemma sequence_cons_eq_seq_sequence [DecidableEq α] (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) : (sequence (ν :: μs)) = (List.cons <$> ν <*> sequence μs) := by
  rw [sequence, List.traverse_cons id]
  simp

lemma sequence_cons_apply_cons [DecidableEq α] (μs : List (DiscreteMeasure α)) (ν : DiscreteMeasure α) (l : List α) (a : α) : (sequence (ν :: μs)) (a :: l) = (ν a) * ((sequence μs) l) := by
  rw [List.sequence_cons]
  exact cons_map_seq_apply_cons (sequence μs) ν l a

@[simp]
lemma sequence_nil {α : Type u} : sequence ([] : List (DiscreteMeasure α)) = Pure.pure [] := by
  simp [sequence]

lemma sequence_apply₀ [DecidableEq α] (μs : List (DiscreteMeasure α)) (l : List α) (h : μs.length = l.length) :
    (sequence μs) l = List.prod (μs.zipWith (·.weight ·) l) := by
  induction μs generalizing l with
  | nil =>
    rw [List.length_nil, eq_comm, ← List.eq_nil_iff_length_eq_zero] at h
    subst h; simp [sequence, ← pure_eq_pure]
  | cons μ_head μ_tail h' =>
    rw [List.length_cons, eq_comm] at h
    obtain ⟨lh,lt, lht⟩ := List.exists_cons_of_length_eq_add_one h
    rw [lht]
    rw [prod_zipWith_cons]
    rw [sequence_cons_apply_cons]
    have : μ_tail.length = lt.length := by
      simpa [lht, eq_comm]using h
    congr
    exact h' lt this

lemma sequence_apply_of_length [DecidableEq α] (μs : List (DiscreteMeasure α)) (l : List α) (h : μs.length = l.length) :
    (sequence μs) l = List.prod (μs.zipWith (·.weight ·) l) :=
  sequence_apply₀ μs l h

lemma sequence_apply_of_replicate [DecidableEq α] (μs : List (DiscreteMeasure α)) (a : α) :
    (sequence μs) (List.replicate μs.length a) = (μs.map (fun m ↦ m.weight a)).prod := by
  sorry

lemma sequence_apply_of_not_length [DecidableEq α] (μs : List (DiscreteMeasure α)) (l : List α) (h : μs.length ≠ l.length) :
    (sequence μs) l = 0 := by
  induction μs generalizing l with
  | nil =>
    rw [ne_comm, List.length_nil, ← Iff.ne List.eq_nil_iff_length_eq_zero] at h
    exact pure_apply_nonself h
  | cons μ μs ih =>
    cases l with
    | nil =>
      rw [List.sequence_cons]
      simp [monad_norm]
      rw [← bind_eq_bind, bind_apply]
      apply ENNReal.tsum_eq_zero.mpr (fun a ↦ ?_); apply mul_eq_zero_of_right
      simp_rw [← bind_eq_bind, bind_apply, comp_apply]
      apply ENNReal.tsum_eq_zero.mpr (fun b ↦ ?_); apply mul_eq_zero_of_right
      apply pure_apply_nonself (by simp)
    | cons a l' =>
      rw [sequence_cons_apply_cons]
      have : μs.length ≠ l'.length := by simpa using h
      rw [ih l' this, mul_zero]

lemma sequence_support [DecidableEq α] {μs : List (DiscreteMeasure α)} :
    (sequence μs).weight.support ⊆ {l : List α | l.length = μs.length} := by
  refine support_subset_iff'.mpr (fun l hl ↦ ?_)
  rw [Set.mem_setOf_eq, eq_comm] at hl
  exact sequence_apply_of_not_length μs l hl

/-
lemma sequence_apply₁ [DecidableEq α] (μs : List (DiscreteMeasure α)) (l : List α) :
    sequence μs l = ∏ i, (List.get μs i) (List.Vector.get l i) :=
  by
  rw [sequence_apply₀]
  have h : List.Vector.zipWith (fun x1 x2 => x1 x2) μs l = List.Vector.zipWith (fun x1 x2 => x1 x2) (List.Vector.map (fun x ↦ x.weight) μs) l := by
    rw [List.Vector.ext_iff]
    simp
  rw [h, prod_zipWith]
  simp
-/

-- TODO: define marginal distributions

lemma hasSum_sequence [DecidableEq α] {μs : List (DiscreteMeasure α)} (hμ : ∀ i, HasSum (μs.get i).weight 1) : HasSum (sequence μs) 1 := by
  induction μs with
  | nil =>
    simp [sequence, ← pure_eq_pure, hasSum_pure]
  | cons μh μt μht =>
    rw [sequence_cons_eq_seq_sequence]
    simp only [map_eq_bind_pure_comp, seq_eq_bind_map, bind_assoc, comp_apply,
      LawfulMonad.pure_bind]
    have hg₀ (i : Fin μt.length) : μt[i.val] = (μh :: μt)[i.val+1] := by
      rfl
    have hg₁ : μh = (μh :: μt)[0] := by rfl
    refine hasSum_bind (hg₁ ▸ (hμ 0)) (fun a ha ↦ ?_)
    refine hasSum_bind (μht fun i ↦ ?_) (fun _ _ ↦ hasSum_pure _)
    simp only [List.length_cons, List.get_eq_getElem] at hμ
    simp only [List.get_eq_getElem]
    exact hg₀ i ▸ hμ ⟨i.val+1, Nat.add_lt_add_iff_right.mpr i.prop⟩

lemma isProbabilityMeasure_sequence_toMeasure  [MeasurableSpace (List α)] [MeasurableSingletonClass (List α)] [DecidableEq α] (μs : List (DiscreteMeasure α)) {hμ : ∀ i, HasSum (μs.get i).weight 1} : IsProbabilityMeasure (sequence μs).toMeasure := by
  exact isProbabilityMeasure_iff_hasSum.mpr <| hasSum_sequence hμ

end sequence

section iidSequence

noncomputable def iidSequence (n : ℕ) (μ : DiscreteMeasure α) : DiscreteMeasure (List α) := sequence (List.replicate n μ)

@[simp]
lemma iidSequence_zero (μ : DiscreteMeasure α) : iidSequence 0 μ = pure [] := by
  simp [iidSequence, sequence]

lemma iidSequence_apply [DecidableEq α] (μ : DiscreteMeasure α) (l : List α) :
    (iidSequence l.length μ) l = (l.map μ).prod := by
  induction l with
  | nil =>
    simp [iidSequence, sequence, ← pure_eq_pure, pure_apply_self]
  | cons h t iht =>
    rw [iidSequence] at iht
    rw [iidSequence, List.length_cons, List.replicate_succ,
    sequence_cons_apply_cons, iht, List.map_cons, List.prod_cons]

lemma iidSequence_apply₁ {μ : DiscreteMeasure α} [DecidableEq α] {l : List α} :
    iidSequence l.length μ l = (∏ a ∈ l.toFinset, (μ a) ^ (List.count a l)) := by
  rw [iidSequence_apply μ l]
  exact Finset.prod_list_map_count l μ

lemma iidSequence_apply₂ (μ : DiscreteMeasure α) [DecidableEq α] (l : List α) :
    iidSequence l.length μ l = (∏' (a : α), (μ a) ^ (List.count a l)) := by
  rw [iidSequence_apply₁]
  rw [tprod_eq_prod]
  intro b hb
  have h : List.count b l = 0 := by
    simpa [List.count_eq_zero, ← List.mem_toFinset] using hb
  rw [h, pow_zero]

lemma pure_sequence (ν : DiscreteMeasure α) : sequence [ν] = (ν.map (fun b => [b])) := by
  simp [sequence]

lemma sequence_bind (μ ν : DiscreteMeasure α) : sequence [μ, ν] = μ.bind (fun a => ν.map (fun b => [a, b])) := by
  simp [sequence, monad_norm]

lemma iidSequence_cons {n : ℕ} (ν : DiscreteMeasure α) : (ν >>= fun y => (iidSequence n ν) >>= fun x => pure (x.cons y)) = iidSequence (n+1) ν := by
  rw [iidSequence, iidSequence, List.replicate_succ, List.sequence_cons]
  simp [monad_norm]

end iidSequence

end DiscreteMeasure

end MeasureTheory

/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Monad

/-!
# DiscreteMeasure: Uniform distribution

We define `uniform` as the uniform distribution on a `Finset ι`,
where each element has weight `s.card⁻¹`.
We prove that it is a probability measure.
-/

open MeasureTheory ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

section uniformOfFinset

variable {ι : Type*} [DecidableEq ι] (s : Finset ι)

noncomputable def uniformOfFinset (_hs : s.Nonempty) : DiscreteMeasure ι where
  weight := (s : Set ι).indicator (s.card)⁻¹
  --fun i ↦ if i ∈ s then (s.card)⁻¹ else 0

@[simp]
lemma uniformOfFinset_apply (hs : s.Nonempty) (i : ι) :
    uniformOfFinset s hs i = if i ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
  show (uniformOfFinset s hs).weight i = _
  rw [uniformOfFinset]
  simp [Set.indicator_apply]

lemma uniformOfFinset_apply' (hs : s.Nonempty) (i : ι) :
    uniformOfFinset s hs i = (s : Set ι).indicator (s.card)⁻¹ i := by
  rfl

lemma uniformOfFinset_apply'' (hs : s.Nonempty) (i : ι) :
    uniformOfFinset s hs i = (s.card : ℝ≥0∞)⁻¹ * (s : Set ι).indicator 1 i := by
  simp [uniformOfFinset_apply' s hs, Set.indicator_apply, Set.indicator_apply]


lemma hasSum_uniformOfFinset (hs : s.Nonempty) : HasSum (uniformOfFinset s hs).weight 1 := by
  simp_rw [Summable.hasSum_iff ENNReal.summable, weight_eq, uniformOfFinset_apply', ← _root_.tsum_subtype]
  simp [ENNReal.mul_inv_cancel, card_ne_zero.mpr hs, ENNReal.natCast_ne_top]

lemma isProbabilityMeasure_uniformOfFinset [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    IsProbabilityMeasure (uniformOfFinset s hs).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr (hasSum_uniformOfFinset s hs)

open scoped Classical in
lemma uniformOfFinset_apply_toMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (t : Set ι) (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} * (#s : ℝ≥0∞)⁻¹ := by
  simp only [toMeasure_apply_eq_tsum_mul _ ht, uniformOfFinset_apply'', mul_assoc, ENNReal.tsum_mul_left]
  simp_rw [mul_comm, Set.indicator.mul_indicator_eq]
  rw [← _root_.tsum_subtype]
  simp [Set.indicator_apply]
  rw [Finset.filter_attach', Finset.card_map, Finset.card_attach]
  congr 3; ext x; simp only [exists_prop, mem_filter, and_self_left]

end uniformOfFinset

section uniformOfFintype

noncomputable def uniformOfFintype (ι : Type*) [Fintype ι] [Nonempty ι] : DiscreteMeasure ι :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

@[simp]
theorem uniformOfFintype_apply (i : ι) : uniformOfFintype ι i = (Fintype.card ι : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

-- example [Fintype ι] (t : Set ι) : Finset ι := by
--  exact Finset.empty

open scoped Classical in
lemma uniformOfFintype_apply_toMeasure [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (t : Set ι) (ht : MeasurableSet t) :
    (uniformOfFintype ι).toMeasure t = #t.toFinset * (Fintype.card ι : ℝ≥0∞)⁻¹ := by
  rw [uniformOfFintype, uniformOfFinset_apply_toMeasure (s := (Finset.univ : Finset ι))
    (hs := Finset.univ_nonempty) t ht, Finset.card_univ]
  congr 3
  ext x
  simp




@[simp]
theorem support_uniformOfFintype  :
    (uniformOfFintype (ι := ι)).weight.support = ⊤ :=
  Set.ext fun x => by simp

theorem mem_support_uniformOfFintype (i : ι) : i ∈ (uniformOfFintype (ι := ι)).weight.support := by simp

end uniformOfFintype


end DiscreteMeasure

end MeasureTheory

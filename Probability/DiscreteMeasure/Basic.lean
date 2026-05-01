/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib

/-!
# Discrete measures

We develop a setup for discrete (probability) measures, which is an alternative to PMFs (Probability Mass Functions). Here, a `μ : DiscreteMeasure` coerces to a sum of `dirac`s with weights given by `μ.weight : α → ℝ≥0∞`.

For the coercion to `Measure`, note that `μ : DiscreteMeasure α` is not only σ-additive, but additive; see `DiscreteMeasure.m_iUnion`.

This setup combines the following features:

* We can use the `Measure`-library right from the start (as opposed to `PMF`s). (E.g., integrating wrt a discrete Measure can use linearity in the Measure, and integrating wrt `dirac`. The proofs of the usual properties between `map`, `bind` and `join` can use their counterparts in `Measure`.)
* We establish that `DiscreteMeasure α` is a `LawfulMonad`. In particular, it allows for `do`-notation.
* It will be easier to connect `DiscreteMeasure` with `Measure` (since they coerce to measures). E.g., weak convergence of `P : ℕ → DiscreteMeasure α` to some `Measure α` is easy to formulate. (For this, we have to `trim` the `P n`s to the corresponding `MeasureableSpace α` instance.)

As one example, we have started to establish some results on `coin p`, which is a Bernoulli distribution, as well as alternative formulations for the usual binomial distribution.


ToDos:
* I could add sum to any sequence of a type which has a Sum!?

* generalize coin to any Fintype!
  * the old coin is a newCoin Bool then...
  * does binomial carry over to multinomial?
  No, the new coin is only a general DiscreteMeasure. But multinomial is generic in the sense that it can be based on any DiscreteMeasure!

* define a general thinning operation for DiscreteMeasures, and show that it preserves the class of DiscreteMeasures.

A thinning is a bind: we need `thin : α → UniInterval` and `P : DiscreteMeasure α`. Start by drawing a random variable `X` from `P`, `Y \l  coin (P X)`. If `Y = True`, return `X`, else repeat.

A mixture is a y...!?

Sums with random number of summands!

Introduce mixed Poisson! Also important for infinite divisibility!


new random variable from another DiscreteMeasure which depends on the first one. We can show that the resulting distribution is again a DiscreteMeasure. This is a generalization of the fact that the thinning of a binomial distribution is again binomial.

* multinomial
  * can the new coin be used here? (I guess so, but we have to check the details.)

geometric:
* add throw a coin, it true return 0 else return 1 + itself (is this the definition?)
* add weights are such that weight n+1 = (1 - p) * weight n, and weight 0 = p
* Thinning of a geometric distribution is geometric.

negative binomial:
* define inductively via sums of geometric!





-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

--#37060
@[to_additive]
lemma mulSupport_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ → Set α} (f : α → β)
  (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport)))
  (i : α) (j : γ) (hj : i ∈ s j) :
    (fun d ↦ (s d).mulIndicator f i).mulSupport ⊆ {j} := by
  simp only [Pairwise, Disjoint, Set.le_eq_subset, Set.subset_inter_iff,] at hs
  simp only [Set.subset_singleton_iff, mem_mulSupport, ne_eq, Set.mulIndicator_apply_eq_one,
    Classical.not_imp, and_imp]
  intro j' hj' hi
  by_contra h
  change f i ≠ 1 at hi
  rw [← mem_mulSupport] at hi
  simp_rw [← Set.singleton_subset_iff] at hs hj hj' hi
  simpa only [Set.singleton_subset_iff] using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

@[to_additive]
lemma mulSupport_subsingleton_of_disjoint [One β] {s : γ → Set α} (f : α → β)
    (hs : Pairwise (Disjoint on s)) (i : α) (j : γ)
    (hj : i ∈ s j) : (fun d ↦ (s d).mulIndicator f i).mulSupport ⊆ {j} :=
  mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1) i j hj

--#37060
@[to_additive]
lemma tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α)
    (i : β) (hi : i ∈ ⋃ d, s d) (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) :
    ∏' d, (s d).mulIndicator f i = f i := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]
lemma tprod_mulIndicator_of_mem_union_disjoint [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α) (hs : Pairwise (Disjoint on s))
    (i : β) (hi : i ∈ ⋃ d, s d) : ∏' d, (s d).mulIndicator f i = f i :=
  tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem  s f i hi (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1)

@[to_additive]
lemma tprod_mulIndicator_of_notMem [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α) (i : β) (hi : ∀ d, i ∉ s d) :
    ∏' d, (s d).mulIndicator f i = 1 := by
  aesop

@[to_additive]
lemma mulIndicator_iUnion_of_disjoint_on_mulSupport [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (f : β → α)
    (hs : Pairwise (Disjoint on (fun j ↦ s j ∩ f.mulSupport))) (i : β) :
    (⋃ d, s d).mulIndicator f i = ∏' d, (s d).mulIndicator f i := by
  by_cases h₀ : i ∈ ⋃ d, s d
  · simp only [h₀, Set.mulIndicator_of_mem]
    apply Eq.symm <| tprod_mulIndicator_of_pairwise_disjoint_on_mulSupport_of_mem  _ _ _ h₀ hs
  · aesop

@[to_additive]
lemma mulIndicator_iUnion_of_pairwise_disjoint [CommMonoid α] [TopologicalSpace α] (s : γ → Set β) (hs : Pairwise (Disjoint on s)) (f : β → α) :
    (⋃ d, s d).mulIndicator f = fun i ↦ ∏' d, (s d).mulIndicator f i := by
  ext i
  exact mulIndicator_iUnion_of_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs <| fun _ _ hi ↦ hi.1) i

namespace List

@[simp]
lemma map_eq_replicateZipWith (l : List α) (f : α → β) :
  ((List.replicate l.length f).zipWith (fun a b ↦ a b) l) = (l.map f) := by
  induction l with
  | nil => simp
  | cons a l hl =>
  rw [map_cons, length_cons, ← hl]
  rfl

@[simp]
lemma sequence_cons {F : Type u → Type u} [Applicative F] {α : Type u} (l : List (F α)) (a : F α) : sequence (a :: l) = List.cons <$> a <*> (sequence l) := (List.traverse_cons id a l)
/-
lemma tprod_eq_prod_of_pow_count (l : List α) (f : α → ℝ≥0∞) [DecidableEq α] : (∏' a, (f a)^(l.count a)) = (∏ a ∈ l.toFinset, f a ^ (l.count a)) := by
  rw [tprod_eq_prod (fun b hb ↦ ?_)]
  rw [List.mem_toFinset, ← List.count_eq_zero] at hb
  rw [hb, pow_zero]

#check List.prod_map_eq_pow_single
-/
/-
lemma map_prod_eq_count {M : Type u_4} [CommMonoid M] (l : List α) (f : α → M) [DecidableEq α] : (map f l).prod = ∏ a ∈ l.toFinset, (f a) ^ (l.count a) := by
  exact Finset.prod_list_map_count l f
-/

/-
lemma tsum_eq_sum_of_mul_count [DecidableEq α] (l : List α) (f : α → ℝ≥0∞) : (∑' a, (l.count a) * (f a)) = (∑ a ∈ l.toFinset, (l.count a) * f a) := by
  rw [tsum_eq_sum (fun b hb ↦ ?_)]
  rw [List.mem_toFinset, ← List.count_eq_zero] at hb
  rw [hb, CharP.cast_eq_zero, zero_mul]

#check List.sum_map_ite_eq

lemma map_sum_eq_count [DecidableEq α] (l : List α) (f : α → ℝ≥0∞) : (map f l).sum = ∑ a ∈ l.toFinset, (f a) * (l.count a) := by
  simp_rw [Finset.sum_list_map_count, nsmul_eq_mul]

-/
end List

-- somewhere else
instance addBool : HAdd Bool Nat Nat where
  hAdd b i := b.toNat + i

instance addBoolFin {n : ℕ} : HAdd Bool (Fin n) (Fin (n + 1)) where
  hAdd b i := match b with
  | false => Fin.castSucc i
  | true  => Fin.addNat i 1

-- somewhere else
@[simp]
lemma addBoolFin_false {n : ℕ} (i : Fin n) : addBoolFin.hAdd false i = Fin.castSucc i := by
  rfl

-- somewhere else
@[simp]
lemma addBoolFin_true {n : ℕ} (i : Fin n) : addBoolFin.hAdd true i = Fin.addNat i 1 := by rfl





-- Set.indicator

-- #34138
@[simp]
lemma Set.indicator.mul_indicator_eq (f : α → ℝ≥0∞) (s : Set α) (a : α) : f a * s.indicator 1 a = s.indicator f a := by
  simp only [Set.indicator, Pi.one_apply, mul_ite, mul_one, mul_zero]

-- #34138
lemma Set.PairwiseDisjoint.singleton_subtype (s : Set α) : Pairwise (Disjoint on fun (x : s) => ({x.val} : Set α)) := by
  intro a b hab
  apply pairwise_disjoint_fiber id
  exact Subtype.coe_ne_coe.mpr hab

-- #34138
lemma Set.PairwiseDisjoint.fiber_subtype {g : α → β} (s : Set β) : Pairwise (Disjoint on fun (x : s) => (g⁻¹' {x.val} : Set α)) :=
  fun _ _ hab ↦ pairwise_disjoint_fiber g (Subtype.coe_ne_coe.mpr hab)

-- to Function

lemma Function.comp_apply'  {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f : β → δ} {g : α → β} : (f ∘ fun x => g x) = fun x => f (g x) := by
  -- simp_rw [← Function.comp_apply]
  rfl

-- start `DiscreteMeasure` here.
universe u v w

variable {α β γ δ : Type*}

namespace MeasureTheory

-- #34138
/-- A `DiscreteMeasure α` is given by its weight function `α → ℝ≥0∞`. -/
structure DiscreteMeasure (α : Type*) : Type _ where
  /-- The weight function of the discrete measure. -/
  weight : α → ℝ≥0∞

namespace DiscreteMeasure

-- #34138
/-- The `Measure α` as defined through a `DiscreteMeasure α` (mass function) through a weighted sum
of diracs, using a given `MeasurableSpace α`. -/
noncomputable def toMeasure [MeasurableSpace α] (μ : DiscreteMeasure α) : Measure α :=
  Measure.sum (fun x ↦ μ.weight x • .dirac x)

-- #34138
noncomputable instance [MeasurableSpace α] : Coe (DiscreteMeasure α) (Measure α) where
  coe μ := μ.toMeasure

-- #34138
instance instFunLike : FunLike (DiscreteMeasure α) α ℝ≥0∞ where
  coe p a := p.weight a
  coe_injective' p q h := by
    cases p
    cases q
    simp_all

-- #34138
@[simp]
lemma weight_eq (μ : DiscreteMeasure α) (x : α) : μ.weight x = μ x := by rfl

-- #34138
@[ext]
protected theorem ext {v w : DiscreteMeasure α} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext v w h

-- #34138
theorem mem_support_iff (w : DiscreteMeasure α) (a : α) : a ∈ w.weight.support ↔ w a ≠ 0 := Iff.rfl

-- #34138
theorem apply_eq_zero_iff (w : DiscreteMeasure α) (a : α) : w a = 0 ↔ a ∉ w.weight.support := by
  rw [mem_support_iff, Classical.not_not]

-- #34138
theorem apply_pos_iff (w : DiscreteMeasure α) (a : α) : 0 < w a ↔ a ∈ w.weight.support :=
  pos_iff_ne_zero.trans (w.mem_support_iff a).symm

-- #34138
lemma toMeasure_apply' [MeasurableSpace α] (μ : DiscreteMeasure α) {s : Set α}
    (hs : MeasurableSet s) : μ.toMeasure s = ∑' (a : α), (μ.weight a) • dirac a s := by
  rw [toMeasure, sum_apply (hs := hs)]
  simp_rw [smul_apply]

-- #34138
lemma toMeasure_apply_eq_tsum_mul [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (i : α), μ i * s.indicator 1 i := by
  rw [μ.toMeasure_apply' hs]
  simp

-- #34138
lemma toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (i : α), s.indicator μ i := by
  simp [μ.toMeasure_apply_eq_tsum_mul hs]

-- #34138
lemma toMeasure_apply_eq_tsum_subtype [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : Set α} (hs : MeasurableSet s) : μ.toMeasure s = ∑' (a : s), (μ a) := by
  simp [μ.toMeasure_apply_eq_tsum_mul hs, _root_.tsum_subtype]

-- #34138
@[simp]
lemma toMeasure_apply_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) (a : α) : μ.toMeasure {a} = μ a := by
  simp only [μ.toMeasure_apply_eq_tsum_mul (measurableSet_singleton a), Set.indicator.mul_indicator_eq,
    ←tsum_subtype, tsum_singleton]

-- #34138
theorem toMeasure_apply_eq_zero_iff [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Set α} (hs : MeasurableSet s) :
    μ.toMeasure s = 0 ↔ Disjoint μ.weight.support s := by
  rw [toMeasure_apply (hs := hs), ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

-- #34138
@[simp]
theorem toMeasure_apply_inter_support [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : DiscreteMeasure α} {s u : Set α} (hs : MeasurableSet s) (hu : MeasurableSet u)
    (h : μ.weight.support ⊆ u) : μ.toMeasure (s ∩ u) = μ.toMeasure s := by
  simp only [toMeasure_apply_eq_tsum_mul (hs := hs), toMeasure_apply_eq_tsum_mul (hs := MeasurableSet.inter hs hu)]
  apply tsum_congr (fun a ↦ ?_)
  repeat rw [Set.indicator.mul_indicator_eq, Set.indicator]
  simp only [support_subset_iff, weight_eq, ne_eq] at h
  specialize h a
  aesop

-- #34138
theorem toMeasure_apply_eq_of_inter_support_eq [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hu : MeasurableSet u) (h_support : μ.weight.support ⊆ u)
    (h : s ∩ u = t ∩ u) : μ.toMeasure s = μ.toMeasure t := by
  rw [← toMeasure_apply_inter_support hs hu h_support,
    ← toMeasure_apply_inter_support ht hu h_support, h]

-- #34138
/- Additivity for `μ.toMeasure` for a `μ : DiscreteMeasure` not only applies to countable unions,
but to arbitrary ones. -/
lemma toMeasure_additive [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α)
    {s : δ → Set α} (h₀ : ∀ d, MeasurableSet (s d)) (h₁ : MeasurableSet (⋃ d, s d))
    (hs : Pairwise (Disjoint on s)) : μ.toMeasure (⋃ d, s d) = ∑' (d : δ), μ.toMeasure (s d) := by
  simp only [toMeasure_apply_eq_tsum_mul (hs := h₁), Set.indicator.mul_indicator_eq]
  conv => right; left; intro d; rw [toMeasure_apply_eq_tsum_mul (hs := h₀ _)]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [ENNReal.tsum_comm]
  apply tsum_congr <| fun b ↦ by rw [indicator_iUnion_of_pairwise_disjoint s hs μ]

-- #34138
theorem toMeasure_apply_finset [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Finset α} : μ.toMeasure s = ∑ x ∈ s, μ x := by
  rw [toMeasure_apply (hs := by measurability), tsum_eq_sum (s := s)]
  · exact Finset.sum_indicator_subset μ fun ⦃a⦄ a_1 => a_1
  · exact fun b a => Set.indicator_of_notMem a μ

-- #34138
@[simp]
theorem toMeasure_apply_fintype [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {s : Set α} [Fintype α] : μ.toMeasure s = ∑ x, s.indicator μ x := by
  rw [μ.toMeasure_apply (by measurability)]
  exact tsum_fintype (s.indicator μ)

-- #34138
lemma toMeasure_apply_univ [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) : μ.toMeasure Set.univ = ∑' (a : α), μ a := by
  simp [toMeasure_apply]

-- #34138
lemma toMeasure_apply_univ' [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : DiscreteMeasure α) {s : δ → Set α} (h : ∀ d, MeasurableSet (s d))
    (hs₀ : Pairwise (Disjoint on s)) (hs₁ : Set.univ = ⋃ d, s d) :
    μ.toMeasure Set.univ = ∑' (d : δ), μ.toMeasure (s d) := by
  rw [hs₁]
  exact toMeasure_additive μ h (Eq.symm hs₁ ▸ MeasurableSet.univ) hs₀

-- #34138
theorem toMeasure_injective [MeasurableSpace α] [MeasurableSingletonClass α] :
    (@toMeasure α _).Injective := by
  intro μ ν h
  ext x
  rw [← toMeasure_apply_singleton μ, ← toMeasure_apply_singleton ν, h]

-- #34138
@[simp]
theorem toMeasure_inj [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α} :
    μ.toMeasure = ν.toMeasure ↔ μ = ν :=
  toMeasure_injective.eq_iff

-- #34138
theorem toMeasure_ext [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : DiscreteMeasure α}
    (h : μ.toMeasure = ν.toMeasure) : μ = ν :=
  toMeasure_inj.mp h

-- #34138
theorem toMeasure_mono [MeasurableSpace α] [MeasurableSingletonClass α] {s t u : Set α}
    (hs : MeasurableSet s) (hu : MeasurableSet u) {μ : DiscreteMeasure α} (h : s ∩ u ⊆ t)
    (h_support : μ.weight.support ⊆ u) :
    μ.toMeasure s ≤ μ.toMeasure t := by
  rw [← μ.toMeasure_apply_inter_support hs hu h_support]
  exact OuterMeasureClass.measure_mono μ.toMeasure h

-- #34138
@[simp]
theorem restrict_toMeasure_support [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : DiscreteMeasure α} {u : Set α} (hu : MeasurableSet u) (h : μ.weight.support ⊆ u) :
    μ.toMeasure.restrict u = μ.toMeasure := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, μ.toMeasure_apply_inter_support hs hu h]


lemma nsupport_weight [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) (P : α → Prop) (hμ : μ.toMeasure {a : α | P a} = 0) (a : α) (ha : P a) : μ a = 0 :=
  by
  rw [← nonpos_iff_eq_zero, ← DiscreteMeasure.toMeasure_apply_singleton μ a, ← hμ]
  exact toMeasure_mono (by measurability) (MeasurableSet.univ) (by simp [ha]) (by simp)

section IsFiniteOrProbabilityMeasure

lemma isProbabilityMeasure_iff_hasSum [MeasurableSpace α] [MeasurableSingletonClass α] {p : DiscreteMeasure α} :
    IsProbabilityMeasure p.toMeasure ↔ HasSum p 1 := by
  rw [isProbabilityMeasure_iff, DiscreteMeasure.toMeasure_apply_univ, Summable.hasSum_iff ENNReal.summable]

lemma isProbabilityMeasure_iff_tsumOne [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} : IsProbabilityMeasure μ.toMeasure ↔ ∑' a, μ a = 1 := by
  rw [isProbabilityMeasure_iff_hasSum, Summable.hasSum_iff ENNReal.summable]

lemma isFiniteMeasure_iff_tsum_ne_top [MeasurableSpace α] [MeasurableSingletonClass α] {μ : DiscreteMeasure α} : IsFiniteMeasure μ.toMeasure ↔ ∑' a, μ a ≠ ⊤ := by
  rw [isFiniteMeasure_iff, DiscreteMeasure.toMeasure_apply_univ, lt_top_iff_ne_top]

theorem toMeasure_ne_top_of_isFiniteMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s ≠ ∞ := measure_ne_top p.toMeasure s

theorem toMeasure_le_top_of_isFiniteMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure) (s : Set α) : p.toMeasure s < ∞ := by
  exact measure_lt_top p.toMeasure s

theorem coe_ne_zero [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsProbabilityMeasure p.toMeasure): p.weight ≠ (fun _ ↦ 0) := by
  by_contra h'
  rw [isProbabilityMeasure_iff] at h
  have g : p.toMeasure Set.univ = 0 := by
    rw [DiscreteMeasure.toMeasure_apply_univ]
    simp_rw [← weight_eq, h']
    simp only [tsum_zero]
  apply zero_ne_one' ℝ≥0∞
  rw [← g, ← h]

@[simp]
theorem support_nonempty [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsProbabilityMeasure p.toMeasure): p.weight.support.Nonempty := by
  apply Function.support_nonempty_iff.2 (coe_ne_zero p h)

@[simp]
theorem support_countable [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (h : IsFiniteMeasure p.toMeasure): p.weight.support.Countable :=
  Summable.countable_support_ennreal <| isFiniteMeasure_iff_tsum_ne_top.mp h

theorem toMeasure_apply_eq_toMeasure_univ_iff [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) {s : Set α} (hs : MeasurableSet s) (ha : p.toMeasure s ≠ ⊤) : p.toMeasure s = p.toMeasure Set.univ ↔ p.weight.support ⊆ s := by
  refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ ?_⟩
  · rw [← Set.compl_subset_compl]
    simp at ⊢
    rw [← measure_add_measure_compl (s := s) (by measurability)] at h₀
    nth_rw 1 [← add_zero (p.toMeasure s)] at h₀
    rw [ENNReal.add_right_inj ha] at h₀
    obtain h₀' := Eq.symm h₀
    rw [DiscreteMeasure.toMeasure_apply_eq_zero_iff (MeasurableSet.compl_iff.mpr hs)] at h₀'
    exact Set.disjoint_compl_right_iff_subset.mp h₀'
  · rw [← DiscreteMeasure.toMeasure_apply_inter_support hs MeasurableSet.univ (fun x hx ↦ trivial)]
    rw [← DiscreteMeasure.toMeasure_apply_inter_support MeasurableSet.univ hs h₀, Set.inter_comm]

theorem apply_eq_toMeasure_univ_iff [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (hp : p.weight ≠ fun _ ↦ 0) (a : α) (ha : p a ≠ ⊤) : p a = p.toMeasure Set.univ ↔ p.weight.support = {a} := by
  rw [← DiscreteMeasure.toMeasure_apply_singleton p a, toMeasure_apply_eq_toMeasure_univ_iff p (by measurability)]
  · refine ⟨fun h₀ ↦ ?_, fun h₀ ↦ h₀.le⟩
    apply le_antisymm h₀
    simp at h₀ ⊢
    obtain h₀' : ∀ (y : α), y ≠ a → p y = 0 := by
      intro y hy
      exact (DiscreteMeasure.apply_eq_zero_iff p y).mpr fun a => hy (h₀ y a)
    by_contra h₂
    apply hp
    ext x
    by_cases h₃ : x = a
    · exact h₃ ▸ h₂
    · exact h₀' x h₃
  · simp [ha]

theorem coe_le_toMeasure_univ [MeasurableSpace α] [MeasurableSingletonClass α] (p : DiscreteMeasure α) (a : α) : p a ≤ p.toMeasure Set.univ := by
  rw [← DiscreteMeasure.toMeasure_apply_singleton p a]
  apply DiscreteMeasure.toMeasure_mono (by measurability) MeasurableSet.univ (by simp) (by simp)

theorem apply_le_one [MeasurableSpace α] [MeasurableSingletonClass α] {w : DiscreteMeasure α} [IsProbabilityMeasure w.toMeasure] (a : α) : w a ≤ 1 := by
  have h : w.toMeasure Set.univ = 1 := by
    rw [← isProbabilityMeasure_iff]
    infer_instance
  rw [← toMeasure_apply_singleton w a, ← h]
  exact measure_mono (Set.subset_univ _)

end IsFiniteOrProbabilityMeasure

end DiscreteMeasure

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any measure into a `DiscreteMeasure`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toDiscreteMeasure [hmeas : MeasurableSpace α] (μ : Measure α)
    : DiscreteMeasure α := ⟨fun x => μ ({x} : Set α)⟩

variable [MeasurableSpace α] (μ : Measure α)

theorem toDiscreteMeasure_apply (x : α) : μ.toDiscreteMeasure x = μ {x} := rfl

@[simp]
theorem toDiscreteMeasure_toMeasure [MeasurableSingletonClass α] [Countable α] : μ.toDiscreteMeasure.toMeasure = μ := by
  apply Measure.ext
  intro s hs
  rw [μ.toDiscreteMeasure.toMeasure_apply_eq_tsum_mul hs, ← μ.tsum_indicator_apply_singleton s hs]
  apply tsum_congr (fun b ↦ ?_)
  rw [Set.indicator.mul_indicator_eq]
  congr

end Measure

namespace DiscreteMeasure

section countable

variable (p : DiscreteMeasure α)

variable  [hmeas : MeasurableSpace α] [MeasurableSingletonClass α]

@[simp]
theorem toMeasure_toDiscreteMeasure : toDiscreteMeasure p.toMeasure = p := by
  ext x
  simp_rw [toDiscreteMeasure, toMeasure_apply_singleton]
  rfl

theorem toMeasure_eq_iff_eq_toDiscreteMeasure [Countable α] (μ : Measure α) :
    p.toMeasure = μ ↔ p = μ.toDiscreteMeasure := by
  rw [Measure.ext_iff]
  refine ⟨fun h ↦ ?_, fun h s hs ↦ ?_⟩
  · ext x
    specialize h {x} (measurableSet_singleton x)
    rw [DiscreteMeasure.toMeasure_apply_singleton] at h
    rw [h]
    rfl
  · rw [h]
    nth_rw 2 [← toDiscreteMeasure_toMeasure μ]

end countable

end DiscreteMeasure

end MeasureTheory

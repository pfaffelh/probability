/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Basic

/-!
# DiscreteMeasure: Monad structure

We establish that `DiscreteMeasure α` is a `LawfulMonad`, by defining `map`, `pure`, `bind`,
`join`, and `seq`. This allows for `do`-notation. We also prove the monad laws and provide
`ULiftable` instances.
-/

open MeasureTheory ProbabilityTheory Measure Function

open scoped ENNReal NNReal

namespace MeasureTheory

universe u v w

variable {α β γ δ : Type*}

namespace DiscreteMeasure

/- Now we enter the monad world. -/

section map

/-- The functorial action of a function on a `DiscreteMeasure`. -/
noncomputable def map (g : α → β) (μ : DiscreteMeasure α) : DiscreteMeasure β where weight := fun b ↦ (∑' a, (g⁻¹' {b}).indicator μ.weight a)

@[simp]
lemma map_eq
(μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x = (∑' a, (g⁻¹' {x}).indicator μ.weight a) := by
  rfl

lemma map_eq' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : α), μ i * ({x} : Set β).indicator 1 (g i) := by
  rw [map]
  apply tsum_congr (fun b ↦ ?_)
  rw [← Set.indicator.mul_indicator_eq]
  rfl

lemma map_eq_of_injAt (μ : DiscreteMeasure α) (g : α → β) (x : α) (hx : ∀ x', g x' = g x → x' = x) (y : β) (hy : g x = y) : (μ.map g) y =  μ x := by
  rw [map_eq, ← hy]
  have h : {x} = g ⁻¹' {g x} := (Set.Subset.antisymm (fun ⦃a⦄ => congrArg g) hx)
  rw [← h, ← tsum_subtype]
  simp

lemma map_eq_of_inj (μ : DiscreteMeasure α) (g : α → β) (hg : g.Injective) (x : α) (y : β) (hy : g x = y): (μ.map g) y =  μ x := by
  obtain hg' := fun x' ↦ @hg x' x
  exact map_eq_of_injAt _ _ _ hg' _ hy

lemma map_eq'' (μ : DiscreteMeasure α) (g : α → β) (x : β) : (μ.map g) x =  ∑' (i : g⁻¹' {x}), μ i := by
  rw [tsum_subtype]
  rfl

lemma map_coe [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (f : α → β) (hf : Measurable f) : toMeasure (μ.map f : DiscreteMeasure β) = Measure.map f (toMeasure μ) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (hs := hs) (hf := hf)]
  rw [toMeasure_apply_eq_tsum_subtype (hs := hs)]
  conv => left; left; intro a; rw [map_eq' μ f a.val]
  have h : f⁻¹' s = ⋃ (i : s), f⁻¹' {i.val} := by simp
  nth_rw 1 [h]
  simp_rw [@toMeasure_additive α s _ _ μ _ (by measurability) (by measurability) (Set.PairwiseDisjoint.fiber_subtype s)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_eq_tsum_mul μ (by measurability)]
  rfl

lemma map_toMeasure
[MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) : (μ.map g).toMeasure = sum (fun a ↦ μ a • (dirac (g a))) := by
  letI hα : MeasurableSpace α := ⊤
  rw [map_coe (hf := Measurable.of_discrete)]
  apply @Measure.ext _ _
  intro s hs
  rw [toMeasure, @Measure.map_sum (hf := AEMeasurable.of_discrete)]
  simp_rw [Measure.map_smul, Measure.map_dirac]
  rfl

lemma map_map (μ : DiscreteMeasure α) (g : α → β) (h : β → γ) : (μ.map g).map h = μ.map (h ∘ g) := by
  rw [← @toMeasure_inj γ ⊤, @map_coe β γ ⊤ _ ⊤ _ (hf := by measurability), @map_coe α β ⊤ _ ⊤ _ (hf := by measurability), @map_coe α γ ⊤ _ ⊤ _ (hf := by measurability), Measure.map_map (by measurability) (by measurability)]

lemma map_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = μ.toMeasure (g⁻¹' s) := by
  rw [map_coe (hf := hg)]
  exact Measure.map_apply (by measurability) (by measurability)

lemma map_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (x : β) : μ.map g x = μ.toMeasure (g⁻¹' {x}) := by
  rw [← toMeasure_apply_singleton (map g μ)]
  apply map_toMeasure_apply (hs := by measurability) (hg := hg)

lemma map_toMeasure_apply_eq_tsum_mul [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), μ a * s.indicator 1 (g a) := by
  rw [map_toMeasure]
  rw [sum_apply (hs := hs)]
  simp_rw [smul_apply, dirac_apply' _ hs, smul_eq_mul]

lemma map_apply_eq_tsum_mul (μ : DiscreteMeasure α) (g : α → β) (x : β) : μ.map g x = ∑' (a : α), μ a * ({x} : Set β).indicator 1 (g a) := by
  rw[@map_apply α β ⊤ _ ⊤ _ (hg := by measurability)]
  rw [@toMeasure_apply_eq_tsum_mul α ⊤ _ (hs := by measurability)]
  apply tsum_congr (fun b ↦ by rfl)

lemma map_apply_eq_tsum [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (a : α), (g⁻¹' s).indicator μ a := by
  simp_rw [map_toMeasure, sum_apply (hs := hs), smul_apply, dirac_apply' (hs := hs), smul_eq_mul]
  exact tsum_congr (fun b ↦ Set.indicator.mul_indicator_eq μ (fun b => s (g b)) b)

lemma map_toMeasure_apply_eq_tsum_subtype [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (s : Set β) (hs : MeasurableSet s): (μ.map g).toMeasure s = ∑' (b : s), μ.toMeasure (g⁻¹' {b.val}) := by
  rw [toMeasure_apply_eq_tsum_subtype (hs := hs)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_eq_tsum_mul (hs := by measurability), map_eq']
  rfl

lemma map_toMeasure_apply₄ [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (s : Set β) (hs : MeasurableSet s) : (μ.map g).toMeasure s = ∑' (a : g⁻¹' s), (μ a.val) := by
  letI mα : MeasurableSpace α := ⊤
  rw [map_toMeasure_apply (hg := Measurable.of_discrete) (hs := hs), toMeasure_apply_eq_tsum_subtype (hs := by measurability)]

theorem id_map (μ : DiscreteMeasure α) :
μ.map id = μ := by
  ext x
  rw [map_eq'']
  simp

theorem hasSum_map {μ : DiscreteMeasure α} (hμ : HasSum μ.weight 1) (f : α → β)  : HasSum (μ.map f) 1 := by
  letI mα : MeasurableSpace α := ⊤
  letI mβ : MeasurableSpace β := ⊤
  haveI : IsProbabilityMeasure μ.toMeasure := by exact isProbabilityMeasure_iff_hasSum.mpr hμ
  rw [← isProbabilityMeasure_iff_hasSum]
  rw [map_coe (hf := Measurable.of_discrete)]
  apply isProbabilityMeasure_map (hf := AEMeasurable.of_discrete)

theorem isProbabilityMeasure_map_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α)  (hμ : HasSum μ.weight 1) (f : α → β)  : IsProbabilityMeasure (μ.map f).toMeasure := by
  exact isProbabilityMeasure_iff_hasSum.mpr (hasSum_map hμ f)

end map

section lintegral

lemma lintegral_eq_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (μ : DiscreteMeasure α) (g : α → ℝ≥0∞) : ∫⁻ (a : α), g a ∂ μ.toMeasure = ∑' (a : α), μ a * (g a) := by
  rw [toMeasure]
  simp

-- TODO: integral_map

lemma lintegral_map [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → β) (hg : Measurable g) (f : β → ℝ≥0∞) (hf : Measurable f) : ∫⁻ (a : β), (f a) ∂ (map g μ).toMeasure = ∫⁻ (a : α), f (g a) ∂ μ.toMeasure := by
  rw [map_coe (hf := hg), MeasureTheory.lintegral_map (hf := hf) (hg := hg)]

end lintegral

section join

/-- The monadic join operation for `DiscreteMeasure`. -/
noncomputable def join (m : DiscreteMeasure (DiscreteMeasure α)) : (DiscreteMeasure α) := ⟨fun a ↦ ∑' (μ : DiscreteMeasure α), m μ * μ a⟩

@[simp]
lemma join_weight (m : DiscreteMeasure (DiscreteMeasure α)) (x : α) : m.join x = ∑' (μ : DiscreteMeasure α), m μ * μ x := by
  rfl

/-
noncomputable instance instMeasurableSpace [MeasurableSpace α] : MeasurableSpace (DiscreteMeasure α) := MeasurableSpace.comap toMeasure Measure.instMeasurableSpace

lemma comap_def [m : MeasurableSpace α] (f : β → α) {s : Set β} : MeasurableSet[m.comap f] s ↔ ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s := Iff.rfl

@[measurability]
lemma measurable_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] : Measurable (@toMeasure α _) := by
  intro s hs
  rw [comap_def]
  use s

lemma map_def {s : Set β} : MeasurableSet[m.map f] s ↔ MeasurableSet[m] (f ⁻¹' s) := Iff.rfl


-- set_option maxHeartbeats 0
lemma measurable_map [MeasurableSpace α] [MeasurableSingletonClass α]
[MeasurableSpace β] [MeasurableSingletonClass β] (f : α → β) (hf : Measurable f) : Measurable (map f) := by
  intro s hs
  rw [comap_def]


  sorry

noncomputable instance Measure.instMeasurableSingletonClass [MeasurableSpace α] [MeasurableSingletonClass α] : MeasurableSingletonClass (Measure α) := by
  sorry

  /- refine { measurableSet_singleton := ?_ }
  intro x
  refine MeasurableSpace.measurableSet_generateFrom ?_
  simp
  use ∅
  refine MeasurableSpace.measurableSet_generateFrom ?_
  simp


  refine MeasurableSpace.measurableSet_iInf.mpr (fun i => ?_)
  rw [comap_def]
  rw [comap_def]


  rw [MeasurableSpace.map_def]


  apply?
  refine MeasurableSet.singleton x

  sorry-/


noncomputable instance instMeasurableSingletonClass [MeasurableSpace α] [MeasurableSingletonClass α] : MeasurableSingletonClass (DiscreteMeasure α) := by
  refine { measurableSet_singleton := ?_ }
  intro x
  rw [comap_def]
  use toMeasure '' {x}
  refine ⟨?_, ?_⟩
  · sorry
  · refine Injective.preimage_image toMeasure_injective {x}


-/

lemma join_coe [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)] [MeasurableSingletonClass (DiscreteMeasure α)] {h : Measurable (@toMeasure α _)} (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = Measure.join ((Measure.map toMeasure m.toMeasure)):= by
  apply Measure.ext
  intro s hs
  rw [Measure.join_apply (hs := by measurability)]
  rw [MeasureTheory.lintegral_map (hf := measurable_coe (by trivial)) (hg := by measurability)]
  rw [lintegral_eq_toMeasure, toMeasure_apply_eq_tsum_subtype (hs := hs)]
  simp_rw [join_weight]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun μ ↦ ?_)
  rw [ENNReal.tsum_mul_left, toMeasure_apply_eq_tsum_subtype (hs := hs)]

-- #34239
-- join commutes with sum
-- This goes to MeasureTheory.Measure
lemma Measure.join_sum {α : Type u_1} {mα : MeasurableSpace α} {ι : Type u_7} (m : ι → Measure (Measure α)) :
(sum m).join = sum fun (i : ι) ↦ (m i).join := by
  simp_rw [Measure.join, lintegral_sum_measure]
  ext s hs
  rw [ofMeasurable_apply s hs, Measure.sum_apply _ hs]
  apply tsum_congr (fun i ↦ ?_)
  rw [ofMeasurable_apply s hs]

lemma join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)] [MeasurableSingletonClass (DiscreteMeasure α)] (h : Measurable (@toMeasure α _)) (m : DiscreteMeasure (DiscreteMeasure α)) : m.join.toMeasure = sum (fun μ  ↦ m μ • μ.toMeasure) := by
  apply Measure.ext
  intro s hs
  rw [join_coe (h := h), toMeasure, Measure.map_sum (hf := h.aemeasurable), Measure.join_sum, Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  apply tsum_congr (fun μ ↦ ?_)
  rw [Measure.smul_apply, Measure.map_smul, Measure.join_smul, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have hd : Measure.map toMeasure (dirac μ) = dirac (toMeasure μ) := by
    ext t ht; rw [Measure.map_apply h ht, Measure.dirac_apply' _ ht, Measure.dirac_apply' _ (h ht)]
    rfl
  simp [hd, Measure.join_dirac]

lemma join_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace (DiscreteMeasure α)]  [MeasurableSingletonClass (DiscreteMeasure α)] (h : Measurable (@toMeasure α _)) (m : DiscreteMeasure (DiscreteMeasure α)) (s : Set α) (hs : MeasurableSet s): m.join.toMeasure s = ∑' (μ : DiscreteMeasure α), m μ * μ.toMeasure s := by
  simp only [join_toMeasure h]
  rw [Measure.sum_apply (hs := by measurability)]
  simp

-- #34239
open Measure in
theorem isProbabilityMeasure_join [MeasurableSpace α] {m : Measure (Measure α)} [IsProbabilityMeasure m] (hm : ∀ᵐ μ ∂m, IsProbabilityMeasure μ) : IsProbabilityMeasure (m.join) := by
  simp only [isProbabilityMeasure_iff, MeasurableSet.univ, join_apply]
  simp_rw [isProbabilityMeasure_iff] at hm
  exact lintegral_eq_const hm

lemma ae_iff_support [MeasurableSpace α] [MeasurableSingletonClass α] (P : α → Prop) (hP : MeasurableSet {x | P x}) (μ : DiscreteMeasure α) : (∀ᵐ x ∂μ.toMeasure, P x) ↔ (∀ x ∈ μ.weight.support, P x) := by
  simp_rw [ae_iff, mem_support_iff, ne_eq, ← not_imp_comm]
  rw [toMeasure_apply_eq_tsum_subtype (hs := by measurability)]
  simp

lemma isProbabilityMeasure_join_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (m : DiscreteMeasure (DiscreteMeasure α)) (hm : HasSum m.weight 1) (hμ : ∀ μ ∈ m.weight.support, HasSum μ 1) : IsProbabilityMeasure (m.join).toMeasure := by
  letI hα : MeasurableSpace (DiscreteMeasure α) := ⊤
  simp_rw [Summable.hasSum_iff ENNReal.summable] at hm hμ
  simp_rw [isProbabilityMeasure_iff, toMeasure_apply_univ, join_weight, ← hm]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ ?_)
  by_cases h : m b = 0
  · simp [h]
  · rw [ENNReal.tsum_mul_left, hμ b <| (mem_support_iff m b).mpr h]
    simp

end join

/-- The monadic bind operation for `DiscreteMeasure`. -/
noncomputable def bind (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (DiscreteMeasure β) := (μ.map g).join

-- define a mixture
noncomputable def mixture {n : ℕ} (p : DiscreteMeasure (Fin n)) (μ : Fin n → DiscreteMeasure α) := p.bind μ

lemma bind_toMeasure_apply_eq_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g)
 : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  rw [bind, Measure.bind, join_coe (h := htoβ), ← Measure.map_map (hf := hg) (hg := htoβ), map_coe (hf := hg)]

lemma bind_coe [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (hg : Measurable g) : (μ.bind g).toMeasure = μ.toMeasure.bind (toMeasure ∘ g) := by
  apply Measure.ext
  intro s hs
  rw [bind_toMeasure_apply_eq_toMeasure (htoβ := htoβ) (hg := hg)]

-- #34239
open Measure in
theorem isProbabilityMeasure_bind [MeasurableSpace α] [MeasurableSpace β] {m : Measure α} [IsProbabilityMeasure m] {f : α → Measure β} (hf₀ : AEMeasurable f m) (hf₁ : ∀ᵐ μ ∂m, IsProbabilityMeasure (f μ)) : IsProbabilityMeasure (m.bind f) := by
  simp [Measure.bind]
  apply @isProbabilityMeasure_join _ _ _ (isProbabilityMeasure_map hf₀) ((ae_map_iff hf₀ ProbabilityMeasure.measurableSet_isProbabilityMeasure).mpr hf₁)

-- #34239
-- bind commutes with sum
-- This goes to MeasureTheory.Measure
lemma Measure.bind_sum {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {ι : Type u_7} (m : ι → Measure α) (f : α → Measure β) (h : AEMeasurable f (sum fun i => m i)) :
  (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [Measure.bind, Measure.map_sum h, Measure.join_sum]

-- #34239
-- scalar multiplication commutes with bind
-- This goes to MeasureTheory.Measure
lemma Measure.bind_smul {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α) (f : α → Measure β) :
  (c • m).bind f = c • (m.bind f) := by
  simp_rw [Measure.bind, Measure.map_smul, Measure.join_smul]


lemma bind_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β]
(μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) : (μ.bind g).toMeasure  = sum (fun a ↦ (μ a) • (g a).toMeasure) := by
  letI hα : MeasurableSpace α := ⊤
  letI hDα : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI hDβ : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply Measure.ext
  intro s _
  rw [bind_toMeasure_apply_eq_toMeasure (htoβ := by measurability) (hg := by measurability), toMeasure, Measure.bind_sum (h := AEMeasurable.of_discrete), Measure.sum_apply (hs := by measurability), Measure.sum_apply (hs := by measurability)]
  simp_rw [Measure.bind_smul, Measure.dirac_bind (f := toMeasure ∘ g) (hf := by measurability)]
  rfl

lemma bind_toMeasure_apply [MeasurableSpace β] [MeasurableSingletonClass β] (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  (s : Set β) (hs : MeasurableSet s): (μ.bind g).toMeasure s = ∑' (a : α), μ a * (g a).toMeasure s := by
  simp_rw [bind_toMeasure, Measure.sum_apply (hs := hs), smul_apply, smul_eq_mul]

@[simp]
lemma bind_apply (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β) (x : β) : (μ.bind g) x = ∑' (a : α), μ a * (g a) x := by
  letI : MeasurableSpace β := ⊤
  simp_rw [← toMeasure_apply_singleton (μ.bind g) x, ← toMeasure_apply_singleton _ x]
  exact bind_toMeasure_apply μ g _ (by measurability)

lemma join_map_map (m : DiscreteMeasure (DiscreteMeasure α)) (f : α → β) : (map (map f) m).join = map f m.join := by
  rw [← bind]
  ext x
  letI hα : MeasurableSpace α := ⊤
  letI hDα : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI hβ : MeasurableSpace β := ⊤
  rw [← toMeasure_apply_singleton (m.bind (map f)), ← toMeasure_apply_singleton (map f m.join), bind_toMeasure_apply, map_toMeasure_apply (hg := Measurable.of_discrete) (hs := MeasurableSet.of_discrete), join_toMeasure_apply (h := Measurable.of_discrete) (hs := MeasurableSet.of_discrete)]
  apply tsum_congr (fun b ↦ ?_)
  rw [toMeasure_apply_singleton, DiscreteMeasure.map_apply (hg := Measurable.of_discrete)]
  exact MeasurableSet.of_discrete

/- currently not needed!

noncomputable instance : HSMul ℝ≥0∞ (DiscreteMeasure β) (DiscreteMeasure β) := by
  exact { hSMul := fun a x ↦ ⟨fun i ↦ a * x.weight i⟩ }

lemma smul_apply' {α : Type u_1} {R : Type u_6} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  {_m : MeasurableSpace α} (c : R) (μ : DiscreteMeasure α) (x : Set α) : (c • μ) s = c • μ s

lemma hSMul_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (a : ℝ≥0∞) (x : DiscreteMeasure α) : (a • x).toMeasure = a • x.toMeasure := by
  ext s hs
  rw [smul_apply]

  sorry

theorem bind_const (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) : (μ₁.bind fun (_ : α) => μ₂) =  (∑' a, μ₁ a) • μ₂ := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure α) := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  rw [← toMeasure_inj]
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := by measurability), Function.comp_apply', Measure.bind_const]
  rw [toMeasure_apply_univ, hSMul_toMeasure_apply]

-/

theorem bind_bind (μ₁ : DiscreteMeasure α) (f : α → DiscreteMeasure β) (g : β → DiscreteMeasure γ) :
(μ₁.bind f).bind g = μ₁.bind fun (a : α) => (f a).bind g := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace γ := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  letI : MeasurableSpace (DiscreteMeasure γ) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete)]
  rw [Measure.bind_bind AEMeasurable.of_discrete AEMeasurable.of_discrete]
  congr
  ext a'
  rw [comp_apply, comp_apply, bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete)]

theorem bind_comm (μ₁ : DiscreteMeasure α) (μ₂ : DiscreteMeasure β) (f : α → β → DiscreteMeasure γ) :
(μ₁.bind fun (a : α) => μ₂.bind (f a)) = μ₂.bind fun (b : β) => μ₁.bind fun (a : α) => f a b := by
  ext x
  repeat simp_rw [bind_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr (fun b ↦ tsum_congr (fun a ↦ ?_))
  ring

/- lemma isProbabilityMeasure_bind_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace (DiscreteMeasure β)] [MeasurableSingletonClass (DiscreteMeasure β)] {htoβ : Measurable (@toMeasure β _)} {m : DiscreteMeasure α} [hm : IsProbabilityMeasure m.toMeasure] {f : α → DiscreteMeasure β} (hf : Measurable f) (hf₁ : ∀ (a : α), IsProbabilityMeasure (f a).toMeasure) : IsProbabilityMeasure (m.bind f).toMeasure := by
  rw [bind_coe (htoβ := htoβ) (hg := hf)]
  exact @isProbabilityMeasure_bind α β  _ _ m.toMeasure _ (toMeasure ∘ f) ((htoβ.comp hf).aemeasurable) (ae_of_all (toMeasure m) hf₁)
-/

lemma hasSum_bind {m : DiscreteMeasure α} (hm : HasSum m.weight 1) {f : α → DiscreteMeasure β} (hf₁ : ∀ a ∈ support m.weight, HasSum (f a).weight 1) : HasSum (m.bind f) 1 := by
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  letI : MeasurableSpace α := ⊤
  rw [← isProbabilityMeasure_iff_hasSum]
  rw [bind_coe (htoβ := by measurability) (hg := by measurability)]
  haveI : IsProbabilityMeasure (toMeasure m) := isProbabilityMeasure_iff_hasSum.mpr hm
  exact isProbabilityMeasure_bind AEMeasurable.of_discrete (hf₁ := (ae_iff_support (fun x => IsProbabilityMeasure ((toMeasure ∘ f) x)) trivial m).mpr (fun x hx ↦ isProbabilityMeasure_iff_hasSum.mpr (hf₁ x hx)))

lemma isProbabilityMeasure_bind_toMeasure [MeasurableSpace β] [MeasurableSingletonClass β] {m : DiscreteMeasure α} (hm : HasSum m.weight 1) {f : α → DiscreteMeasure β} (hf₁ : ∀ a ∈ support m.weight, HasSum (f a).weight 1) : IsProbabilityMeasure (m.bind f).toMeasure := by
  exact isProbabilityMeasure_iff_hasSum.mpr (hasSum_bind hm hf₁)

-- end bind

section pure

/-- The pure `DiscreteMeasure` puts all the mass lies in one point. The value of `pure a` is `1` at `a` and
`0` elsewhere. In other words, `pure ∘ toMeasure = Measure.dirac`. -/
noncomputable def pure (a : α) : DiscreteMeasure α := ⟨({a} : Set α).indicator 1⟩

lemma pure_apply (a b : α) : (pure a) b = ({a} : Set α).indicator 1 b := rfl

@[simp]
lemma pure_apply_self {a : α} : pure a a = 1 := by
  rw [pure_apply]
  simp

@[simp]
lemma pure_apply_nonself {a b : α} (h : b ≠ a) : pure a b = 0 := by
  rw [pure_apply]
  simp [h]

lemma pure_comm {a a' : α} : pure a a' = pure a' a := by
  rw [pure_apply, pure_apply, Set.indicator, Set.indicator]
  congr 1
  simp only [Set.mem_singleton_iff, eq_iff_iff]
  exact eq_comm

@[simp]
lemma pure_toMeasure_apply [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) (s : Set α) (hs : MeasurableSet s): (pure a).toMeasure s = s.indicator 1 a := by
  rw [toMeasure_apply (hs := hs)]
  simp_rw [← Set.indicator.mul_indicator_eq (f := (pure a))]
  simp_rw [pure_apply, Set.indicator.mul_indicator_eq, Set.indicator_indicator]
  by_cases h : a ∈ s
  · rw [Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h),
      ← tsum_subtype, tsum_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

lemma pure_coe [MeasurableSpace α] [MeasurableSingletonClass α]  (a : α) : (pure a).toMeasure = .dirac a := by
  apply Measure.ext
  intro s hs
  simp_rw [pure_toMeasure_apply (hs := hs), Measure.dirac_apply]

lemma toMeasure_pure_eq_dirac [MeasurableSpace α] [MeasurableSingletonClass α] : (toMeasure ∘ @pure α) = .dirac := by
  funext a
  rw [← pure_coe]
  rfl

lemma pure_hasSum [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) : HasSum (pure a) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  simp_rw [pure_apply, ← tsum_subtype, tsum_singleton]
  rfl

lemma map_pure (a : α) (f : α → β) : (pure a).map f = pure (f a) := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  rw [← toMeasure_inj, pure_coe, map_coe (hf := by measurability), pure_coe, Measure.map_dirac]

theorem pure_bind (a : α) (f : α → DiscreteMeasure β) :
(pure a).bind f = f a := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), pure_coe, dirac_bind (hf := Measurable.of_discrete)]
  rfl

theorem bind_pure  (μ : DiscreteMeasure α) :
μ.bind pure = μ := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace (DiscreteMeasure α) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), Measure.bind, toMeasure_pure_eq_dirac, ← Measure.bind, Measure.bind_dirac]

@[simp, monad_norm]
lemma bind_pure_comp (f : α → β) (μ : DiscreteMeasure α) : μ.bind (fun a ↦ pure (f a)) = μ.map f := by
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  letI : MeasurableSpace (DiscreteMeasure β) := ⊤
  apply toMeasure_ext
  rw [bind_coe (htoβ := Measurable.of_discrete) (hg := Measurable.of_discrete), map_coe (hf := Measurable.of_discrete), Function.comp_apply']
  simp_rw [pure_coe]
  rw [Measure.bind_dirac_eq_map (hf := Measurable.of_discrete)]

/-- Pushing `map` through `bind`: `(p.bind f).map g = p.bind (fun a => (f a).map g)`. -/
lemma map_bind (p : DiscreteMeasure α) (f : α → DiscreteMeasure β) (g : β → γ) :
    (p.bind f).map g = p.bind (fun a => (f a).map g) := by
  rw [← bind_pure_comp, bind_bind]
  congr 1
  funext a
  rw [bind_pure_comp]

/-- Pushing `bind` past `map`: `(p.map f).bind g = p.bind (fun a => g (f a))`. -/
lemma bind_map (p : DiscreteMeasure α) (f : α → β) (g : β → DiscreteMeasure γ) :
    (p.map f).bind g = p.bind (fun a => g (f a)) := by
  rw [← bind_pure_comp, bind_bind]
  congr 1
  funext a
  rw [pure_bind]

lemma hasSum_pure (a : α) : HasSum (pure a) 1 := by
  simp_rw [Summable.hasSum_iff ENNReal.summable, pure_apply, ← tsum_subtype]
  simp

lemma isProbabilityMeasure_pure_toMeasure [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) : IsProbabilityMeasure ((pure a).toMeasure) := isProbabilityMeasure_iff_hasSum.mpr (hasSum_pure a)

@[simp]
lemma tsum_pure (a : α) (f : α → ℝ≥0∞): ∑' (x : α), (f x) * pure a x = f a := by
  simp_rw [pure_apply]
  simp_rw [Set.indicator.mul_indicator_eq]
  rw [← tsum_subtype]
  simp

end pure

section seq

variable (q : DiscreteMeasure (α → β)) (p : Unit → DiscreteMeasure α) (b : β)

/-- The monadic sequencing operation for `DiscreteMeasure`. -/
-- mf <*> mx := mf >>= fun f => mx >>= fun x => pure (f x)
noncomputable def seq (q :DiscreteMeasure (α → β)) (p :  Unit →DiscreteMeasure α) : DiscreteMeasure β :=
  q.bind fun m => (p ()).bind fun a => pure (m a)

@[simp, monad_norm]
lemma bind_map_eq_seq (q :DiscreteMeasure (α → β)) (p : Unit →DiscreteMeasure α) : seq q p = q.bind (fun m => (p ()).map m) := by
  simp_rw [← bind_pure_comp]
  rfl

@[simp]
theorem seq_apply [DecidableEq β] : seq q p b = ∑' (f : α → β) (a : α), q f * if b = f a then (p ()) a else 0 := by
  simp_rw [seq, bind_apply, pure_apply, Set.indicator, Set.mem_singleton_iff, ← ENNReal.tsum_mul_left]
  repeat apply tsum_congr (fun f ↦ ?_)
  split_ifs <;> simp

theorem seq_apply₁ [DecidableEq β] : seq q p b = ∑' (f : α → β) (a : f⁻¹' {b}), q f * (p ()) a := by
  simp_rw [seq_apply, ENNReal.tsum_mul_left, tsum_subtype, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr 1
  apply tsum_congr (fun g ↦ ?_)
  grind

@[simp]
theorem seq_apply₂ : seq q p b = ∑' (f : α → β), q f * ∑' (a : α), (f⁻¹' {b}).indicator (p ()) a := by
  simp_rw [seq, bind_apply, pure_apply, Set.indicator]
  apply tsum_congr (fun f ↦ ?_)
  congr
  funext a
  simp only [Pi.one_apply, mul_ite, mul_one, mul_zero, Set.mem_preimage, Set.mem_singleton_iff]
  grind

lemma hasSum_seq {q : DiscreteMeasure (α → β)} (hq : HasSum q.weight 1) {p : Unit → DiscreteMeasure α} (hp : HasSum (p ()).weight 1) : HasSum (seq q p) 1 := by
  letI hα : MeasurableSpace α := ⊤
  rw [bind_map_eq_seq]
  apply hasSum_bind hq (fun a _ ↦ hasSum_map hp a)

lemma isProbabilityMeasure_seq_toMeasure  [MeasurableSpace β] [MeasurableSingletonClass β] {q : DiscreteMeasure (α → β)} (hq : HasSum q.weight 1) {p : Unit → DiscreteMeasure α} (hp : HasSum (p ()).weight 1) : IsProbabilityMeasure (seq q p).toMeasure := by
  exact isProbabilityMeasure_iff_hasSum.mpr (hasSum_seq hq hp)

end seq

noncomputable instance : Functor DiscreteMeasure where
  map := map

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map g h μ := (map_map μ g h).symm

section monad

noncomputable instance : Functor DiscreteMeasure where
  map := map

noncomputable instance : Seq DiscreteMeasure where
  seq := seq

noncomputable instance : Monad DiscreteMeasure where
  pure := pure
  bind := bind

instance : LawfulFunctor DiscreteMeasure where
  map_const := rfl
  id_map := id_map
  comp_map f g μ := (map_map μ f g).symm

instance : LawfulMonad DiscreteMeasure :=
  LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)
  (bind_map :=
  fun q p ↦ (bind_map_eq_seq q (fun _ ↦ p)).symm)

@[simp, monad_norm]
lemma pure_eq_pure : @pure α = @Pure.pure DiscreteMeasure _ α := by rfl

@[simp, monad_norm]
lemma map_eq_map {α β : Type u} (f : α → β) (p : DiscreteMeasure α) : (map f p) = (Functor.map f p) := rfl

@[simp, monad_norm]
lemma seq_eq_seq {α β : Type u} (p : DiscreteMeasure (α → β)) (q : Unit → DiscreteMeasure α) : seq p q = Seq.seq p q := by
  rfl

@[simp, monad_norm]
lemma bind_eq_bind {α β : Type u} (μ : DiscreteMeasure α) (g : α → DiscreteMeasure β)  : (bind μ g) = (Bind.bind μ g) := rfl

/--
This instance allows `do` notation for `DiscreteMeasure` to be used across universes, for instance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
noncomputable instance : ULiftable DiscreteMeasure.{u} DiscreteMeasure.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by rw [map_map, Equiv.symm_comp_self, id_map]
      right_inv := fun a => by simp [map_map]
      }

end monad

end DiscreteMeasure

end MeasureTheory

/-
Copyright (c) 2026 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Uniform
import Probability.DiscreteMeasure.Sequence

/-!
# A multi-color urn

We introduce the model for a multi-color urn, frequently used in discrete probability theory. An
`urn ι` is parametrised by a `Fintype ι` of colors and a function `card : ι → ℕ` giving the number
of balls of each color `i : ι`. The individual balls are encoded as the sigma type
`u.toSet := Σ i : ι, Fin (u.card i)`, so that each ball is a pair `⟨color, index⟩`.

For an urn `u : urn ι`, the Finset `u.draw n : Finset (Finset u.toSet)` collects all draws of `n`
balls without replacement, and `u.result n` (resp. `u.colResult n i`) records the per-color
configurations where exactly `n i` balls of color `i` have been drawn. We use these to model the
uniform distribution on draws and read off color statistics.

# Hypergeometric distribution

The (multi-color) hypergeometric distribution `hypergeometric u n` describes drawing `n` balls
without replacement from `u`, with the result given as the function `i ↦ #{ balls of color i in
the draw}`. The classical two-color case is recovered as `hypergeometricBool_weight` for
`u : urn Bool`.
-/

open MeasureTheory DiscreteMeasure ProbabilityTheory Measure Function Finset

open scoped ENNReal NNReal

universe u v w

variable {α β γ δ : Type*}

section urn

/-- An urn is a finite collection of balls of various colors. The colors are from a finite
type `ι`, and `card i` gives the number of balls of color `i`. -/
structure urn (ι : Type*) [Fintype ι] where
  card : ι → ℕ

variable {ι : Type*} [Fintype ι]

/-- Each ball in the urn is given by the pair `⟨color, index⟩` where `color : ι` is the
color and `index : Fin (u.card color)` identifies the ball within that color. -/
@[reducible] def urn.toSet (u : urn ι) : Type _ := Σ i : ι, Fin (u.card i)

instance (u : urn ι) : Fintype u.toSet := Sigma.instFintype

/-- The color of a ball. -/
def color {u : urn ι} (x : u.toSet) : ι := x.1

/-- The total number of balls equals the sum over all colors. -/
lemma card_toSet (u : urn ι) : Fintype.card u.toSet = ∑ i, u.card i := by
  unfold urn.toSet
  rw [Fintype.card_sigma]
  simp

/-- The set of `n`-element subsets of the urn (drawing `n` balls without replacement). -/
def urn.draw (u : urn ι) (n : ℕ) : Finset (Finset u.toSet) :=
  Finset.powersetCard n Finset.univ

lemma urn.draw_mem (u : urn ι) (n : ℕ) (s : Finset u.toSet) : s ∈ u.draw n ↔ #s = n := by simp [urn.draw]

/-- The number of `n`-element draws from an urn with `N` balls is `N.choose n`. -/
lemma draw_card (u : urn ι) (n : ℕ) :
    (u.draw n).card = (∑ i, u.card i).choose n := by
  rw [urn.draw, Finset.card_powersetCard, Finset.card_univ, card_toSet]

/-- The set of draws is nonempty when `n` does not exceed the total number of balls. -/
lemma draw_nonempty (u : urn ι) (n : ℕ) (hn : n ≤ ∑ i, u.card i) :
    (u.draw n).Nonempty := by
  rw [← Finset.card_pos, draw_card]
  exact Nat.choose_pos hn

instance (priority := low) draw_nonempty_subtype (u : urn ι) (n : ℕ)
    [h : Fact (n ≤ ∑ i, u.card i)] :
    Nonempty ↥(u.draw n) :=
  (draw_nonempty u n h.out).to_subtype

/-- For each color `i`, the set of `n i`-element subsets of balls of color `i`. -/
def urn.colResult [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (i : ι) : Finset (Finset (Fin (u.card i))) :=
  Finset.powersetCard (n i) Finset.univ

lemma urn.colResult_mem [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (i : ι) (s :  (Finset (Fin (u.card i)))) : s ∈ urn.colResult u n i ↔ s.card = n i := by
  simp [urn.colResult]

/-- A colored draw: independently choose `n i` balls of each color `i`.
This is a `piFinset` of per-color draws. -/
def urn.result [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    Finset (∀ i, Finset (Fin (u.card i))) :=
  Fintype.piFinset (u.colResult n)

lemma urn.result_mem [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (s : (i : ι) → Finset (Fin (u.card i))) : s ∈ urn.result u n ↔ ∀ i, #(s i) = n i := by
  simp_rw [result, Fintype.mem_piFinset, urn.colResult_mem]

-- Helper: extract balls of a given color from a draw
private noncomputable def extractColor [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) (i : ι) :
    Finset (Fin (u.card i)) :=
      { j | ⟨i, j⟩ ∈ d}
  --d.preimage (fun j => (⟨i, j⟩ : u.toSet)) (by intro a _ b _ h; cases h; rfl)

-- Helper: reassemble per-color choices into a single draw
private noncomputable def assembleDraw [DecidableEq ι] {u : urn ι} (f : ∀ i, Finset (Fin (u.card i))) :
    Finset u.toSet :=
  (Finset.univ (α := ι)).sigma f

private lemma assembleDraw_mem [DecidableEq ι] {u : urn ι} {f : ∀ i, Finset (Fin (u.card i))}
    {x : u.toSet} : x ∈ assembleDraw f ↔ x.2 ∈ f x.1 := by
  simp [assembleDraw]

private lemma extractColor_mem [DecidableEq ι] {u : urn ι} {d : Finset u.toSet}
    {i : ι} {j : Fin (u.card i)} : j ∈ extractColor d i ↔ (⟨i, j⟩ : u.toSet) ∈ d := by
  simp [extractColor]

private lemma assembleDraw_extractColor [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) :
    assembleDraw (extractColor d) = d := by
  ext ⟨i, j⟩
  rw [assembleDraw_mem, extractColor_mem]

private lemma extractColor_assembleDraw [DecidableEq ι] {u : urn ι}
    (f : ∀ i, Finset (Fin (u.card i))) :
    extractColor (assembleDraw f) = f := by
  ext i j
  rw [extractColor_mem, assembleDraw_mem]

lemma extractColor_mem_result [ DecidableEq ι] (u : urn ι) (n : ι → ℕ) (d : Finset u.toSet) (h : ∀ (i : ι), (extractColor d i).card = n i) : extractColor d ∈ urn.result u n := by
  simp [urn.result, urn.colResult, h]

noncomputable def urn.result' [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    Finset (Finset u.toSet) :=
  {d : Finset u.toSet | ∀ i, #(extractColor d i) = n i}

def urn.result'_mem [DecidableEq ι] (u : urn ι) (n : ι → ℕ) (d : Finset u.toSet) : d ∈ u.result' n ↔ ∀ i, #(extractColor d i) = n i := by
  simp [urn.result']

lemma urn.result'_mem_draw [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    u.result' n ⊆ u.draw (∑ i, n i) := by
  intro d hd
  rw [urn.draw_mem, ← assembleDraw_extractColor d, assembleDraw, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => (urn.result'_mem u n d).mp hd i)

/-
private lemma count_eq_extractColor_card' [DecidableEq ι] {u : urn ι} (d : Finset u.toSet) (i : ι) :
    (d.val.map color).count i = (extractColor d i).card := by
  rw [Multiset.count_map]
  calc
    _ = (d.filter (fun x => x.1 = i)).card := by simp_rw [Finset.card, Finset.filter_val, color, eq_comm]
    _ = ((extractColor d i).map
      ⟨fun j => (⟨i, j⟩ : u.toSet), fun _ _ h => by simpa using h⟩).card := by
          congr; ext ⟨i', j'⟩; rw [extractColor]; aesop
    _ = (extractColor d i).card := by
      rw [Finset.card_map]
-/

/-- Bijection between draws with fixed color counts and `result` (the piFinset of per-color choices). -/
noncomputable def equiv_filter_draw_result [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    u.result' n ≃ u.result n where
  toFun := fun ⟨d, hd⟩ =>
    ⟨extractColor d, extractColor_mem_result u n d ((u.result'_mem n d).mp hd)⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨assembleDraw f, (urn.result'_mem u n _).mpr (fun i => by
      rw [extractColor_assembleDraw]
      exact (urn.result_mem u n f).mp hf i)⟩
  left_inv := fun ⟨d, _⟩ => Subtype.ext (assembleDraw_extractColor d)
  right_inv := fun ⟨f, _⟩ => Subtype.ext (extractColor_assembleDraw _)

/-- The cardinality version of the bijection. -/
lemma result'_card_result [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    #(u.result' n) = #(u.result n) := by
  rw [← Fintype.card_coe, Fintype.card_congr (equiv_filter_draw_result u n),
    Fintype.card_coe]

/-- The cardinality of result as given by `(n : ι → ℕ)` is `∏ i, (u.card i).choose (n i)` — immediate from piFinset. -/
lemma result_card [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    #(u.result n) = ∏ i, (u.card i).choose (n i) := by
  simp [urn.result, urn.colResult, Fintype.card_piFinset, Finset.card_powersetCard]

/-
private lemma assembleDraw_card [DecidableEq ι] {u : urn ι}
    (f : ∀ i, Finset (Fin (u.card i))) :
    (assembleDraw f).card = ∑ i, (f i).card := by
  rw [assembleDraw, Finset.card_sigma]
-/

/-- The number of draws with fixed color counts equals `∏ i, (u.card i).choose (n i)`. -/
lemma result'_card [DecidableEq ι] (u : urn ι) (n : ι → ℕ) :
    #(u.result' n) =
    ∏ i, (u.card i).choose (n i) := by
  rw [result'_card_result, result_card]

end urn

section hypergeometric

namespace MeasureTheory

namespace DiscreteMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The hypergeometric distribution for drawing `n` balls without replacement from an urn with `u.card i` ι of color `i : ι`, returning
the number of balls of each color. -/
noncomputable def hypergeometric (u : urn ι) (n : ℕ)  [Nonempty (u.draw n)] :
    DiscreteMeasure (ι → ℕ) :=
  do
    let X ← uniformOfFintype (u.draw n)
    return (fun i => (extractColor X.val i).card)

lemma hypergeometric_eq_map (u : urn ι) (n : ℕ) [Nonempty (u.draw n)] :
    hypergeometric u n =
      map (fun X : ↥(u.draw n) => fun b => (extractColor X.val b).card)
        (uniformOfFintype ↥(u.draw n)) :=
  bind_pure_comp _ _

theorem hypergeometric_hasSum (u : urn ι) (n : ℕ) [Nonempty (u.draw n)] :
    HasSum (hypergeometric u n).weight 1 := by
  rw [hypergeometric_eq_map]
  exact hasSum_map (hasSum_uniformOfFinset (hs := Finset.univ_nonempty)) _

theorem hypergeometric_weight (u : urn ι) (m : ι → ℕ) [Nonempty (u.draw (∑ i, m i))] :
    (hypergeometric u (∑ i, m i)).weight m =
    (((∑ i, u.card i).choose (∑ i, m i) : ℝ≥0∞))⁻¹ * ∏ i, (u.card i).choose (m i) := by
  classical
  letI : MeasurableSpace (u.draw (∑ i, m i)) := ⊤
  rw [hypergeometric_eq_map]
  rw [weight_eq, map_apply (hg := Measurable.of_discrete)]
  rw [uniformOfFintype_apply_toMeasure (ht := MeasurableSet.of_discrete)]
  simp only [Fintype.card_coe]
  have h : ((fun (X : ↥(u.draw (∑ i, m i))) (i : ι) => #(extractColor X.val i))
      ⁻¹' {m}).toFinset =
      (u.result' m).preimage Subtype.val
        Subtype.val_injective.injOn := by
    ext X
    simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_preimage, urn.result'_mem, funext_iff]
  rw [h, Finset.card_preimage,
    Finset.filter_eq_self.mpr (fun d hd => ⟨⟨d, u.result'_mem_draw m hd⟩, rfl⟩),
    result'_card, draw_card, mul_comm]

theorem hypergeometricBool_weight (u : urn Bool) (k l : ℕ) [Nonempty ↥(u.draw (k + l))] :
    (hypergeometric u (k + l)).weight (cond · k l) =
    (((u.card true + u.card false).choose (k + l) : ℝ≥0∞))⁻¹ * ((u.card true).choose k * (u.card false).choose l) := by
  let m : Bool → ℕ := (cond · k l)
  have hm : k + l = ∑ i, m i := by simp [m]
  haveI : Nonempty ↥(u.draw (∑ i, m i)) := by
    rw [← hm]
    infer_instance
  simp only [hm]
  rw [hypergeometric_weight]
  simp
  rfl

end DiscreteMeasure

end MeasureTheory

end hypergeometric

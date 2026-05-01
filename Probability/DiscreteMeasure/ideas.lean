/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Probability.DiscreteMeasure.Binomial

/-!
# DiscreteMeasure: Ideas — mixing and thinning

Sketches of identities connecting Poisson, Binomial, Exponential, and Geometric
distributions via `bind`. Two flavors:

* **Option A (fully discrete).** Poisson thinning:
  `(poisson λ).bind (fun n => binom p n) = poisson (λ * p)`.
  Fits the `DiscreteMeasure` monad directly.

* **Option B (continuous mixing).** `Exp.bind Poisson = Geometric`.
  Escapes the discrete setting; has to live in Mathlib's `Measure` / `PMF`
  world, using `exponentialMeasure`, `pmfPoisson`, `pmfGeometric`.
-/

open MeasureTheory ProbabilityTheory Measure Function
open scoped ENNReal NNReal

namespace MeasureTheory

namespace DiscreteMeasure

/-! ## Option A: Poisson thinning -/

section poisson

/-- Poisson distribution with rate `lam : ℝ≥0`, as a `DiscreteMeasure ℕ`. -/
noncomputable def poisson (lam : ℝ≥0) : DiscreteMeasure ℕ where
  weight k := ENNReal.ofReal (Real.exp (-lam) * lam ^ k / k.factorial)

lemma poisson_apply (lam : ℝ≥0) (k : ℕ) :
    poisson lam k = ENNReal.ofReal (Real.exp (-lam) * lam ^ k / k.factorial) := rfl

lemma hasSum_poisson (lam : ℝ≥0) : HasSum (poisson lam) 1 := by
  -- `∑ₖ lam^k / k! = exp lam`, then multiply by `exp (-lam)`.
  -- Uses `Real.hasSum_exp_of_nonneg` / `NNReal.exp_series`, then transfer
  -- through `ENNReal.ofReal` via `ENNReal.hasSum_ofReal` on nonneg summands.
  sorry

instance isProbabilityMeasure_poisson (lam : ℝ≥0) :
    IsProbabilityMeasure (poisson lam).toMeasure :=
  isProbabilityMeasure_iff_hasSum.mpr (hasSum_poisson lam)

end poisson

section thinning

/-- Poisson thinning: if `N ~ Poisson lam` and `K | N = n ~ Binomial n p`,
    then marginally `K ~ Poisson (lam * p)`.

    Proof sketch (pointwise in `k`):
    ```
    Σₙ e^{-lam} lam^n / n! · C(n,k) p^k (1-p)^(n-k)
      = e^{-lam} p^k / k! · Σ_{n ≥ k} lam^n (1-p)^(n-k) / (n-k)!
      = e^{-lam} p^k / k! · lam^k · e^{lam (1-p)}
      = e^{-lam p} (lam p)^k / k!
    ```
-/
theorem poisson_bind_binom (lam : ℝ≥0) (p : unitInterval) :
    ((poisson lam).bind (fun n => binom p n))
      = poisson (lam * ⟨p, p.2.1⟩) := by
  ext k
  simp_rw [bind_apply, poisson_apply, binom_formula]
  -- swap sum over `n ≥ k`, factor `p^k / k!`, re-index `m = n - k`,
  -- remaining sum is `exp (lam (1-p))`; combine with `exp (-lam)` to get
  -- `exp (-lam p)`.
  sorry

end thinning

end DiscreteMeasure

end MeasureTheory

/-! ## Option B: `Exp.bind Poisson = Geometric`

This does not fit `DiscreteMeasure`, since the mixing law is continuous.
In Mathlib's general `Measure` / `PMF` framework, using

* `ProbabilityTheory.exponentialMeasure : ℝ → Measure ℝ`,
* `ProbabilityTheory.pmfPoisson       : ℝ≥0 → PMF ℕ`,
* `ProbabilityTheory.pmfGeometric     : ℝ → PMF ℕ`,

the identity reads:

```lean
theorem exp_bind_poisson_eq_geometric (β : ℝ) (hβ : 0 < β) :
    (exponentialMeasure β).bind (fun lam => (pmfPoisson lam.toNNReal).toMeasure)
      = (pmfGeometric (β / (1 + β))).toMeasure := by
  -- pointwise:
  --   P(K = k) = ∫₀^∞ e^{-lam} lam^k / k! · β e^{-β lam} dlam
  --            = β / (1 + β)^{k+1}
  -- Core integral: Real.integral_rpow_mul_exp_neg / Real.Gamma_nat_eq_factorial
  --   ∫₀^∞ lam^k e^{-(1+β) lam} dlam = k! / (1 + β)^{k+1}
  -- Everything else: Measure.bind_apply + MeasureTheory.lintegral_…
  sorry
```

Sitting outside `DiscreteMeasure`, this naturally goes in a sibling
`ContinuousMixture/` directory rather than here.
-/

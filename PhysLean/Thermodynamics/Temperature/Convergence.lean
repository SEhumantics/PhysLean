/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import PhysLean.Thermodynamics.Temperature.Basic

/-!
# Convergence of inverse temperature maps

This file proves that as the inverse temperature `β` tends to infinity,
the temperature `ofβ β` tends to zero.

## Main results

* `Temperature.eventually_pos_ofβ`: `ofβ` eventually produces positive temperatures.
* `Temperature.tendsto_toReal_ofβ_atTop` : The real representation of `ofβ β`
  tends to `0` as `β → ∞`.
* `Temperature.tendsto_ofβ_atTop` : `ofβ β` tends to `0` from above as `β → ∞`.
-/

open NNReal

namespace Temperature
open Constants
open Filter Topology

/-- Lemma for `Temperature`:

The function `ofβ` produces strictly positive real-valued temperatures
for sufficiently large inverse temperature β.
-/
lemma eventually_pos_ofβ : ∀ᶠ b : ℝ≥0 in atTop, ((Temperature.ofβ b : Temperature) : ℝ) > 0 := by
  -- We start by proving that for sufficiently large `b : ℝ≥0`,
  -- we have `1 ≤ b` using `Filter.eventually_ge_atTop 1`,
  -- which states that eventually, all elements of the filter
  -- at infinity are greater than or equal to `1`.
  -- This gives us the hypothesis `h_eventually_b_ge_one`.
  have h_eventually_b_ge_one : ∀ᶠ b : ℝ≥0 in atTop, (1 : ℝ≥0) ≤ b := Filter.eventually_ge_atTop 1
  -- We then refine the goal using `h_eventually_b_ge_one.mono`,
  -- which allows us to prove the desired property for all `b` that satisfy `1 ≤ b`.
  -- The new goal is now `⊢ ∀ (x : ℝ≥0), 1 ≤ x → (ofβ x).toReal > 0`.
  refine h_eventually_b_ge_one.mono ?_
  -- We introduce `b : ℝ≥0` and the hypothesis `h_b_ge_one : 1 ≤ b` from the goal.
  -- The goal is now `⊢ (ofβ b).toReal > 0`.
  intro b h_b_ge_one
  -- We derive `h_b_pos : 0 < (b : ℝ)` using `zero_lt_one.trans_le h_b_ge_one`,
  -- which states that if `0 < 1` and `1 ≤ b`, then `0 < b`.
  have h_b_pos : 0 < (b : ℝ) := by
    exact zero_lt_one.trans_le h_b_ge_one
  -- We derive `h_denominator_pos : 0 < kB * (b : ℝ)` using `mul_pos kB_pos h_b_pos`,
  -- which states that if `kB` is positive (proven by `kB_pos`)
  -- and `b` is positive (proven by `h_b_pos`), then their product is positive.
  have h_denominator_pos : 0 < kB * (b : ℝ) := by
    exact mul_pos kB_pos h_b_pos
  -- We derive `h_quotient_pos : 0 < (1 : ℝ) / (kB * (b : ℝ))`
  -- using `one_div_pos.mpr h_denominator_pos`, which states that if the denominator is positive,
  -- then the reciprocal is also positive.
  have h_quotient_pos : 0 < (1 : ℝ) / (kB * (b : ℝ)) := one_div_pos.mpr h_denominator_pos
  -- We change the goal of `⊢ (ofβ b).toReal > 0` to its equivalent form
  -- `⊢ (fun b => 1 / (kB * ↑b)) b > 0`.
  change
    (λ (b : ℝ≥0) => (1 : ℝ) / (kB * b)) b > 0
  -- We can apply `h_quotient_pos` to conclude that the goal is true, since `h_quotient_pos` states
  -- that the expression `1 / (kB * (b : ℝ))` is positive, which is exactly what we need to show.
  -- QED.
  exact h_quotient_pos

/-- Helper lemma for `Temperature`:

Positivity of the epsilon-delta bound construction.
-/
private lemma tendsto_const_inv_mul_bound_pos (a ε : ℝ) (h_a_pos : 0 < a) (h_ε_pos : 0 < ε) :
    0 < (1 / (a * ε)) + 1 := by
  -- We derive `h_reciprocal_pos : 0 < (1 / (a * ε))` to show that the first term in the sum
  -- is positive, which will allow us to conclude that the entire sum is positive.
  have h_reciprocal_pos : 0 < (1 / (a * ε)) := by
    -- We derive `h_product_pos : 0 < a * ε` using `mul_pos h_a_pos h_ε_pos`,
    -- which states that the product of two positive numbers is positive
    -- (proof of `a` and `ε` being positive are given by `h_a_pos` and `h_ε_pos`).
    have h_product_pos : 0 < a * ε := by
      exact mul_pos h_a_pos h_ε_pos
    -- We then apply `one_div_pos.mpr h_product_pos` to conclude that `1 / (a * ε)` is positive,
    -- since `h_product_pos` states that the denominator is positive. QED for this part.
    exact one_div_pos.mpr h_product_pos
  -- Finally, we apply `add_pos` to `h_reciprocal_pos` and `zero_lt_one` to conclude that the sum
  -- `(1 / (a * ε)) + 1` is positive, since both terms are positive. QED.
  exact add_pos h_reciprocal_pos zero_lt_one

/-- Helper lemma for `Temperature`:

Product positivity via transitivity of ordering.
-/
private lemma tendsto_const_inv_mul_product_pos_of_le (a b_lower_bound b : ℝ) (h_a_pos : 0 < a)
    (h_b_lower_bound_pos : 0 < b_lower_bound) (h_b_lower_bound_le_b : b_lower_bound ≤ b) :
    0 < a * b := by
  -- We derive `h_b_pos : 0 < b` using `lt_of_lt_of_le h_b_lower_bound_pos h_b_lower_bound_le_b`,
  -- which states that if `b_lower_bound` is positive and `b_lower_bound ≤ b`,
  -- then `b` is also positive.
  have h_b_pos : 0 < b := lt_of_lt_of_le h_b_lower_bound_pos h_b_lower_bound_le_b
  -- We then apply `mul_pos` to `h_a_pos` and `h_b_pos` to conclude that the product
  -- `a * b` is positive. QED.
  exact mul_pos h_a_pos h_b_pos

/-- Helper lemma for `Temperature`:

Antitonicity of reciprocal function with constant multiplier.
-/
private lemma tendsto_const_inv_mul_reciprocal_antitone (a b_lower_bound b : ℝ) (h_a_pos : 0 < a)
    (h_product_b_lower_bound_pos : 0 < a * b_lower_bound)
    (h_b_lower_bound_le_b : b_lower_bound ≤ b) :
    (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound) := by
  -- We derive `h_denom_le : (a * b_lower_bound) ≤ (a * b)`
  -- using `mul_le_mul_of_nonneg_left h_b_lower_bound_le_b (le_of_lt h_a_pos)`, which states that
  -- if `b_lower_bound ≤ b` and `a` is non-negative, then multiplying both sides by `a` preserves
  -- the inequality, giving us `a * b_lower_bound ≤ a * b`.
  have h_denom_le : (a * b_lower_bound) ≤ (a * b) := by
    exact mul_le_mul_of_nonneg_left h_b_lower_bound_le_b (le_of_lt h_a_pos)
  -- Then we apply `one_div_le_one_div_of_le` to `h_product_b_lower_bound_pos` and `h_denom_le`
  -- to conclude that the reciprocal of the larger denominator is less than or equal to the
  -- reciprocal of the smaller denominator, which establishes the antitonicity. QED.
  exact one_div_le_one_div_of_le h_product_b_lower_bound_pos h_denom_le

/-- Helper lemma for `Temperature`:

Evaluating the function at the constructed bound yields a value less than `ε`.
-/
private lemma tendsto_const_inv_mul_at_bound_lt_epsilon (a ε : ℝ) (h_a_pos : 0 < a)
    (h_ε_pos : 0 < ε) :
    (1 : ℝ) / (a * ((1 / (a * ε)) + 1)) < ε := by
  -- We first simplify the expression by performing field simplification with `field_simp`
  -- to rewrite the goal into `⊢ 1 < 1 + a * ε`.
  field_simp
  -- We then simplify further using `simp` to reduce the goal to `⊢ 0 < a * ε`.
  simp
  -- We derive `h_product_pos : 0 < a * ε` using `mul_pos h_a_pos h_ε_pos`,
  -- which states that the product of two positive numbers is positive.
  have h_product_pos : 0 < a * ε := by
    exact mul_pos h_a_pos h_ε_pos
  -- Finally, we conclude that `⊢ 0 < a * ε` is true by `h_product_pos`. QED.
  exact h_product_pos

/-- Helper lemma for `Temperature`:

Conversion from nonnegative inequality to metric space distance.
-/
private lemma tendsto_const_inv_mul_nonneg_to_dist (x ε : ℝ) (h_x_nonneg : 0 ≤ x)
    (h_x_lt_ε : x < ε) :
    dist x 0 < ε := by
  -- We rewrite the goal `⊢ dist x 0 < ε` using `Real.dist_eq` to express the distance
  -- in terms of absolute value (`dist x 0` is equal to `|x - 0|`),
  -- and use `sub_zero` to simplify this to `⊢ |x| < ε`.
  rw [Real.dist_eq, sub_zero]
  -- We derive `h_abs_lt : |x| < ε`, by rewriting `|x|` as `x` using `abs_of_nonneg h_x_nonneg`,
  -- which states that if `x` is nonnegative, then `|x|` is equal to `x`.
  -- Then we apply `h_x_lt_ε` to conclude that `|x| < ε` is true.
  have h_abs_lt : |x| < ε := by
    rw [abs_of_nonneg h_x_nonneg]
    exact h_x_lt_ε
  -- Finally, we conclude that `⊢ |x| < ε` is true by `h_abs_lt`. QED.
  exact h_abs_lt

/-- Helper lemma for `Temperature`:

Given a lower bound on `b` that ensures the function value is less than `ε`,
we can conclude that for any `b` greater than or equal to that lower bound,
the function value is nonnegative and less than `ε`.
-/
private lemma tendsto_const_inv_mul_nonneg_and_lt_of_bound (a ε b_lower_bound b : ℝ)
    (h_a_pos : 0 < a)(h_b_lower_bound_pos : 0 < b_lower_bound)
    (h_b_lower_bound_le_b : b_lower_bound ≤ b) (h_at_bound_lt : (1 : ℝ) / (a * b_lower_bound) < ε) :
    0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε := by
  -- We derive `h_prod_lower_bound_pos : 0 < a * b_lower_bound`
  -- using `mul_pos h_a_pos h_b_lower_bound_pos`, which states that the product of
  -- two positive numbers is positive (proof of `a` and `b_lower_bound` being positive are given by
  -- `h_a_pos` and `h_b_lower_bound_pos`).
  have h_prod_lower_pos : 0 < a * b_lower_bound := by
    exact mul_pos h_a_pos h_b_lower_bound_pos
  -- We then derive `h_prod_pos : 0 < a * b` using the previous lemma
  -- `tendsto_const_inv_mul_product_pos_of_le`, which states that if `b` is greater than or equal
  -- to a positive lower bound, then the product `a * b` is also positive.
  have h_prod_pos : 0 < a * b := by
    exact tendsto_const_inv_mul_product_pos_of_le a b_lower_bound b
          h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b
  -- We then derive `h_rec_le : (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound)`
  -- using the previous lemma `tendsto_const_inv_mul_reciprocal_antitone`,
  -- which states that the reciprocal function is antitone.
  have h_rec_le : (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound) := by
    exact tendsto_const_inv_mul_reciprocal_antitone a b_lower_bound b
          h_a_pos h_prod_lower_pos h_b_lower_bound_le_b
  -- We then derive `h_lt : (1 : ℝ) / (a * b) < ε` using `lt_of_le_of_lt h_rec_le h_at_bound_lt`,
  -- which states that if `1 / (a * b)` is less than or equal to `1 / (a * b_lower_bound)`
  -- and `1 / (a * b_lower_bound)` is less than `ε`, then `1 / (a * b)` is also less than `ε`.
  have h_lt : (1 : ℝ) / (a * b) < ε := by
    exact lt_of_le_of_lt h_rec_le h_at_bound_lt
  -- We then derive `h_nonneg : 0 ≤ (1 : ℝ) / (a * b)`
  -- using `div_nonneg zero_le_one (le_of_lt h_prod_pos)`,
  -- which states that the reciprocal of a positive number is nonnegative.
  have h_nonneg : 0 ≤ (1 : ℝ) / (a * b) := by
    exact div_nonneg zero_le_one (le_of_lt h_prod_pos)
  -- Finally, we conclude that both `0 ≤ (1 : ℝ) / (a * b)` and `(1 : ℝ) / (a * b) < ε` hold by
  -- the proofs of `h_nonneg` and `h_lt`. QED.
  exact ⟨h_nonneg, h_lt⟩

/-- Helper lemma for `Temperature`:

Given a lower bound on `b` that ensures the function value is less than `ε`,
we can conclude that for any `b` greater than or equal to that lower bound,
the distance from the function value to `0` is less than `ε`.
-/
private lemma tendsto_const_inv_mul_dist_lt_of_bound (a ε b_lower_bound b : ℝ)
    (h_a_pos : 0 < a) (h_b_lower_bound_pos : 0 < b_lower_bound)
    (h_b_lower_bound_le_b : b_lower_bound ≤ b) (h_at_bound_lt : (1 : ℝ) / (a * b_lower_bound) < ε) :
    dist ((1 : ℝ) / (a * b)) (0 : ℝ) < ε := by
  -- We derive `h_nonneg_and_lt : 0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε`
  -- using the previous lemma `tendsto_const_inv_mul_nonneg_and_lt_of_bound`,
  -- which states that for any `b` greater than or equal to the lower bound,
  -- the function value is nonnegative and less than `ε`.
  have h_nonneg_and_lt : 0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε :=
    tendsto_const_inv_mul_nonneg_and_lt_of_bound a ε b_lower_bound b
      h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b h_at_bound_lt
  -- Finally, we apply the previous lemma `tendsto_const_inv_mul_nonneg_to_dist` to conclude that
  -- the distance from the function value to `0` is less than `ε`, since we have established that
  -- the function value is nonnegative and less than `ε`. QED.
  exact tendsto_const_inv_mul_nonneg_to_dist ((1 : ℝ) / (a * b)) ε
        h_nonneg_and_lt.left h_nonneg_and_lt.right

/-- Helper lemma for `Temperature`:

As `b` tends to infinity, the distance from the function value `1 / (a * b)` to `0`
becomes less than any positive `ε` for sufficiently large `b`.

(TODO)
-/
private lemma tendsto_const_inv_mul_atTop_eventually_dist_lt (a : ℝ) (h_a_pos : 0 < a) (ε : ℝ)
    (h_ε_pos : 0 < ε) : ∀ᶠ b :
    ℝ≥0 in atTop, dist ((1 : ℝ) / (a * (b : ℝ))) (0 : ℝ) < ε := by
  -- We construct a real number `B_real` defined as `(1 / (a * ε)) + 1`,
  -- which serves as a candidate lower bound for `b` to ensure that the function value
  -- is less than `ε`.
  let B_real : ℝ := (1 / (a * ε)) + 1
  -- We then derive `h_B_real_pos : 0 < B_real` using the previous lemma
  -- `tendsto_const_inv_mul_bound_pos`, which states that the constructed bound is positive.
  have h_B_real_pos : 0 < B_real := by
    exact tendsto_const_inv_mul_bound_pos a ε h_a_pos h_ε_pos
  -- We then define a nonnegative real number `B_nnreal` by taking the nonnegative part of
  -- `B_real`, ensuring that it is still positive.
  let B_nnreal : ℝ≥0 := ⟨B_real, le_of_lt h_B_real_pos⟩
  -- We then derive `h_B_nnreal_pos : 0 < (B_nnreal : ℝ)` from `h_B_real_pos`
  -- by noting that the coercion of `B_nnreal` to `ℝ` is exactly `B_real`, which is positive. QED.
  have h_B_nnreal_pos : 0 < B_nnreal:= by
    exact h_B_real_pos
  -- We then refine the goal using `Filter.eventually_ge_atTop B_nnreal`,
  -- which states that eventually, all elements of the filter at infinity are greater than or equal
  -- to `B_nnreal`. The goal is now `⊢ ∀ (x : ℝ≥0), B_nnreal ≤ x → dist (1 / (a * ↑x)) 0 < ε`.
  refine (Filter.eventually_ge_atTop B_nnreal).mono ?_
  -- We introduce `b : ℝ≥0` and the hypothesis `h_B_nnreal_le_b : B_nnreal ≤ b` from the goal.
  --The goal is now `⊢ dist (1 / (a * ↑b)) 0 < ε`.
  intro b h_B_nnreal_le_b
  -- We derive `h_atB_lt : (1 : ℝ) / (a * (B_nnreal : ℝ)) < ε` using the previous lemma
  -- `tendsto_const_inv_mul_at_bound_lt_epsilon`, which states that evaluating the function
  -- at the constructed bound yields a value less than `ε`.
  have h_atB_lt : (1 : ℝ) / (a * (B_nnreal : ℝ)) < ε := by
    exact tendsto_const_inv_mul_at_bound_lt_epsilon a ε h_a_pos h_ε_pos
  -- Finally, we apply `tendsto_const_inv_mul_dist_lt_of_bound`
  -- to conclude that the distance from the function value to `0` is less than `ε`
  -- for any `b` greater than or equal to the constructed bound. QED.
  exact tendsto_const_inv_mul_dist_lt_of_bound a ε (B_nnreal : ℝ) (b : ℝ)
        h_a_pos h_B_nnreal_pos h_B_nnreal_le_b h_atB_lt

/-- Helper lemma for `Temperature`:

As `b` tends to infinity, the function value `1 / (a * b)` tends to `0`
in the sense of the metric space distance.
-/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (h_a_pos : 0 < a) :
    Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  -- We refine the goal using `Metric.tendsto_nhds.mpr`,
  -- which allows us to prove the convergence by showing that for every positive `ε`,
  -- the function values are eventually within `ε` of `0`.
  -- The new goal is now `⊢ ∀ ε > 0, ∀ᶠ (x : ℝ≥0) in atTop, dist (1 / (a * ↑x)) 0 < ε`.
  refine Metric.tendsto_nhds.mpr ?_
  -- We introduce `ε : ℝ` and the hypothesis `h_ε_pos : 0 < ε` from the goal.
  -- The goal is now `⊢ ∀ᶠ (x : ℝ≥0) in atTop, dist (1 / (a * ↑x)) 0 < ε`.
  intro ε h_ε_pos
  -- We apply the previous lemma `tendsto_const_inv_mul_atTop_eventually_dist_lt`
  -- to conclude that for sufficiently large `b`, the distance from the function value to `0`
  -- is less than `ε`. QED.
  exact tendsto_const_inv_mul_atTop_eventually_dist_lt a h_a_pos ε h_ε_pos

/-- Lemma for `Temperature`:

As the inverse temperature `β` tends to infinity,
the real-valued representation of the temperature `ofβ β` tends to `0`
in the sense of the metric space distance.
-/
lemma tendsto_toReal_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  -- We apply the previous lemma `tendsto_const_inv_mul_atTop`
  -- with `a` set to `kB` and `h_a_pos` set to `kB_pos`,
  -- which states that as `b` tends to infinity, the function value `1 / (kB * b)` tends to `0`.
  -- Since `ofβ b` is defined as `1 / (kB * b)`, this directly implies the desired convergence. QED.
  exact tendsto_const_inv_mul_atTop kB kB_pos

/-- Lemma for `Temperature`:

As the inverse temperature `β` tends to infinity,
the real-valued representation of the temperature `ofβ β`
tends to `0` from above (within the interval `(0, ∞)`).
-/
lemma tendsto_ofβ_atTop :
    Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  -- We derive `h_tendsto_nhds_zero` from
  -- `tendsto_toReal_ofβ_atTop`, which states that as `β`
  -- tends to infinity, the real-valued temperature
  -- tends to `0` in the nhds sense.
  have h_tendsto_nhds_zero := tendsto_toReal_ofβ_atTop
  -- We derive `h_tendsto_principal_Ioi` which states that
  -- as `β` tends to infinity, the real-valued temperature
  -- eventually lies in the interval `(0, ∞)`, using
  -- `tendsto_principal.mpr` and `eventually_pos_ofβ`.
  have h_tendsto_principal_Ioi :
      Tendsto (fun b : ℝ≥0 =>
        (Temperature.ofβ b : ℝ))
        atTop (𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_principal.mpr
      (by simpa using Temperature.eventually_pos_ofβ)
  -- We combine `h_tendsto_nhds_zero` and
  -- `h_tendsto_principal_Ioi` using `tendsto_inf.mpr` to
  -- conclude that the function tends to `0` within the
  -- infimum filter `nhds 0 ⊓ 𝓟 (Set.Ioi 0)`.
  have h_tendsto_inf :
      Tendsto (fun b : ℝ≥0 =>
        (Temperature.ofβ b : ℝ))
        atTop
        ((nhds (0 : ℝ)) ⊓ 𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_inf.mpr
      ⟨h_tendsto_nhds_zero, h_tendsto_principal_Ioi⟩
  -- Since `nhdsWithin 0 (Set.Ioi 0)` is defined as
  -- `nhds 0 ⊓ 𝓟 (Set.Ioi 0)`, the conclusion follows
  -- directly from `h_tendsto_inf` by simplification.
  -- QED.
  simpa [nhdsWithin] using h_tendsto_inf

end Temperature

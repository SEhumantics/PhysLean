/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import PhysLean.Thermodynamics.Temperature.Basic

/-!
# Calculus relating temperature and inverse temperature

This file establishes the derivative of `β` with respect to temperature `T`,
and provides a chain rule for composing functions of `β` with the
temperature-to-beta map.

## Main results

* `Temperature.βFromReal` : Map a real `t` to `β(ofNNReal(toNNReal t))`.
* `Temperature.β_fun_T_formula` : Closed form `βFromReal t = 1 / (kB * t)` for `t > 0`.
* `Temperature.deriv_β_wrt_T` : The derivative of `βFromReal` is `-1 / (kB * T²)`.
* `Temperature.chain_rule_T_β` : Chain rule for composing through `βFromReal`.
-/

open NNReal

namespace Temperature
open Constants
open Set
open scoped ENNReal

/-- Function for `Temperature`:

Map a real number `t` to the inverse temperature `β` corresponding to
the temperature `Real.toNNReal t` (`max t 0`), returned as a real number.

- Note:

1. Why `ℝ` instead of `ℝ≥0`, if `β` is of type `ℝ≥0`?
-/
noncomputable def βFromReal (t : ℝ) : ℝ := ((Temperature.ofNNReal (Real.toNNReal t)).β)

/-- Lemma for `Temperature`:

Explicit closed-form for `βFromReal t` when `t > 0`: `βFromReal t = 1 / (kB * t)`.
-/
lemma β_fun_T_formula (t : ℝ) (h_t_pos : 0 < t) :
    βFromReal t = (1 :  ℝ) / (kB * t) := by
  -- We derive `h_t_nonneg : 0 ≤ t` from `h_t_pos` by weakening strict
  -- inequality to non-strict inequality.
  have h_t_nonneg : (0 : ℝ) ≤ t := h_t_pos.le
  -- We derive `h_beta_formula` which states that the explicit formula
  -- for `β` applied to `Real.toNNReal t` equals `1 / (kB * t)`,
  -- by simplifying using the definitions of `β`, `ofNNReal`, `toReal`,
  -- and the fact that `Real.toNNReal t = t` when `t ≥ 0`.
  have h_beta_formula :
      ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ) = (1 :  ℝ) / (kB * t) := by
    simp [Temperature.β, Temperature.ofNNReal, Temperature.toReal,
          Real.toNNReal_of_nonneg h_t_nonneg, one_div, mul_comm]
  -- We conclude by simplifying the definition of `βFromReal` and
  -- applying `h_beta_formula`. QED.
  simpa [βFromReal] using h_beta_formula

/-- Lemma for `Temperature`:

On the interval `(0, ∞)`, `βFromReal t` equals `1 / (kB * t)`.
-/
lemma β_fun_T_eq_on_Ioi : EqOn βFromReal (fun t : ℝ => (1 :  ℝ) / (kB * t)) (Set.Ioi 0) := by
  -- We introduce `t : ℝ` and the hypothesis
  -- `h_t_pos : t ∈ Set.Ioi 0` (i.e. `0 < t`) from the goal.
  intro t h_t_pos
  -- We simplify `h_t_pos` to extract the inequality `0 < t`.
  simp at h_t_pos
  -- We apply `β_fun_T_formula t h_t_pos` to conclude that
  -- `βFromReal t = 1 / (kB * t)`. QED.
  exact β_fun_T_formula t h_t_pos

/-- Lemma for `Temperature`:

The function `βFromReal` has derivative `-1 / (kB * T²)` within the
interval `(0, ∞)` at the point `T.val`, when `T` is strictly positive.
-/
lemma deriv_β_wrt_T (T : Temperature) (h_T_pos : 0 < T.val) : HasDerivWithinAt βFromReal
    (-1 / (kB * (T.val : ℝ)^2)) (Set.Ioi 0) (T.val : ℝ) := by
  -- We define `f : ℝ → ℝ` as the explicit formula
  -- `f t = 1 / (kB * t)`, which is the closed form of
  -- `βFromReal` on `(0, ∞)`.
  let f : ℝ → ℝ := fun t => (1 :  ℝ) / (kB * t)
  -- We derive `h_eq_on : EqOn βFromReal f (Set.Ioi 0)`
  -- using `β_fun_T_eq_on_Ioi`, which states that
  -- `βFromReal` and `f` agree on `(0, ∞)`.
  have h_eq_on : EqOn βFromReal f (Set.Ioi 0) :=
    β_fun_T_eq_on_Ioi
  -- We derive `h_T_ne_zero : (T.val : ℝ) ≠ 0` from
  -- `h_T_pos` using `ne_of_gt`, since a strictly positive
  -- number is nonzero.
  have h_T_ne_zero : (T.val : ℝ) ≠ 0 :=
    ne_of_gt h_T_pos
  -- We derive `h_f_def` which rewrites `f` in terms of
  -- inverses: `f = fun t => kB⁻¹ * t⁻¹`, by case-splitting
  -- on whether `t = 0` and simplifying.
  have h_f_def :
      f = fun t : ℝ => (kB)⁻¹ * t⁻¹ := by
    funext t
    -- We case-split on whether `t = 0`.
    by_cases h_t_eq_zero : t = 0
    -- If `t = 0`, both sides simplify to `0`.
    · simp [f, h_t_eq_zero]
    -- If `t ≠ 0`, we simplify and apply `ring`. QED.
    · simp [f, one_div, *] at *
      ring
  -- We derive `h_inv` which states that the derivative of
  -- `t⁻¹` at `T.val` is `-(T.val²)⁻¹`, using
  -- `hasDerivAt_inv` with `h_T_ne_zero`.
  have h_inv :
      HasDerivAt (fun t : ℝ => t⁻¹)
        (-((T.val : ℝ) ^ 2)⁻¹) (T.val : ℝ) := by
    simpa using
      (hasDerivAt_inv (x := (T.val : ℝ)) h_T_ne_zero)
  -- We derive `h_deriv_aux` which states the derivative of
  -- `kB⁻¹ * t⁻¹` at `T.val` is `kB⁻¹ * (-(T.val²)⁻¹)`,
  -- by applying the constant-multiple rule to `h_inv`.
  have h_deriv_aux :
      HasDerivAt (fun t : ℝ => (kB)⁻¹ * t⁻¹)
        ((kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹))
        (T.val : ℝ) :=
    h_inv.const_mul ((kB)⁻¹)
  -- We derive `h_pow_simp` which simplifies the derivative
  -- expression `kB⁻¹ * (-(T.val²)⁻¹)` to the target form
  -- `-1 / (kB * T.val²)`, using algebraic manipulations.
  have h_pow_simp :
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹) =
        -1 / (kB * (T.val : ℝ)^2) := by
    calc
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹)
          = -((kB)⁻¹ * ((T.val : ℝ) ^ 2)⁻¹) := by
            ring
      _ = -(1 / kB * (1 / (T.val : ℝ) ^ 2)) := by
            simp [one_div]
      _ = -1 / (kB * (T.val : ℝ) ^ 2) := by
        rw [one_div]
        field_simp [pow_two, mul_comm,
          mul_left_comm, mul_assoc,
          kB_ne_zero, h_T_ne_zero]
  -- We derive `h_deriv_f` which states that `f` has
  -- derivative `-1 / (kB * T.val²)` at `T.val`, by
  -- combining `h_f_def`, `h_pow_simp`, and `h_deriv_aux`.
  have h_deriv_f :
      HasDerivAt f
        (-1 / (kB * (T.val : ℝ)^2))
        (T.val : ℝ) := by
    simpa [h_f_def, h_pow_simp] using h_deriv_aux
  -- We derive `h_mem : (T.val : ℝ) ∈ Set.Ioi 0` from
  -- `h_T_pos`, confirming that the evaluation point lies
  -- in the domain.
  have h_mem : (T.val : ℝ) ∈ Set.Ioi (0 : ℝ) :=
    h_T_pos
  -- We conclude by converting `h_deriv_f` to a
  -- `HasDerivWithinAt` and applying `congr` with `h_eq_on`
  -- to replace `f` by `βFromReal` on the set. QED.
  exact (h_deriv_f.hasDerivWithinAt).congr
    h_eq_on (h_eq_on h_mem)

/-- Lemma for `Temperature`:

Chain rule for `β(T)`: if `F` has derivative `F'` at `β(T)` within
`(0, ∞)`, then the composition `t ↦ F(βFromReal(t))` has derivative
`F' * (-1 / (kB * T²))` within `(0, ∞)` at `T.val`.
-/
lemma chain_rule_T_β {F : ℝ → ℝ} {F' : ℝ}
    (T : Temperature) (h_T_pos : 0 < T.val)
    (h_F_deriv : HasDerivWithinAt F F' (Set.Ioi 0) (T.β : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => F (βFromReal t))
    (F' * (-1 / (kB * (T.val : ℝ)^2)))
    (Set.Ioi 0) (T.val : ℝ) := by
  -- We derive `h_β_deriv` from `deriv_β_wrt_T`, which
  -- gives the derivative of `βFromReal` at `T.val`.
  have h_β_deriv :=
    deriv_β_wrt_T (T := T) h_T_pos
  -- We derive `h_maps_to` which states that `βFromReal`
  -- maps `(0, ∞)` into `(0, ∞)`, i.e. positive inputs
  -- produce positive outputs.
  have h_maps_to :
      Set.MapsTo βFromReal (Set.Ioi 0) (Set.Ioi 0) := by
    -- We introduce `t : ℝ` and the hypothesis
    -- `h_t_pos : t ∈ Set.Ioi 0` (i.e. `0 < t`).
    intro t h_t_pos
    -- We derive `h_kB_mul_t_pos : 0 < kB * t` using
    -- `mul_pos kB_pos h_t_pos`.
    have h_kB_mul_t_pos : 0 < kB * t :=
      mul_pos kB_pos h_t_pos
    -- We derive `h_quotient_pos : 0 < 1 / (kB * t)` using
    -- `one_div_pos.mpr h_kB_mul_t_pos`.
    have h_quotient_pos : 0 < (1 :  ℝ) / (kB * t) :=
      one_div_pos.mpr h_kB_mul_t_pos
    -- We derive `h_βFromReal_eq` which states that
    -- `βFromReal t = 1 / (kB * t)` on `(0, ∞)`.
    have h_βFromReal_eq :
        βFromReal t = (1 :  ℝ) / (kB * t) :=
      β_fun_T_eq_on_Ioi h_t_pos
    -- We conclude by rewriting `βFromReal t` with
    -- `h_βFromReal_eq` and applying `h_quotient_pos`. QED.
    simpa [h_βFromReal_eq] using h_quotient_pos
  -- We derive `h_β_at_T` which states that
  -- `βFromReal (T.val : ℝ) = (T.β : ℝ)`, i.e. the
  -- explicit formula agrees with the definition of `β`.
  have h_β_at_T :
      βFromReal (T.val : ℝ) = (T.β : ℝ) := by
    -- We derive `h_T_pos_real : 0 < (T.val : ℝ)` from
    -- `h_T_pos`.
    have h_T_pos_real : 0 < (T.val : ℝ) := h_T_pos
    -- We derive `h_βFromReal_eq_at_T` from
    -- `β_fun_T_eq_on_Ioi h_T_pos_real`.
    have h_βFromReal_eq_at_T :=
      β_fun_T_eq_on_Ioi h_T_pos_real
    -- We conclude by simplifying with the definitions of
    -- `β` and `toReal`. QED.
    simpa [Temperature.β, Temperature.toReal]
      using h_βFromReal_eq_at_T
  -- We derive `h_F_deriv_at_βFromReal` which rewrites
  -- `h_F_deriv` to use `βFromReal (T.val)` instead of
  -- `(T.β : ℝ)`, using `h_β_at_T`.
  have h_F_deriv_at_βFromReal :
      HasDerivWithinAt F F'
        (Set.Ioi 0) (βFromReal (T.val : ℝ)) := by
    simpa [h_β_at_T] using h_F_deriv
  -- We derive `h_composition` by applying the chain rule
  -- (`HasDerivWithinAt.comp`) to compose `F` with
  -- `βFromReal`, using `h_F_deriv_at_βFromReal`,
  -- `h_β_deriv`, and `h_maps_to`.
  have h_composition :=
    h_F_deriv_at_βFromReal.comp
      (T.val : ℝ) h_β_deriv h_maps_to
  -- We conclude by simplifying `h_composition` with
  -- `mul_comm` to match the target derivative expression.
  -- QED.
  simpa [mul_comm] using h_composition

end Temperature

/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Meta.Types.PosReal

/-!
# Calculus relating temperature and inverse temperature

This file establishes the derivative of `β` with respect to (positive) temperature `T`,
and provides a chain rule for composing functions of `β` with the
temperature-to-beta map, leveraging `PositiveTemperature`.

## Main results

* `PositiveTemperature.deriv_β_wrt_T` : The derivative of the `β` formula is `-1 / (kB * T²)`.
* `PositiveTemperature.chain_rule_T_β` : Chain rule for composing through the `β` formula.
-/

open NNReal

namespace PositiveTemperature
open Constants
open Set


/-- Lemma for `PositiveTemperature`:

The real-valued function mapping `t ↦ 1 / (kB * t)` has the full derivative
`-1 / (kB * T²)` at the evaluation point `(T : ℝ)`.

Note that `t` is a positive real variable, since it represents positive temperature.
-/
lemma deriv_β_wrt_T (T : PositiveTemperature) : HasDerivAt (fun (t : ℝ) => (1 : ℝ) / (kB * t))
    (-1 / (kB * (T : ℝ)^2)) (T : ℝ) := by
  -- We derive `h_T_ne_zero` from the type property `T : ℝ>0`.
  have h_T_ne_zero : (T : ℝ) ≠ 0 := by
    exact ne_of_gt T.zero_lt_toReal

  -- We derive `h_f_def` to rewrite the original function `1 / (kB * t)`
  -- into the more convenient form `(kB)⁻¹ * t⁻¹`.
  have h_f_def : (fun (t : ℝ) => (1 : ℝ) / (kB * t)) = fun (t : ℝ) => (kB)⁻¹ * t⁻¹ := by
    -- Simplify the original function using `one_div` and `mul_inv_rev` to get the desired form.
    -- The goal is now `⊢ (fun t => t⁻¹ * kB⁻¹) = fun t => kB⁻¹ * t⁻¹`.
    simp only [one_div, mul_inv_rev]
    -- As the goal is now an equality of two functions,
    -- we can apply `funext` to reduce it to a pointwise equality.
    -- The goal is now `T⁻¹ * kB⁻¹ = kB⁻¹ * T⁻¹`
    funext T
    -- Finally, we can use `ring` to verify the commutativity of multiplication
    -- in the pointwise equality. QED.
    ring

  -- We derive `h_t_inv_deriv` to compute the derivative of the inner function `t ↦ t⁻¹`
  -- as `-((T : ℝ) ^ 2)⁻¹` at the evaluation point `(T : ℝ)`.
  have h_t_inv_deriv : HasDerivAt (fun (t : ℝ) => t⁻¹)
      (-((T : ℝ) ^ 2)⁻¹) (T : ℝ) := by
    -- We can directly prove there exists a strict derivative for the function `t ↦ t⁻¹`
    -- with `hasDerivAt_inv`, given that the evaluation point `(T : ℝ)` is nonzero.
    exact (hasDerivAt_inv (x := (T : ℝ)) h_T_ne_zero)

  -- We apply the constant-multiple rule:
  -- If `f` has derivative `f'` at `x`, then `c * f` has derivative `c * f'` at `x`.
  have h_deriv_aux : HasDerivAt (fun (t : ℝ) => (kB)⁻¹ * t⁻¹)
      ((kB)⁻¹ * (-((T : ℝ) ^ 2)⁻¹)) (T : ℝ) := by
    -- As we have `h_t_inv_deriv` that proves the existence of the derivative of `t ↦ t⁻¹`,
    -- we can apply the constant-multiply rule `hasDerivAt.const_mul`
    -- to conclude the derivative of `t ↦ (kB)⁻¹ * t⁻¹`.
    exact h_t_inv_deriv.const_mul ((kB)⁻¹)

  -- We rewrite the goal using `h_f_def` to express the original function in terms of the simpler form.
  rw [h_f_def]

  -- We use `convert` to unify the goal with `h_deriv_aux` up to `1` level of congruence,
  -- reducing it to an equality of derivative values.
  convert h_deriv_aux using 1

  -- Finally, we can use `ring` to verify the algebraic manipulation of the derivative expression
  -- to match the desired form `-1 / (kB * T²)`. QED.
  ring

/-- Lemma for `PositiveTemperature`:

Chain rule for `β(T)`:

- If `F` is a real-valued function of a real variable,
and `F` has a derivative `F'` at the point `β(T)`,
then the composition function `F(β(T))` or `t ↦ F(1 / (kB * t))` has a derivative
`F' * (-1 / (kB * T²))` at the evaluation point `(T : ℝ)`.
-/
lemma chain_rule_T_β {F : ℝ → ℝ} {F' : ℝ} (T : PositiveTemperature)
    (h_F_deriv : HasDerivAt F F' (β T : ℝ)) : HasDerivAt (fun (t : ℝ) => F ((1 : ℝ) / (kB * t)))
    (F' * (-1 / (kB * (T : ℝ)^2))) (T : ℝ) := by
  -- We derive `h_β_deriv` from the previous lemma `deriv_β_wrt_T`
  -- to establish the fact that `β(T)` has a derivative of `-1 / (kB * T²)`
  -- at the evaluation point `(T : ℝ)`.
  have h_β_deriv := deriv_β_wrt_T T

  -- We derive `h_comp` by applying the `HasDerivAt.comp` rule
  -- to compose the derivatives of `F` and `β(T)`.
  have h_comp := h_F_deriv.comp (T : ℝ) h_β_deriv

  -- We use `convert` to unify the goal with `h_comp` up to `1` level of congruence,
  -- reducing it to an equality of derivative values. QED.
  convert h_comp using 1

end PositiveTemperature

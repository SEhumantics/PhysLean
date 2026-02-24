/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
/-!
# Units on Temperature === TODO TIL THE END OF THE FILE

A unit of temperature interval corresponds to a choice of
translationally-invariant metric on the temperature manifold (to be
defined diffeomorphic to `ℝ≥0`). Such a choice is (non-canonically)
equivalent to a choice of positive real number. We define the type
`TemperatureUnit` to be equivalent to the positive reals.

On `TemperatureUnit` there is an instance of division giving a real
number, corresponding to the ratio of the two interval scales.

To define specific temperature units, we first state the existence of
a given temperature unit, and then construct all other temperature
units from it. We choose to state the existence of the temperature
unit of kelvin, and construct all other temperature units from that.
-/

open NNReal

/-- The type `TemperatureUnit` represents a choice of
  translationally-invariant metric on the temperature-manifold,
  corresponding to a multiplicative choice of unit scale for
  temperature intervals.
  - `val` of type `ℝ`: The underlying scale of the unit.
  - `property` of type `0 < val`: Proof that the scale is strictly
    positive.
-/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  /-- Proof that the scale is strictly positive. -/
  property : 0 < val

namespace TemperatureUnit

/-- Simplification lemma for `TemperatureUnit`:

The value of a temperature unit is nonzero.
-/
@[simp]
lemma val_ne_zero (x : TemperatureUnit) : x.val ≠ 0 := by
  -- Since `x.val > 0` (by `x.property`), it follows that
  -- `x.val ≠ 0` by `Ne.symm` applied to `ne_of_lt x.property`.
  -- QED.
  exact Ne.symm (ne_of_lt x.property)

/-- Lemma for `TemperatureUnit`:

The value of a temperature unit is strictly positive.
-/
lemma val_pos (x : TemperatureUnit) : 0 < x.val :=
  x.property

/-- Default instance for `TemperatureUnit`, set to scale `1`.
-/
instance : Inhabited TemperatureUnit where
  default := ⟨1, by norm_num⟩

/-!
## Division of TemperatureUnit
-/

/-- Division of two `TemperatureUnit` values, yielding a nonnegative
ratio in `ℝ≥0`.
-/
noncomputable instance :
    HDiv TemperatureUnit TemperatureUnit ℝ≥0 where
  hDiv x t :=
    ⟨x.val / t.val,
      div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩

/-- Lemma for `TemperatureUnit`:

Division unfolds to the ratio of underlying values.
-/
lemma div_eq_val (x y : TemperatureUnit) :
    x / y =
      (⟨x.val / y.val,
        div_nonneg (le_of_lt x.val_pos)
          (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl

/-- Simplification lemma for `TemperatureUnit`:

The division of two temperature units is nonzero.
-/
@[simp]
lemma div_ne_zero (x y : TemperatureUnit) :
    ¬ x / y = (0 : ℝ≥0) := by
  -- We rewrite the goal using the definition of division
  -- from `div_eq_val`, which unfolds the division into the
  -- ratio of underlying values.
  rw [div_eq_val]
  -- We refine the goal using `coe_ne_zero.mp`, which
  -- reduces the nonzero condition on `ℝ≥0` to a condition
  -- on the underlying `ℝ` values.
  refine coe_ne_zero.mp ?_
  -- We simplify to conclude, since `x.val / y.val ≠ 0`
  -- follows from both values being strictly positive. QED.
  simp

/-- Simplification lemma for `TemperatureUnit`:

The division of two temperature units is strictly positive.
-/
@[simp]
lemma div_pos (x y : TemperatureUnit) :
    (0 : ℝ≥0) < x / y := by
  -- We apply `lt_of_le_of_ne` to show strict positivity
  -- from nonnegativity and the fact that the division is
  -- nonzero.
  apply lt_of_le_of_ne
  -- `case ha`: The goal is `⊢ 0 ≤ x / y`, which is true
  -- since `x / y : ℝ≥0` is nonnegative by definition.
  -- QED for this case.
  · exact zero_le (x / y)
  -- `case hb`: The goal is `⊢ 0 ≠ x / y`, which follows
  -- from `div_ne_zero x y` by symmetry. QED for this case.
  -- All cases have been proven. QED.
  · exact Ne.symm (div_ne_zero x y)

/-- Simplification lemma for `TemperatureUnit`:

Dividing a temperature unit by itself yields `1`.
-/
@[simp]
lemma div_self (x : TemperatureUnit) :
    x / x = (1 : ℝ≥0) := by
  -- We simplify using the definition of division and the
  -- fact that `x.val ≠ 0`. QED.
  simp [div_eq_val, x.val_ne_zero]

/-- Lemma for `TemperatureUnit`:

Division is the inverse of the reverse division.
-/
lemma div_symm (x y : TemperatureUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  -- We rewrite both sides using `div_eq_val` and
  -- `inv_eq_one_div` to express them in terms of
  -- underlying values.
  rw [div_eq_val, inv_eq_one_div, div_eq_val]
  -- We simplify to conclude, since the algebraic identity
  -- `x / y = (y / x)⁻¹` holds for positive reals. QED.
  simp

/-- Simplification lemma for `TemperatureUnit`:

Chain rule for division: `(x / y) * (y / z) = x / z` when coerced
to `ℝ`.
-/
@[simp]
lemma div_mul_div_coe (x y z : TemperatureUnit) :
    (x / y : ℝ) * (y / z : ℝ) = x / z := by
  -- We simplify using the definition of division.
  simp [div_eq_val]
  -- We apply `field_simp` to clear denominators and
  -- conclude by algebraic simplification. QED.
  field_simp

/-!
## The scaling of a temperature unit
-/

/-- Function for `TemperatureUnit`:

Scale a temperature unit by a positive real number.
-/
def scale (r : ℝ) (x : TemperatureUnit)
    (hr : 0 < r := by norm_num) : TemperatureUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

/-- Simplification lemma for `TemperatureUnit`:

Scaling a unit and dividing by the original yields the scale factor.
-/
@[simp]
lemma scale_div_self (x : TemperatureUnit) (r : ℝ)
    (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  -- We simplify using the definitions of `scale` and
  -- `div_eq_val`. QED.
  simp [scale, div_eq_val]

/-- Simplification lemma for `TemperatureUnit`:

Dividing a unit by its scaled version yields the reciprocal of the
scale factor.
-/
@[simp]
lemma self_div_scale (x : TemperatureUnit) (r : ℝ)
    (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r,
        _root_.div_nonneg (by simp)
          (le_of_lt hr)⟩ : ℝ≥0) := by
  -- We simplify using the definitions of `scale` and
  -- `div_eq_val`.
  simp [scale, div_eq_val]
  -- We apply extensionality to reduce the goal to
  -- equality of underlying values.
  ext
  -- We simplify the coercion from `ℝ≥0` to `ℝ`.
  simp only [coe_mk]
  -- We apply `field_simp` to clear denominators and
  -- conclude by algebraic simplification. QED.
  field_simp

/-- Simplification lemma for `TemperatureUnit`:

Scaling by `1` is the identity.
-/
@[simp]
lemma scale_one (x : TemperatureUnit) :
    scale 1 x = x := by
  -- We simplify using the definition of `scale`, since
  -- `1 * x.val = x.val`. QED.
  simp [scale]

/-- Simplification lemma for `TemperatureUnit`:

The ratio of two scaled units factors into the product of scale
ratios and unit ratios.
-/
@[simp]
lemma scale_div_scale (x1 x2 : TemperatureUnit)
    {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) *
        (x1 / x2) := by
  -- We refine the goal using `NNReal.eq`, which reduces
  -- equality of `ℝ≥0` values to equality of their
  -- underlying `ℝ` values.
  refine NNReal.eq ?_
  -- We simplify using the definitions of `scale` and
  -- `div_eq_val`.
  simp [scale, div_eq_val]
  -- We apply `field_simp` to clear denominators and
  -- conclude by algebraic simplification. QED.
  field_simp

/-- Simplification lemma for `TemperatureUnit`:

Double scaling is equivalent to scaling by the product.
-/
@[simp]
lemma scale_scale (x : TemperatureUnit) (r1 r2 : ℝ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  -- We simplify using the definition of `scale`.
  simp [scale]
  -- We conclude by the algebraic identity
  -- `r1 * (r2 * x.val) = (r1 * r2) * x.val`. QED.
  ring

/-!
## Specific choices of temperature units

To define specific temperature units, we first define the notion of
a kelvin to correspond to the temperature unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism
between the set of metrics on the temperature manifold and the
positive reals.

Once we have defined kelvin, we can define other temperature units
by scaling kelvin.
-/

/-- Function for `TemperatureUnit`:

The definition of a temperature unit of kelvin.
-/
def kelvin : TemperatureUnit := ⟨1, by norm_num⟩

/-- Function for `TemperatureUnit`:

The temperature unit of degrees nanokelvin (`10^(-9) kelvin`).
-/
noncomputable def nanokelvin : TemperatureUnit :=
  scale (1e-9) kelvin

/-- Function for `TemperatureUnit`:

The temperature unit of degrees microkelvin (`10^(-6) kelvin`).
-/
noncomputable def microkelvin : TemperatureUnit :=
  scale (1e-6) kelvin

/-- Function for `TemperatureUnit`:

The temperature unit of degrees millikelvin (`10^(-3) kelvin`).
-/
noncomputable def millikelvin : TemperatureUnit :=
  scale (1e-3) kelvin

/-- Function for `TemperatureUnit`:

The temperature unit of degrees rankine (`(5/9)` of a kelvin).
-/
noncomputable def rankine : TemperatureUnit :=
  scale (5 / 9) kelvin

end TemperatureUnit

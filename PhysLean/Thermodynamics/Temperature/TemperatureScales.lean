/-
Copyright (c) 2026 Trong-Nghia Be. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Tan-Phuoc-Hung Le
-/
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
/-!
# Affine temperature scales === TODO TIL THE END OF THE FILE

`Temperature` stores absolute temperature in kelvin (`ℝ≥0`), which
is the physically meaningful quantity used by thermodynamics and
statistical mechanics.

This file introduces affine display scales (such as Celsius and
Fahrenheit), where the reading is allowed to be negative while the
corresponding absolute temperature remains nonnegative.
-/

open NNReal

/-- The type `TemperatureScale` represents an affine temperature
  scale, such as Celsius or Fahrenheit.
  - `unit` of type `TemperatureUnit`: The size of one degree on
    this scale as a multiplicative temperature interval.
  - `absoluteZero` of type `ℝ`: The reading on this scale
    corresponding to `0 K`. For example, on the Celsius scale this
    is `-273.15`.
-/
structure TemperatureScale where
  /-- The multiplicative interval unit for one degree on this
  scale. -/
  unit : TemperatureUnit
  /-- The reading corresponding to absolute zero (`0 K`). -/
  absoluteZero : ℝ

namespace TemperatureScale

/-- Function for `TemperatureScale`:

Convert a reading in an affine temperature scale into kelvin as a
real number.
-/
noncomputable def toKelvinReal
    (s : TemperatureScale) (reading : ℝ) : ℝ :=
  (reading - s.absoluteZero) *
    (s.unit / TemperatureUnit.kelvin : ℝ)

/-- Function for `TemperatureScale`:

Convert a kelvin value into a reading in an affine temperature scale
as a real number.
-/
noncomputable def fromKelvinReal
    (s : TemperatureScale) (k : ℝ) : ℝ :=
  s.absoluteZero +
    k * (TemperatureUnit.kelvin / s.unit : ℝ)

/-- Lemma for `TemperatureScale`:

Converting to kelvin and back to the affine scale is the identity.
-/
lemma fromKelvinReal_toKelvinReal
    (s : TemperatureScale) (reading : ℝ) :
    fromKelvinReal s (toKelvinReal s reading) =
      reading := by
  -- We unfold the definitions of `fromKelvinReal` and
  -- `toKelvinReal` to expose the underlying expressions.
  unfold fromKelvinReal toKelvinReal
  -- We derive `hmul` which states that the product of the
  -- unit ratio and its inverse equals `1`, using the chain
  -- rule for division `div_mul_div_coe`.
  have hmul :
      (s.unit / TemperatureUnit.kelvin : ℝ) *
        (TemperatureUnit.kelvin / s.unit : ℝ) = 1 := by
    calc
      (s.unit / TemperatureUnit.kelvin : ℝ) *
          (TemperatureUnit.kelvin / s.unit : ℝ)
          = (s.unit / s.unit : ℝ) :=
            TemperatureUnit.div_mul_div_coe
              s.unit TemperatureUnit.kelvin s.unit
      _ = 1 := by simp
  -- We conclude by algebraic simplification using `hmul`
  -- to replace the product of ratios with `1`. QED.
  calc
    s.absoluteZero +
        ((reading - s.absoluteZero) *
          (s.unit / TemperatureUnit.kelvin : ℝ)) *
            (TemperatureUnit.kelvin / s.unit : ℝ)
        = s.absoluteZero +
          (reading - s.absoluteZero) *
            ((s.unit / TemperatureUnit.kelvin : ℝ) *
              (TemperatureUnit.kelvin / s.unit : ℝ)) :=
                by ring
    _ = s.absoluteZero +
          (reading - s.absoluteZero) * 1 := by
            rw [hmul]
    _ = reading := by ring

/-- Lemma for `TemperatureScale`:

Converting from kelvin to the affine scale and back to kelvin is the
identity.
-/
lemma toKelvinReal_fromKelvinReal
    (s : TemperatureScale) (k : ℝ) :
    toKelvinReal s (fromKelvinReal s k) = k := by
  -- We unfold the definitions of `fromKelvinReal` and
  -- `toKelvinReal` to expose the underlying expressions.
  unfold fromKelvinReal toKelvinReal
  -- We derive `hmul` which states that the product of the
  -- unit ratio and its inverse equals `1`, using the chain
  -- rule for division `div_mul_div_coe`.
  have hmul :
      (TemperatureUnit.kelvin / s.unit : ℝ) *
        (s.unit / TemperatureUnit.kelvin : ℝ) = 1 := by
    calc
      (TemperatureUnit.kelvin / s.unit : ℝ) *
          (s.unit / TemperatureUnit.kelvin : ℝ)
          = (TemperatureUnit.kelvin /
              TemperatureUnit.kelvin : ℝ) :=
            TemperatureUnit.div_mul_div_coe
              TemperatureUnit.kelvin s.unit
              TemperatureUnit.kelvin
      _ = 1 := by simp
  -- We conclude by algebraic simplification using `hmul`
  -- to replace the product of ratios with `1`. QED.
  calc
    (s.absoluteZero +
        k * (TemperatureUnit.kelvin / s.unit : ℝ) -
          s.absoluteZero) *
        (s.unit / TemperatureUnit.kelvin : ℝ)
        = (k *
            (TemperatureUnit.kelvin / s.unit : ℝ)) *
          (s.unit / TemperatureUnit.kelvin : ℝ) :=
            by ring
    _ = k *
          ((TemperatureUnit.kelvin / s.unit : ℝ) *
            (s.unit / TemperatureUnit.kelvin : ℝ)) :=
              by ring
    _ = k * 1 := by rw [hmul]
    _ = k := by ring

/-- Function for `TemperatureScale`:

The kelvin scale, with unit size equal to one kelvin and zero
offset.
-/
def kelvin : TemperatureScale :=
  ⟨TemperatureUnit.kelvin, 0⟩

/-- Function for `TemperatureScale`:

The Celsius scale, with unit size equal to one kelvin and absolute
zero at `-273.15`.
-/
noncomputable def celsius : TemperatureScale :=
  ⟨TemperatureUnit.kelvin, -(27315 : ℝ) / 100⟩

/-- Function for `TemperatureScale`:

The Rankine scale, with unit size equal to one rankine degree and
zero offset.
-/
noncomputable def rankine : TemperatureScale :=
  ⟨TemperatureUnit.rankine, 0⟩

/-- Function for `TemperatureScale`:

The Fahrenheit scale, with unit size equal to one rankine degree and
absolute zero at `-459.67`.
-/
noncomputable def fahrenheit : TemperatureScale :=
  ⟨TemperatureUnit.rankine, -(45967 : ℝ) / 100⟩

/-- Simplification lemma for `TemperatureScale`:

Converting a kelvin reading to kelvin is the identity.
-/
@[simp]
lemma toKelvinReal_kelvin (k : ℝ) :
    toKelvinReal kelvin k = k := by
  -- We simplify using the definitions of `toKelvinReal`
  -- and `kelvin`. QED.
  simp [toKelvinReal, kelvin]

/-- Simplification lemma for `TemperatureScale`:

Converting a kelvin value to a kelvin reading is the identity.
-/
@[simp]
lemma fromKelvinReal_kelvin (k : ℝ) :
    fromKelvinReal kelvin k = k := by
  -- We simplify using the definitions of `fromKelvinReal`
  -- and `kelvin`. QED.
  simp [fromKelvinReal, kelvin]

/-- Simplification lemma for `TemperatureScale`:

Converting a Celsius reading `c` to kelvin yields
`c + 273.15`.
-/
@[simp]
lemma toKelvinReal_celsius (c : ℝ) :
    toKelvinReal celsius c =
      c + (27315 : ℝ) / 100 := by
  -- We compute `toKelvinReal celsius c` step by step.
  calc
    toKelvinReal celsius c
        = (c - (-(27315 : ℝ) / 100)) *
            (TemperatureUnit.kelvin /
              TemperatureUnit.kelvin : ℝ) := by
              rfl
    -- We simplify `kelvin / kelvin` to `1` and the
    -- subtraction of a negative to addition.
    _ = c - (-(27315 : ℝ) / 100) := by simp
    -- We conclude by the algebraic identity
    -- `c - (-273.15) = c + 273.15`. QED.
    _ = c + (27315 : ℝ) / 100 := by ring

/-- Simplification lemma for `TemperatureScale`:

Converting a kelvin value to Celsius yields
`-273.15 + k`.
-/
@[simp]
lemma fromKelvinReal_celsius (k : ℝ) :
    fromKelvinReal celsius k =
      -(27315 : ℝ) / 100 + k := by
  -- We simplify using the definitions of `fromKelvinReal`,
  -- `celsius`, and commutativity of addition. QED.
  simp [fromKelvinReal, celsius, add_comm]

/-- Simplification lemma for `TemperatureScale`:

Converting a Fahrenheit reading `f` to kelvin yields
`(f + 459.67) * (5 / 9)`.
-/
@[simp]
lemma toKelvinReal_fahrenheit (f : ℝ) :
    toKelvinReal fahrenheit f =
      (f + (45967 : ℝ) / 100) * (5 / 9 : ℝ) := by
  -- We compute `toKelvinReal fahrenheit f` step by step.
  calc
    toKelvinReal fahrenheit f
        = (f - (-(45967 : ℝ) / 100)) *
            (TemperatureUnit.rankine /
              TemperatureUnit.kelvin : ℝ) := by
              rfl
    -- We simplify the subtraction of a negative to
    -- addition and evaluate `rankine / kelvin = 5/9`.
    _ = (f + (45967 : ℝ) / 100) *
          (5 / 9 : ℝ) := by
      -- We derive that `f - (-459.67) = f + 459.67`.
      have hneg :
          f - (-(45967 : ℝ) / 100) =
            f + (45967 : ℝ) / 100 := by ring
      -- We rewrite using `hneg` and simplify the rankine
      -- to kelvin ratio. QED.
      rw [hneg]
      simp [TemperatureUnit.rankine,
        TemperatureUnit.scale_div_self]

/-- Simplification lemma for `TemperatureScale`:

Converting a kelvin value to Fahrenheit yields
`-459.67 + k * (9 / 5)`.
-/
@[simp]
lemma fromKelvinReal_fahrenheit (k : ℝ) :
    fromKelvinReal fahrenheit k =
      -(45967 : ℝ) / 100 + k * (9 / 5 : ℝ) := by
  -- We simplify using the definitions of `fromKelvinReal`,
  -- `fahrenheit`, `rankine`, `self_div_scale`, and
  -- commutativity of addition. QED.
  simp [fromKelvinReal, fahrenheit,
    TemperatureUnit.rankine,
    TemperatureUnit.self_div_scale, add_comm]

/-- Lemma for `TemperatureScale`:

The kelvin value of a Celsius reading is nonnegative if and only if
the reading is at or above `-273.15`.
-/
lemma zero_le_toKelvinReal_celsius_iff (c : ℝ) :
    0 ≤ toKelvinReal celsius c ↔
      (-(27315 : ℝ) / 100) ≤ c := by
  -- We rewrite the goal using `toKelvinReal_celsius` to
  -- get the explicit formula.
  rw [toKelvinReal_celsius]
  -- We prove both directions using `linarith`. QED.
  constructor <;> intro h <;> linarith

/-- Lemma for `TemperatureScale`:

The kelvin value of a Fahrenheit reading is nonnegative if and only
if the reading is at or above `-459.67`.
-/
lemma zero_le_toKelvinReal_fahrenheit_iff (f : ℝ) :
    0 ≤ toKelvinReal fahrenheit f ↔
      (-(45967 : ℝ) / 100) ≤ f := by
  -- We rewrite the goal using `toKelvinReal_fahrenheit`
  -- to get the explicit formula.
  rw [toKelvinReal_fahrenheit]
  -- We prove the forward direction.
  constructor
  · intro h
    -- We derive `h'` stating that `f + 459.67 ≥ 0`
    -- from the product being nonnegative with the
    -- positive factor `5/9`.
    have h' : 0 ≤ f + (45967 : ℝ) / 100 :=
      (mul_nonneg_iff_of_pos_right
        (show (0 : ℝ) < 5 / 9 by norm_num)).1 h
    -- We conclude by linear arithmetic. QED for this
    -- case.
    linarith
  -- We prove the reverse direction.
  · intro h
    -- We derive `h'` stating that `f + 459.67 ≥ 0`
    -- from the hypothesis.
    have h' : 0 ≤ f + (45967 : ℝ) / 100 := by
      linarith
    -- We conclude by `mul_nonneg` since both factors
    -- are nonnegative. QED for this case.
    -- All cases have been proven. QED.
    exact mul_nonneg h' (by norm_num)

end TemperatureScale

namespace Temperature

/-- Function for `Temperature`:

Convert an absolute temperature to a reading in an affine scale.
-/
noncomputable def toScale
    (T : Temperature) (s : TemperatureScale) : ℝ :=
  TemperatureScale.fromKelvinReal s (T : ℝ)

/-- Function for `Temperature`:

Build an absolute temperature from an affine scale reading and a
proof it is physically valid.
-/
noncomputable def ofScale (s : TemperatureScale)
    (x : ℝ)
    (hx : 0 ≤ TemperatureScale.toKelvinReal s x) :
    Temperature :=
  Temperature.ofRealNonneg
    (TemperatureScale.toKelvinReal s x) hx

/-- Function for `Temperature`:

Build an absolute temperature from an affine scale reading,
returning `none` below absolute zero.
-/
noncomputable def ofScale?
    (s : TemperatureScale) (x : ℝ) :
    Option Temperature :=
  if hx : 0 ≤ TemperatureScale.toKelvinReal s x then
    some (ofScale s x hx)
  else none

/-- Function for `Temperature`:

Convert an absolute temperature to Celsius.
-/
noncomputable def toCelsius (T : Temperature) : ℝ :=
  toScale T TemperatureScale.celsius

/-- Function for `Temperature`:

Convert an absolute temperature to Fahrenheit.
-/
noncomputable def toFahrenheit
    (T : Temperature) : ℝ :=
  toScale T TemperatureScale.fahrenheit

/-- Function for `Temperature`:

Build an absolute temperature from Celsius.
-/
noncomputable def ofCelsius (c : ℝ)
    (hc : (-(27315 : ℝ) / 100) ≤ c) : Temperature :=
  ofScale TemperatureScale.celsius c
    ((TemperatureScale.zero_le_toKelvinReal_celsius_iff
        c).2 hc)

/-- Function for `Temperature`:

Build an absolute temperature from Fahrenheit.
-/
noncomputable def ofFahrenheit (f : ℝ)
    (hf : (-(45967 : ℝ) / 100) ≤ f) : Temperature :=
  ofScale TemperatureScale.fahrenheit f
    ((TemperatureScale.zero_le_toKelvinReal_fahrenheit_iff
        f).2 hf)

/-- Function for `Temperature`:

Build an absolute temperature from Celsius, returning `none` below
absolute zero.
-/
noncomputable def ofCelsius? (c : ℝ) :
    Option Temperature :=
  ofScale? TemperatureScale.celsius c

/-- Function for `Temperature`:

Build an absolute temperature from Fahrenheit, returning `none`
below absolute zero.
-/
noncomputable def ofFahrenheit? (f : ℝ) :
    Option Temperature :=
  ofScale? TemperatureScale.fahrenheit f

/-- Lemma for `Temperature`:

Converting to a scale and back recovers the original reading.
-/
lemma toScale_ofScale (s : TemperatureScale) (x : ℝ)
    (hx : 0 ≤ TemperatureScale.toKelvinReal s x) :
    toScale (ofScale s x hx) s = x := by
  -- We simplify using the definitions of `toScale`,
  -- `ofScale`, `ofRealNonneg`, `ofNNReal`, `toReal`,
  -- and the round-trip lemma
  -- `fromKelvinReal_toKelvinReal`. QED.
  simp [toScale, ofScale, Temperature.ofRealNonneg,
    Temperature.ofNNReal, Temperature.toReal,
    TemperatureScale.fromKelvinReal_toKelvinReal]

/-- Simplification lemma for `Temperature`:

Absolute zero in Celsius is `-273.15`.
-/
@[simp]
lemma toCelsius_zero :
    toCelsius (0 : Temperature) =
      (-(27315 : ℝ) / 100) := by
  -- We change the goal to unfold `toCelsius` and
  -- `toScale` into `fromKelvinReal` applied to `0`.
  change TemperatureScale.fromKelvinReal
    TemperatureScale.celsius
    (((0 : Temperature).val : ℝ)) =
      (-(27315 : ℝ) / 100)
  -- We derive that the real value of zero temperature
  -- is `0`.
  have hzero : (((0 : Temperature).val : ℝ)) = 0 :=
    by rfl
  -- We simplify using `hzero` and the definitions of
  -- `fromKelvinReal` and `celsius`. QED.
  simp [hzero, TemperatureScale.fromKelvinReal,
    TemperatureScale.celsius]

/-- Simplification lemma for `Temperature`:

Absolute zero in Fahrenheit is `-459.67`.
-/
@[simp]
lemma toFahrenheit_zero :
    toFahrenheit (0 : Temperature) =
      (-(45967 : ℝ) / 100) := by
  -- We change the goal to unfold `toFahrenheit` and
  -- `toScale` into `fromKelvinReal` applied to `0`.
  change TemperatureScale.fromKelvinReal
    TemperatureScale.fahrenheit
    (((0 : Temperature).val : ℝ)) =
      (-(45967 : ℝ) / 100)
  -- We derive that the real value of zero temperature
  -- is `0`.
  have hzero : (((0 : Temperature).val : ℝ)) = 0 :=
    by rfl
  -- We simplify using `hzero` and the definitions of
  -- `fromKelvinReal` and `fahrenheit`. QED.
  simp [hzero, TemperatureScale.fromKelvinReal,
    TemperatureScale.fahrenheit]

/-- Simplification lemma for `Temperature`:

`ofCelsius?` returns `none` below absolute zero.
-/
@[simp]
lemma ofCelsius?_below_absoluteZero :
    ofCelsius? ((-(27315 : ℝ) / 100) - 1) =
      none := by
  -- We simplify using the definitions of `ofCelsius?`
  -- and `ofScale?`.
  simp [ofCelsius?, ofScale?]
  -- We conclude by linear arithmetic, since the kelvin
  -- value is negative below absolute zero. QED.
  linarith

/-- Simplification lemma for `Temperature`:

`ofFahrenheit?` returns `none` below absolute zero.
-/
@[simp]
lemma ofFahrenheit?_below_absoluteZero :
    ofFahrenheit? ((-(45967 : ℝ) / 100) - 1) =
      none := by
  -- We simplify using the definitions of `ofFahrenheit?`
  -- and `ofScale?`.
  simp [ofFahrenheit?, ofScale?]
  -- We conclude by linear arithmetic, since the kelvin
  -- value is negative below absolute zero. QED.
  linarith

/-- Lemma for `Temperature`:

`-40` degrees Celsius equals `-40` degrees Fahrenheit.
-/
lemma minusForty_celsius_eq_minusForty_fahrenheit :
    toFahrenheit (ofCelsius (-40) (by norm_num)) =
      (-40 : ℝ) := by
  -- We simplify using the definitions of `toFahrenheit`,
  -- `toScale`, `ofCelsius`, and `ofScale`.
  simp [toFahrenheit, toScale, ofCelsius, ofScale]
  -- We conclude by numerical computation. QED.
  norm_num

end Temperature

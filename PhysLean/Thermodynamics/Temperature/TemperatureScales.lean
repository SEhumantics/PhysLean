/-
Copyright (c) 2026 Trong-Nghia Be. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Tan-Phuoc-Hung Le
-/
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
/-!

# Affine temperature scales === TODO TIL THE END OF THE FILE

`Temperature` stores absolute temperature in kelvin (`ℝ≥0`), which is the physically meaningful quantity used by thermodynamics and statistical mechanics.

This file introduces affine display scales (such as Celsius and Fahrenheit), where the reading is allowed to be negative while the corresponding absolute temperature remains nonnegative.

-/

open NNReal

/-- An affine scale for reading temperatures.

- `unit` gives the size of one degree on this scale as a multiplicative temperature interval.
- `absoluteZero` is the reading on this scale corresponding to `0 K`.
   For example, on the Celsius scale this is `-273.15`.
-/
structure TemperatureScale where
  /-- The multiplicative interval unit for one degree on this scale. -/
  unit : TemperatureUnit
  /-- The reading corresponding to absolute zero (`0 K`). -/
  absoluteZero : ℝ

namespace TemperatureScale

/-- Convert a reading in an affine temperature scale into kelvin as a real number.

- Input:
  - `s` of type `TemperatureScale`: the affine temperature scale.
  - `reading` of type `ℝ`: the reading on the affine scale.
- Output:
  - result of type `ℝ`: the corresponding temperature in kelvin as a real number.

- Algorithm:
  1. Subtract `s.absoluteZero` from `reading` to get the temperature interval above absolute zero.
  2. Multiply the result by the ratio of `s.unit` to `TemperatureUnit.kelvin` to convert the interval to kelvin.
-/
noncomputable def toKelvinReal (s : TemperatureScale) (reading : ℝ) : ℝ :=
  (reading - s.absoluteZero) * (s.unit / TemperatureUnit.kelvin : ℝ)

/-- Convert a kelvin value into a reading in an affine temperature scale as a real number. -/
noncomputable def fromKelvinReal (s : TemperatureScale) (k : ℝ) : ℝ :=
  s.absoluteZero + k * (TemperatureUnit.kelvin / s.unit : ℝ)

lemma fromKelvinReal_toKelvinReal (s : TemperatureScale) (reading : ℝ) :
    fromKelvinReal s (toKelvinReal s reading) = reading := by
  unfold fromKelvinReal toKelvinReal
  have hmul : (s.unit / TemperatureUnit.kelvin : ℝ) *
      (TemperatureUnit.kelvin / s.unit : ℝ) = 1 := by
    calc
      (s.unit / TemperatureUnit.kelvin : ℝ) * (TemperatureUnit.kelvin / s.unit : ℝ)
          = (s.unit / s.unit : ℝ) :=
            TemperatureUnit.div_mul_div_coe s.unit TemperatureUnit.kelvin s.unit
      _ = 1 := by simp
  calc
    s.absoluteZero +
        ((reading - s.absoluteZero) * (s.unit / TemperatureUnit.kelvin : ℝ)) *
          (TemperatureUnit.kelvin / s.unit : ℝ)
        = s.absoluteZero +
          (reading - s.absoluteZero) *
            ((s.unit / TemperatureUnit.kelvin : ℝ) *
              (TemperatureUnit.kelvin / s.unit : ℝ)) := by ring
    _ = s.absoluteZero + (reading - s.absoluteZero) * 1 := by rw [hmul]
    _ = reading := by ring

lemma toKelvinReal_fromKelvinReal (s : TemperatureScale) (k : ℝ) :
    toKelvinReal s (fromKelvinReal s k) = k := by
  unfold fromKelvinReal toKelvinReal
  have hmul : (TemperatureUnit.kelvin / s.unit : ℝ) *
      (s.unit / TemperatureUnit.kelvin : ℝ) = 1 := by
    calc
      (TemperatureUnit.kelvin / s.unit : ℝ) * (s.unit / TemperatureUnit.kelvin : ℝ)
          = (TemperatureUnit.kelvin / TemperatureUnit.kelvin : ℝ) :=
            TemperatureUnit.div_mul_div_coe TemperatureUnit.kelvin s.unit TemperatureUnit.kelvin
      _ = 1 := by simp
  calc
    (s.absoluteZero + k * (TemperatureUnit.kelvin / s.unit : ℝ) - s.absoluteZero) *
        (s.unit / TemperatureUnit.kelvin : ℝ)
        = (k * (TemperatureUnit.kelvin / s.unit : ℝ)) *
          (s.unit / TemperatureUnit.kelvin : ℝ) := by ring
    _ = k * ((TemperatureUnit.kelvin / s.unit : ℝ) *
          (s.unit / TemperatureUnit.kelvin : ℝ)) := by ring
    _ = k * 1 := by rw [hmul]
    _ = k := by ring

/-- Kelvin scale. -/
def kelvin : TemperatureScale := ⟨TemperatureUnit.kelvin, 0⟩

/-- Celsius scale. -/
noncomputable def celsius : TemperatureScale := ⟨TemperatureUnit.kelvin, -(27315 : ℝ) / 100⟩

/-- Rankine scale. -/
noncomputable def rankine : TemperatureScale := ⟨TemperatureUnit.rankine, 0⟩

/-- Fahrenheit scale. -/
noncomputable def fahrenheit : TemperatureScale := ⟨TemperatureUnit.rankine, -(45967 : ℝ) / 100⟩

@[simp]
lemma toKelvinReal_kelvin (k : ℝ) : toKelvinReal kelvin k = k := by
  simp [toKelvinReal, kelvin]

@[simp]
lemma fromKelvinReal_kelvin (k : ℝ) : fromKelvinReal kelvin k = k := by
  simp [fromKelvinReal, kelvin]

@[simp]
lemma toKelvinReal_celsius (c : ℝ) :
    toKelvinReal celsius c = c + (27315 : ℝ) / 100 := by
  calc
    toKelvinReal celsius c
        = (c - (-(27315 : ℝ) / 100)) * (TemperatureUnit.kelvin / TemperatureUnit.kelvin : ℝ) := by
            rfl
    _ = c - (-(27315 : ℝ) / 100) := by simp
    _ = c + (27315 : ℝ) / 100 := by ring

@[simp]
lemma fromKelvinReal_celsius (k : ℝ) :
    fromKelvinReal celsius k = -(27315 : ℝ) / 100 + k := by
  simp [fromKelvinReal, celsius, add_comm]

@[simp]
lemma toKelvinReal_fahrenheit (f : ℝ) :
    toKelvinReal fahrenheit f = (f + (45967 : ℝ) / 100) * (5 / 9 : ℝ) := by
  calc
    toKelvinReal fahrenheit f
        = (f - (-(45967 : ℝ) / 100)) * (TemperatureUnit.rankine / TemperatureUnit.kelvin : ℝ) := by
            rfl
    _ = (f + (45967 : ℝ) / 100) * (5 / 9 : ℝ) := by
      have hneg : f - (-(45967 : ℝ) / 100) = f + (45967 : ℝ) / 100 := by ring
      rw [hneg]
      simp [TemperatureUnit.rankine, TemperatureUnit.scale_div_self]

@[simp]
lemma fromKelvinReal_fahrenheit (k : ℝ) :
    fromKelvinReal fahrenheit k = -(45967 : ℝ) / 100 + k * (9 / 5 : ℝ) := by
  simp [fromKelvinReal, fahrenheit, TemperatureUnit.rankine, TemperatureUnit.self_div_scale,
    add_comm]

lemma zero_le_toKelvinReal_celsius_iff (c : ℝ) :
    0 ≤ toKelvinReal celsius c ↔ (-(27315 : ℝ) / 100) ≤ c := by
  rw [toKelvinReal_celsius]
  constructor <;> intro h <;> linarith

lemma zero_le_toKelvinReal_fahrenheit_iff (f : ℝ) :
    0 ≤ toKelvinReal fahrenheit f ↔ (-(45967 : ℝ) / 100) ≤ f := by
  rw [toKelvinReal_fahrenheit]
  constructor
  · intro h
    have h' : 0 ≤ f + (45967 : ℝ) / 100 :=
      (mul_nonneg_iff_of_pos_right (show (0 : ℝ) < 5 / 9 by norm_num)).1 h
    linarith
  · intro h
    have h' : 0 ≤ f + (45967 : ℝ) / 100 := by linarith
    exact mul_nonneg h' (by norm_num)

end TemperatureScale

namespace Temperature

/-- Convert an absolute temperature to a reading in an affine scale. -/
noncomputable def toScale (T : Temperature) (s : TemperatureScale) : ℝ :=
  TemperatureScale.fromKelvinReal s (T : ℝ)

/-- Build an absolute temperature from an affine scale reading and a proof it is physically valid. -/
noncomputable def ofScale (s : TemperatureScale) (x : ℝ)
    (hx : 0 ≤ TemperatureScale.toKelvinReal s x) : Temperature :=
  Temperature.ofRealNonneg (TemperatureScale.toKelvinReal s x) hx

/-- Build an absolute temperature from an affine scale reading, failing below absolute zero. -/
noncomputable def ofScale? (s : TemperatureScale) (x : ℝ) : Option Temperature :=
  if hx : 0 ≤ TemperatureScale.toKelvinReal s x then some (ofScale s x hx) else none

/-- Convert an absolute temperature to Celsius. -/
noncomputable def toCelsius (T : Temperature) : ℝ :=
  toScale T TemperatureScale.celsius

/-- Convert an absolute temperature to Fahrenheit. -/
noncomputable def toFahrenheit (T : Temperature) : ℝ :=
  toScale T TemperatureScale.fahrenheit

/-- Build an absolute temperature from Celsius. -/
noncomputable def ofCelsius (c : ℝ) (hc : (-(27315 : ℝ) / 100) ≤ c) : Temperature :=
  ofScale TemperatureScale.celsius c ((TemperatureScale.zero_le_toKelvinReal_celsius_iff c).2 hc)

/-- Build an absolute temperature from Fahrenheit. -/
noncomputable def ofFahrenheit (f : ℝ) (hf : (-(45967 : ℝ) / 100) ≤ f) : Temperature :=
  ofScale TemperatureScale.fahrenheit f
    ((TemperatureScale.zero_le_toKelvinReal_fahrenheit_iff f).2 hf)

/-- Build an absolute temperature from Celsius, returning `none` below absolute zero. -/
noncomputable def ofCelsius? (c : ℝ) : Option Temperature :=
  ofScale? TemperatureScale.celsius c

/-- Build an absolute temperature from Fahrenheit, returning `none` below absolute zero. -/
noncomputable def ofFahrenheit? (f : ℝ) : Option Temperature :=
  ofScale? TemperatureScale.fahrenheit f

lemma toScale_ofScale (s : TemperatureScale) (x : ℝ)
    (hx : 0 ≤ TemperatureScale.toKelvinReal s x) :
    toScale (ofScale s x hx) s = x := by
  simp [toScale, ofScale, Temperature.ofRealNonneg, Temperature.ofNNReal,
    Temperature.toReal, TemperatureScale.fromKelvinReal_toKelvinReal]

@[simp]
lemma toCelsius_zero : toCelsius (0 : Temperature) = (-(27315 : ℝ) / 100) := by
  change TemperatureScale.fromKelvinReal TemperatureScale.celsius (((0 : Temperature).val : ℝ)) =
    (-(27315 : ℝ) / 100)
  have hzero : (((0 : Temperature).val : ℝ)) = 0 := by rfl
  simp [hzero, TemperatureScale.fromKelvinReal, TemperatureScale.celsius]

@[simp]
lemma toFahrenheit_zero : toFahrenheit (0 : Temperature) = (-(45967 : ℝ) / 100) := by
  change TemperatureScale.fromKelvinReal TemperatureScale.fahrenheit (((0 : Temperature).val : ℝ)) =
    (-(45967 : ℝ) / 100)
  have hzero : (((0 : Temperature).val : ℝ)) = 0 := by rfl
  simp [hzero, TemperatureScale.fromKelvinReal, TemperatureScale.fahrenheit]

@[simp]
lemma ofCelsius?_below_absoluteZero : ofCelsius? ((-(27315 : ℝ) / 100) - 1) = none := by
  simp [ofCelsius?, ofScale?]
  linarith

@[simp]
lemma ofFahrenheit?_below_absoluteZero : ofFahrenheit? ((-(45967 : ℝ) / 100) - 1) = none := by
  simp [ofFahrenheit?, ofScale?]
  linarith

lemma minusForty_celsius_eq_minusForty_fahrenheit :
    toFahrenheit (ofCelsius (-40) (by norm_num)) = (-40 : ℝ) := by
  simp [toFahrenheit, toScale, ofCelsius, ofScale]
  norm_num

end Temperature

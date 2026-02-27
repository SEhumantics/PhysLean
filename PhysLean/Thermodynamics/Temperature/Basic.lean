/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.Types.PosReal

/-!
# Temperature

In this module we define the types `Temperature` and `PositiveTemperature` to represent
absolute thermodynamic temperature in kelvin.
This is the version of temperature most often used in undergraduate and non-mathematical physics.

We also define the inverse temperature `β` (thermodynamic beta/coldness)
and its inverse function `ofβ`, which are commonly used in statistical mechanics and thermodynamics.

For affine display scales with offsets (such as Celsius and Fahrenheit), see
`PhysLean.Thermodynamics.Temperature.TemperatureScales`.

For regularity properties of `ofβ`, see
`PhysLean.Thermodynamics.Temperature.Regularity`.

For convergence results, see
`PhysLean.Thermodynamics.Temperature.Convergence`.

For calculus relating T and β, see
`PhysLean.Thermodynamics.Temperature.Calculus`.
-/
open NNReal

/-- The type `Temperature` represents absolute thermodynamic temperature in kelvin.
-/
structure Temperature where
  /-- The nonnegative real value of the temperature. -/
  val : ℝ≥0

/-- The type `PositiveTemperature` represents strictly positive absolute thermodynamic temperature
in kelvin.

It is defined as a subtype of `Temperature` where the `val` field is strictly positive.
-/
def PositiveTemperature := { T : Temperature // 0 < T.val }

/-!
## Basic instances and definitions for `Temperature`
-/
namespace Temperature
open Constants

/-- Type coercion (implicit casting) from `Temperature` to `ℝ≥0`.

Defined as a function that takes a `Temperature` and returns its underlying `ℝ≥0` value (by
accessing the `val` field).
-/
instance : Coe Temperature ℝ≥0 := ⟨fun (T : Temperature) => T.val⟩

/-- Function for `Temperature`:

Convert a `Temperature` to a real number in `ℝ`.
-/
def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Type coercion (implicit casting) from `Temperature` to `ℝ`.

Defined as a function that takes a `Temperature` and returns the `val` field converted to `ℝ`.
-/
instance : Coe Temperature ℝ := ⟨fun (T : Temperature) => Temperature.toReal T⟩

/-- Topology on `Temperature` induced from `ℝ≥0`.

Defined using the `induced` topology from the coercion function that maps a `Temperature` to its
real number representation in `ℝ≥0`.
-/
instance : TopologicalSpace Temperature := TopologicalSpace.induced
  (fun (T : Temperature) => (T : ℝ≥0)) inferInstance

/-- The zero temperature (absolute zero) in kelvin. -/
instance : Zero Temperature := ⟨⟨0⟩⟩

/-- Extensionality lemma for `Temperature`.

Two `Temperature` instances are equal if their underlying `val` fields are equal.
-/
@[ext]
lemma ext {T₁ T₂ : Temperature} (h_eq : T₁.val = T₂.val) : T₁ = T₂ := by
  -- Substitutes `T₁` with its constructor form.
  -- We have `T₁ = ⟨val := T₁val⟩` in `h_eq` and the goal.
  cases T₁ with
  | mk T₁val
  -- Substitutes `T₂` with its constructor form.
  -- We have `T₂ = ⟨val := T₂val⟩` in `h_eq` and the goal.
  cases T₂ with
  | mk T₂val
  -- The proof currently has `h_eq: { val := T₁val }.val = { val := T₂val }.val`
  -- and `⊢ ⟨val := T₁val⟩.val = ⟨val := T₂val⟩.val`.
  -- Substitutes `h_eq` into the goal, replacing `T₂.val` with `T₁.val`.
  -- We now have `⊢ ⟨val := T₁val⟩.val = ⟨val := T₁val⟩.val`.
  cases h_eq
  -- As the LHS and RHS are identical, this is true by reflexivity of equality (`rfl`). QED.
  rfl

/-- Simplification lemma for `Temperature`:

Zero is less than or equal to the real number representation of a `Temperature` in `ℝ≥0`.
-/
@[simp]
lemma zero_le_nnreal (T : Temperature) : 0 ≤ (T : ℝ≥0) := by
  -- Since `T : ℝ≥0` is defined as `T.val`, we can directly use the fact that `T.val` has the type
  -- `ℝ≥0`, which carries the proof of its non-negativity as part of its type.
  -- Therefore, we can conclude that `0 ≤ (T : ℝ≥0)` by using the property of `T.val`. QED.
  exact T.val.property

/-- Simplification lemma for `Temperature`:

The real number representation of a `Temperature` is greater or equal to zero in `ℝ≥0`.
-/
@[to_dual existing zero_le_nnreal]
lemma nnreal_ge_zero (T : Temperature) : (T : ℝ≥0) ≥ 0 := by
  -- This is a direct consequence of `zero_le_nnreal T` and the equivalence between `a ≤ b` and
  -- `b ≥ a`. QED.
  exact zero_le_nnreal T

/-- Simplification lemma for `Temperature`:

Zero is less than or equal to the real number representation of a `Temperature` in `ℝ`.
-/
@[simp]
lemma zero_le_real (T : Temperature) : 0 ≤ (T : ℝ) := by
  -- Since `T : ℝ` is defined as `Temperature.toReal T`, which is `NNReal.toReal T.val`, we can use
  -- the fact that `T.val` of type `ℝ≥0` is non-negative (previously established in
  -- `zero_le_nnreal T`).
  -- We also know that the function `NNReal.toReal` preserves the order of non-negativity, meaning
  -- that if `0 ≤ (T : ℝ≥0)`, then `0 ≤ (T : ℝ)` as well. QED.
  exact zero_le_nnreal T

/-- Simplification lemma for `Temperature`:

The real number representation of a `Temperature` is greater or equal to zero.
-/
@[to_dual existing zero_le_real]
lemma real_ge_zero (T : Temperature) : (T : ℝ) ≥ 0 := by
  -- This is a direct consequence of `zero_le_real T` and the equivalence between `a ≤ b` and
  -- `b ≥ a`. QED.
  exact zero_le_real T

/-! ### Conversion to and from `ℝ≥0` -/

/-- Simplification function for `Temperature`:

Build a temperature from a nonnegative real number.

- Input:
  - `t` of type `ℝ≥0`: The nonnegative real number representing the temperature.
- Output:
  - Result of type `Temperature`: The temperature constructed from the nonnegative real number.
-/
@[simp]
def ofNNReal (t : ℝ≥0) : Temperature := ⟨t⟩

/-- Simplification lemma for `Temperature`:

The `val` field of a temperature constructed from a nonnegative real number `t` is equal to `t`.
-/
@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := by
  -- Both sides are definitionally equal by the definition of `ofNNReal`. QED.
  rfl

/-- Simplification lemma for `Temperature`:

Coercing a temperature constructed from a nonnegative real number `t` back to `ℝ≥0` returns `t`.
-/
@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := by
  -- Both sides are definitionally equal by the definition of `ofNNReal` and the coercion. QED.
  rfl

/-- Simplification lemma for `Temperature`:

Coercing a temperature constructed from a nonnegative real number `t` to `ℝ` returns `t`.
-/
@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := by
  -- Both sides are definitionally equal by the definition of `ofNNReal` and the coercion. QED.
  rfl

/-- Simplification function for `Temperature`:

Build a temperature from a real number, given a proof that it is nonnegative.
-/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (h_zero_le_t : 0 ≤ t) : Temperature := by
  -- Apply `ofNNReal` to the nonnegative real number `t` to construct the temperature,
  -- using the fact that `t` can be coerced to `ℝ≥0` since it is nonnegative.
  exact ofNNReal ⟨t, h_zero_le_t⟩

/-- Simplification lemma for `Temperature`:

The `val` field of a temperature constructed from a nonnegative real number `t`
is equal to `⟨t, h_zero_le_t⟩`.
-/
@[simp]
lemma ofRealNonneg_val {t : ℝ} (h_zero_le_t : 0 ≤ t) :
    (ofRealNonneg t h_zero_le_t).val = ⟨t, h_zero_le_t⟩ := by
  -- Both sides are definitionally equal by the definition of `ofRealNonneg`. QED.
  rfl

/-! ### Linear order -/

/-- `Temperature` has a linear order inherited from `ℝ≥0` via the `val` field.

The ordering corresponds to the physical ordering of temperatures:
`T₁ ≤ T₂` if and only if `T₁.val ≤ T₂.val` in `ℝ≥0`.
-/
noncomputable instance : LinearOrder Temperature where
  le T₁ T₂ := T₁.val ≤ T₂.val
  lt T₁ T₂ := T₁.val < T₂.val
  le_refl T := le_refl T.val
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h₁ h₂ := ext (le_antisymm h₁ h₂)
  le_total T₁ T₂ := le_total T₁.val T₂.val
  toDecidableLE T₁ T₂ := inferInstanceAs (Decidable (T₁.val ≤ T₂.val))

/-- `Temperature` has a bottom element (absolute zero). -/
noncomputable instance : OrderBot Temperature where
  bot := 0
  bot_le T := zero_le T.val

/-- Simplification lemma for `Temperature`:

`T₁ ≤ T₂` if and only if `T₁.val ≤ T₂.val` in `ℝ≥0`.
-/
@[simp]
lemma le_def {T₁ T₂ : Temperature} : T₁ ≤ T₂ ↔ T₁.val ≤ T₂.val := by
  -- Both sides are definitionally equal by the definition of `le` in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`T₁ < T₂` if and only if `T₁.val < T₂.val` in `ℝ≥0`.
-/
@[simp]
lemma lt_def {T₁ T₂ : Temperature} : T₁ < T₂ ↔ T₁.val < T₂.val := by
  -- Both sides are definitionally equal by the definition of `lt` in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`⟨a⟩ ≤ ⟨b⟩` if and only if `a ≤ b` in `ℝ≥0`.
-/
@[simp]
lemma mk_le_mk {a b : ℝ≥0} : Temperature.mk a ≤ Temperature.mk b ↔ a ≤ b := by
  -- Both sides are definitionally equal by the definition of `mk` and `le`
  -- in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`⟨a⟩ < ⟨b⟩` if and only if `a < b` in `ℝ≥0`.
-/
@[simp]
lemma mk_lt_mk {a b : ℝ≥0} : Temperature.mk a < Temperature.mk b ↔ a < b := by
  -- Both sides are definitionally equal by the definition of `mk` and `lt`
  -- in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

Absolute zero is the minimum temperature.
-/
@[simp]
lemma zero_le (T : Temperature) : (0 : Temperature) ≤ T := by
  -- This follows from the `bot_le` property of the `OrderBot` instance,
  -- which states that the bottom element is less than or equal to any element. QED.
  exact bot_le

/-- Simplification lemma for `Temperature`:

No temperature is strictly less than absolute zero.
-/
@[simp]
lemma not_lt_zero (T : Temperature) : ¬ T < 0 := by
  -- This follows from the `not_lt_bot` property of the `OrderBot` instance,
  -- which states that no element is strictly less than the bottom element. QED.
  exact not_lt_bot

/-- Lemma for `Temperature`:

The coercion to `ℝ` preserves `≤`.
-/
lemma toReal_le_toReal {T₁ T₂ : Temperature} (h_le : T₁ ≤ T₂) : (T₁ : ℝ) ≤ (T₂ : ℝ) := by
  -- Since we have `h_le : T₁ ≤ T₂`, we can apply it to `NNReal.coe_le_coe.mpr`
  -- to conclude that `T₁.val ≤ T₂.val` in `ℝ≥0`.
  exact NNReal.coe_le_coe.mpr h_le

/-- Lemma for `Temperature`:

The coercion to `ℝ` preserves `<`.
-/
lemma toReal_lt_toReal {T₁ T₂ : Temperature} (h_lt : T₁ < T₂) : (T₁ : ℝ) < (T₂ : ℝ) := by
  -- Since we have `h_lt : T₁ < T₂`, we can apply it to `NNReal.coe_lt_coe.mpr`
  -- to conclude that `T₁.val < T₂.val` in `ℝ≥0`. QED.
  exact NNReal.coe_lt_coe.mpr h_lt

/-- Lemma for `Temperature`:

If the coercion to `ℝ` satisfies `≤`, then the temperatures satisfy `≤`.
-/
lemma le_of_toReal_le {T₁ T₂ : Temperature} (h_le : (T₁ : ℝ) ≤ (T₂ : ℝ)) : T₁ ≤ T₂ := by
  -- Since we have `h_le : (T₁ : ℝ) ≤ (T₂ : ℝ)`, we can apply it to `NNReal.coe_le_coe.mp`
  -- to conclude that `T₁.val ≤ T₂.val` in `ℝ≥0`. QED.
  exact NNReal.coe_le_coe.mp h_le

/-- Lemma for `Temperature`:

If the coercion to `ℝ` satisfies `<`, then the temperatures satisfy `<`.
-/
lemma lt_of_toReal_lt {T₁ T₂ : Temperature} (h_lt : (T₁ : ℝ) < (T₂ : ℝ)) : T₁ < T₂ := by
  -- Since we have `h_lt : (T₁ : ℝ) < (T₂ : ℝ)`, we can apply it to `NNReal.coe_lt_coe.mp`
  -- to conclude that `T₁.val < T₂.val` in `ℝ≥0`. QED.
  exact NNReal.coe_lt_coe.mp h_lt

/-- Simplification lemma for `Temperature`:

`ofNNReal` preserves `≤`.
-/
@[simp]
lemma ofNNReal_le_ofNNReal {a b : ℝ≥0} : ofNNReal a ≤ ofNNReal b ↔ a ≤ b := by
  -- Both sides are definitionally equal by the definition of `ofNNReal` and `le`
  -- in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

`ofNNReal` preserves `<`.
-/
@[simp]
lemma ofNNReal_lt_ofNNReal {a b : ℝ≥0} : ofNNReal a < ofNNReal b ↔ a < b := by
  -- Both sides are definitionally equal by the definition of `ofNNReal` and `lt`
  -- in the `LinearOrder` instance.
  -- Therefore, this is true by reflexivity of equivalence (`Iff.rfl`). QED.
  exact Iff.rfl

/-- Simplification lemma for `Temperature`:

The `val` of `min T₁ T₂` is `min T₁.val T₂.val`.
-/
@[simp]
lemma val_min (T₁ T₂ : Temperature) : (min T₁ T₂).val = min T₁.val T₂.val := by
  -- We can simplify the definition of `min` for `Temperature` using the lemmas
  -- `le_def` and `lt_def`, which relate the order on `Temperature` to the order on `ℝ≥0`.
  -- After simplification, the goal is now
  -- `⊢ (if T₁.val ≤ T₂.val then T₁ else T₂).val = if T₁.val ≤ T₂.val then T₁.val else T₂.val`.
  simp only [min_def, le_def]
  -- We can now split into cases based on whether `T₁.val ≤ T₂.val` is true or false.
  -- In the case where `T₁.val ≤ T₂.val`, we have `⊢ T₁.val = T₁.val`,
  -- which is true by reflexivity of equality (`rfl`).
  -- In the case where `T₁.val ≤ T₂.val` is false, we have `⊢ T₂.val = T₂.val`,
  -- which is also true by reflexivity of equality (`rfl`).
  -- Therefore, we can use `split <;> rfl` to short-circuit the cases with reflexivity. QED.
  split <;> rfl

/-- Simplification lemma for `Temperature`:

The `val` of `max T₁ T₂` is `max T₁.val T₂.val`.
-/
@[simp]
lemma val_max (T₁ T₂ : Temperature) : (max T₁ T₂).val = max T₁.val T₂.val := by
  -- We can simplify the definition of `max` for `Temperature` using the lemmas
  -- `le_def` and `lt_def`, which relate the order on `Temperature` to the order on `ℝ≥0`.
  -- After simplification, the goal is now
  -- `⊢ (if T₁.val ≤ T₂.val then T₂ else T₁).val = if T₁.val ≤ T₂.val then T₂.val else T₁.val`.
  simp only [max_def, le_def]
  -- We can now split into cases based on whether `T₁.val ≤ T₂.val` is true or false.
  -- In the case where `T₁.val ≤ T₂.val`, we have `⊢ T₂.val = T₂.val`,
  -- which is true by reflexivity of equality (`rfl`).
  -- In the case where `T₁.val ≤ T₂.val` is false, we have `⊢ T₁.val = T₁.val`,
  -- which is also true by reflexivity of equality (`rfl`).
  -- Therefore, we can use `split <;> rfl` to short-circuit the cases with reflexivity. QED.
  split <;> rfl

end Temperature

/-!
## Basic instances and definitions for `PositiveTemperature`
-/
namespace PositiveTemperature
open Constants

/-- Type coercion (implicit casting) from `PositiveTemperature` to `Temperature`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `Temperature`.
-/
instance : Coe PositiveTemperature Temperature := ⟨fun (T : PositiveTemperature) => T.1⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ≥0`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `ℝ≥0` value.
-/
instance : Coe PositiveTemperature ℝ≥0 := ⟨fun (T : PositiveTemperature) => T.1.val⟩

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ>0`.

Defined as a function that takes a `PositiveTemperature` and returns the underlying `ℝ>0` value,
which is the `val` field of the underlying `Temperature` along with the proof that
it is strictly positive.
-/
instance : Coe PositiveTemperature ℝ>0 := ⟨fun (T : PositiveTemperature) => ⟨T.1.val, T.2⟩⟩

/-- Function for `PositiveTemperature`:

Convert a `PositiveTemperature` to a real number in `ℝ`.
-/
def toReal (T : PositiveTemperature) : ℝ := Temperature.toReal T.1

/-- Type coercion (implicit casting) from `PositiveTemperature` to `ℝ`.

Defined as a function that takes a `PositiveTemperature` and returns the value converted to `ℝ`.
-/
instance : Coe PositiveTemperature ℝ := ⟨fun (T : PositiveTemperature) => T.toReal⟩

/-- Topology on `PositiveTemperature` induced as a subtype of `Temperature`. -/
instance : TopologicalSpace PositiveTemperature := instTopologicalSpaceSubtype

/-- Extensionality lemma for `PositiveTemperature`.

Two `PositiveTemperature` instances are equal if their underlying `Temperature` values are equal.
-/
@[ext]
lemma ext {T₁ T₂ : PositiveTemperature} (h : T₁.1 = T₂.1) : T₁ = T₂ := by
  -- We can prove this by applying the `ext` lemma for subtypes,
  -- which states that two elements of a subtype are equal if their underlying values are equal.
  -- QED.
  exact Subtype.ext h

/-- Simplification lemma for `PositiveTemperature`:

The `val` field (of type `ℝ≥0`) of the underlying `Temperature` is strictly positive.
-/
@[simp]
lemma val_pos (T : PositiveTemperature) : 0 < T.1.val := by
  -- We can prove this by using the property of `PositiveTemperature`,
  -- which states that the `val` field of the underlying `Temperature` is strictly positive.
  -- QED.
  exact T.2

/-- Simplification lemma for `PositiveTemperature`:

The real number representation of a `PositiveTemperature` is strictly positive.
-/
@[simp]
lemma zero_lt_toReal (T : PositiveTemperature) : 0 < (T : ℝ) := by
  -- We can prove this by using the fact property of `PositiveTemperature`,
  -- which states that the `val` field of the underlying `Temperature` is strictly positive.
  -- Since we defined implicit coercions to `ℝ` that access the `val` field,
  -- we can directly conclude that the real number representation of `T` is strictly positive. QED.
  exact T.2

/-- Function for `PositiveTemperature`:

Calculate the inverse temperature `β` corresponding to a given positive temperature `T`.

- Note:

1. This has dimensions equivalent to `Energy` to the power `-1`. Refer to the concept of
"thermodynamic beta" in thermodynamics for more details.
-/
noncomputable def β (T : PositiveTemperature) : ℝ>0 :=
  ⟨1 / (kB * (T : ℝ)), by
    -- We need to show that `1 / (kB * (T : ℝ))` is strictly positive, by applying `div_pos`.
    apply div_pos
    -- The numerator `1` is strictly positive, which is true by the fact that `0 < 1` from `one_pos`.
    -- QED for this case.
    · exact one_pos
    -- The denominator `kB * (T : ℝ)` is strictly positive, which can be shown by applying `mul_pos`.
    · apply mul_pos
      -- The Boltzmann constant `kB` is strictly positive, which is true by the fact that `0 < kB`
      -- from `kB_pos`. QED for this case.
      · exact kB_pos
      -- The real number representation of the positive temperature `T` is strictly positive,
      -- which can be shown by applying `zero_lt_toReal` to `T`. QED for this case.
      -- All cases have been proved. QED.
      · exact zero_lt_toReal T⟩

/-- Simplification lemma for `PositiveTemperature`:

The definition of `β T` unfolds to its explicit formula in terms of `kB` and `T`.
-/
@[simp]
lemma β_eq (T : PositiveTemperature) : β T =
    ⟨1 / (kB * (T : ℝ)), by
      -- Basically this is what defined in `β`.
      apply div_pos
      · exact one_pos
      · apply mul_pos
        · exact kB_pos
        · exact zero_lt_toReal T⟩ := by
  -- Both sides are definitionally equal by the definition of `β`. QED.
  rfl

/-- Simplification lemma for `PositiveTemperature`:

Coercing `β T` from `ℝ≥0` to `ℝ` gives the explicit formula `1 / (kB * (T : ℝ))`.
-/
@[simp]
lemma β_toReal (T : PositiveTemperature) : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := by
  -- The goal is trivial as both sides are definitionally equal by the definition of `β`. QED.
  rfl

/-- Lemma for `PositiveTemperature`:

The inverse temperature `β` is strictly positive for positive temperatures.
-/
lemma β_pos (T : PositiveTemperature) : 0 < (T.β : ℝ) := by
  -- The goal is trivial as `β T` is defined to be a positive real number.
  -- We can directly use the fact that `β T` is of type `{ β : ℝ // 0 < β }`.
  exact (β T).2

/-- Function for `PositiveTemperature`:

Construct a `PositiveTemperature` from a positive inverse temperature `β`.
-/
noncomputable def ofβ (β : ℝ>0): PositiveTemperature :=
  ⟨⟨⟨1 / (kB * β), by
    -- We need to show that `1 / (kB * β)` is nonnegative, by applying `div_nonneg`.
    apply div_nonneg
    -- The numerator `1` is nonnegative, which is true by the fact that `0 ≤ 1` from `zero_le_one`.
    -- QED for this case.
    · exact zero_le_one
    -- The denominator `kB * β` is nonnegative, which can be shown by applying `mul_nonneg`.
    · apply mul_nonneg
      -- The Boltzmann constant `kB` is nonnegative, which is true by the fact that `0 ≤ kB`
      -- from `kB_nonneg`. QED for this case.
      · exact kB_nonneg
      -- The positive inverse temperature `β` is strictly positive,
      -- which implies it is also nonnegative. This can be shown by applying `le_of_lt` to the
      -- property of `β`, which states that `0 < β`. QED for this case.
      · exact le_of_lt β.property⟩⟩,
   by
    -- We need to prove that `⊢ 0 < { val := ⟨1 / (kB * ↑β), ⋯⟩ }.val`,
    -- which can be shown by applying `div_pos` to `1` and `kB * β`.
    -- Since `1` is strictly positive, which is true by the fact that `0 < 1` from `one_pos`,
    -- and `kB` and `β` are strictly positive by `kB_pos` and `β.property`, respectively,
    -- we have `kB * β` is strictly positive by `mul_pos`.
    -- Therefore, we can conclude that `1 / (kB * β)` is strictly positive. QED.
    exact div_pos one_pos (mul_pos kB_pos β.property)⟩

/-- Simplification lemma for `PositiveTemperature`:

Applying `β` to the temperature constructed from `β'` returns `β'`.
-/
@[simp]
lemma β_ofβ (β' : ℝ>0) : β (ofβ β') = β' := by
  -- We apply the extensionality lemma for `PositiveTemperature` to reduce the goal
  -- to show that the underlying values of `β (ofβ β')` and `β'` are equal.
  -- The goal is now `⊢ ↑(ofβ β').β = ↑β'`, both of type `ℝ`.
  ext
  -- We unfold the definitions of `β`, `ofβ`, `toReal`, and `Temperature.toReal` to expose the
  -- raw arithmetic expressions involving `kB` and `β'`.
  -- The goal becomes `⊢ 1 / (kB * ↑⟨1 / (kB * ↑β'), ⋯⟩) = ↑β'`.
  simp only [PositiveTemperature.β, PositiveTemperature.ofβ, PositiveTemperature.toReal,
             Temperature.toReal]
  -- We simplify the coercion `↑⟨1 / (kB * ↑β'), ⋯⟩` to `1 / (kB * ↑β')` using `NNReal.coe_mk`,
  -- which states that coercing a value constructed with `⟨x, h⟩` returns `x`.
  -- The goal becomes `⊢ 1 / (kB * (1 / (kB * ↑β'))) = ↑β'`.
  simp only [NNReal.coe_mk]
  -- We use `field_simp` to clear all denominators and simplify the resulting equation,
  -- using `kB_ne_zero` to discharge the side condition that `kB ≠ 0`.
  -- After clearing denominators, both sides reduce to the same expression. QED.
  field_simp [kB_ne_zero]

/-- Simplification lemma for `PositiveTemperature`:

Rebuilding a positive temperature `T` from its inverse temperature `β` gives back the original.
-/
@[simp]
lemma ofβ_β (T : PositiveTemperature) : ofβ (β T) = T := by
  -- We apply the extensionality lemma for `PositiveTemperature` to reduce the goal
  -- to showing that the underlying values of `ofβ (β T)` and `T` are equal.
  -- The goal is now `⊢ ↑(↑(ofβ T.β)).val = ↑(↑T).val`, both of type `ℝ`.
  ext
  -- We unfold the definitions of `β`, `ofβ`, `Temperature.toReal`, and
  -- `PositiveTemperature.toReal` to expose the raw arithmetic expressions.
  -- The `simp` tactic also simplifies coercions and constructor projections.
  -- The goal becomes `⊢ kB * ↑(↑T).val * kB⁻¹ = ↑(↑T).val`.
  simp [β, ofβ, Temperature.toReal, PositiveTemperature.toReal]
  -- We use `field_simp` to clear all denominators and simplify the resulting equation,
  -- using `kB_ne_zero` to discharge the side condition that `kB ≠ 0`.
  -- After clearing denominators, both sides reduce to the same expression. QED.
  field_simp [kB_ne_zero]

/-- The thermodynamic equivalence between positive temperature and positive inverse temperature.
-/
noncomputable def equiv_β : PositiveTemperature ≃ ℝ>0 where
  toFun := β
  invFun := ofβ
  left_inv := ofβ_β
  right_inv := β_ofβ

end PositiveTemperature

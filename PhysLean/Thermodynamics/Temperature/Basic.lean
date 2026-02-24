/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant

/-!
# Temperature

In this module we define the type `Temperature`, corresponding to absolute thermodynamic temperature
measured in kelvin.

This is the version of temperature most often used in undergraduate and non-mathematical physics.

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
  - `val` of type `ℝ≥0`: The nonnegative real value of the temperature.
-/
structure Temperature where
  /-- The nonnegative real value of the temperature. -/
  val : ℝ≥0

/-!
## Basic instances and definitions for `Temperature`.

In this namespace we provide basic instances and definitions for the `Temperature` type, including
coercions to `ℝ≥0` and `ℝ`, the definition of inverse temperature `β`, and basic lemmas about these
concepts.
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
noncomputable def toReal (T : Temperature) : ℝ := NNReal.toReal T.val

/-- Type coercion (implicit casting) from `Temperature` to `ℝ`.

Defined as a function that takes a `Temperature` and returns the `val` field converted to `ℝ`.
-/
noncomputable instance : Coe Temperature ℝ := ⟨fun (T : Temperature) => Temperature.toReal T⟩

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
  -- Substitutes `T₁` with its constructor form. We have `T₁ = ⟨val := T₁val⟩` in `h_eq` and the
  -- goal.
  cases T₁ with
  | mk T₁val
  -- Substitutes `T₂` with its constructor form. We have `T₂ = ⟨val := T₂val⟩` in `h_eq` and the
  -- goal.
  cases T₂ with
  | mk T₂val
  -- The proof currently has `h_eq: { val := T₁val }.val = { val := T₂val }.val` and
  -- `⊢ ⟨val := T₁val⟩.val = ⟨val := T₂val⟩.val`.
  -- Substitutes `h_eq` into the goal, replacing `T₂.val` with `T₁.val`. We now have
  -- `⊢ ⟨val := T₁val⟩.val = ⟨val := T₁val⟩.val`.
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
@[simp]
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
@[simp]
lemma real_ge_zero (T : Temperature) : (T : ℝ) ≥ 0 := by
  -- This is a direct consequence of `zero_le_real T` and the equivalence between `a ≤ b` and
  -- `b ≥ a`. QED.
  exact zero_le_real T

/-- Function for `Temperature`:

Calculate the inverse temperature `β` corresponding to a given temperature `T`.

- Note:

1. This has dimensions equivalent to `Energy` to the power `-1`. Refer to the concept of
"thermodynamic beta" in thermodynamics for more details.

2. Currently this formula allows for "non-negative" temperatures, which includes absolute zero in
the denominator. In physical terms, absolute zero is a limit that cannot be reached, and the formula
for `β` is not well-defined at `T = 0`. Therefore, while the type `Temperature` allows for `T = 0`,
we should refactor this definition in the future to exclude absolute zero, either by refining the
domain or by defining `β` as a partial function that is only defined for strictly positive
temperatures.
-/
noncomputable def β (T : Temperature) : ℝ≥0 :=
  -- Given the formula `(1 / (kB * (T : ℝ))) : ℝ≥0`, we need to show that this is non-negative to
  -- fit the type `ℝ≥0`.
  ⟨1 / (kB * (T : ℝ)), by
    -- To show that `1 / (kB * (T : ℝ))` is non-negative, we apply `div_nonneg`, which requires us
    -- to show that the numerator is non-negative and the denominator is non-negative [See Note 2].
    apply div_nonneg
    -- `case ha`: The goal is `⊢ 0 ≤ 1`, which is true by `zero_le_one`, since `1` is a non-negative
    -- real number. QED for this case.
    · exact zero_le_one
    -- `case hb`: The goal is `⊢ 0 ≤ kB * (T : ℝ)`, which we can show by applying `mul_nonneg` to
    -- the product `kB * (T : ℝ)`.
    · apply mul_nonneg
      -- `case hb.ha`: The goal is `⊢ 0 ≤ kB`, which is true by the lemma `kB_nonneg`, since the
      -- Boltzmann constant is a positive physical constant. QED for this case.
      · exact kB_nonneg
      -- `case hb.hb`: The goal is `⊢ 0 ≤ (T : ℝ)`, which is true by `zero_le_real T`, since the
      -- real number representation of a `Temperature` is non-negative. QED for this case.
      -- All cases have been proven. QED.
      · exact zero_le_real T⟩

/-- Simplification lemma for `Temperature`:

The definition of `β T` unfolds to its explicit formula in terms of `kB` and `T`.
-/
@[simp]
lemma β_eq (T : Temperature) : β T =
    ⟨1 / (kB * (T : ℝ)), by
      apply div_nonneg
      · exact zero_le_one
      · apply mul_nonneg
        · exact kB_nonneg
        · exact zero_le_real T⟩ := by
  -- Since the definition of `β T` in the left-hand side is exactly the same as the right-hand side,
  -- this is true by reflexivity of equality (`rfl`). QED.
  rfl

/-- Simplification lemma for `Temperature`:

Coercing `β T` from `ℝ≥0` to `ℝ` gives the explicit formula `1 / (kB * (T : ℝ))`.
-/
@[simp]
lemma β_toReal (T : Temperature) : (β T : ℝ) = (1 : ℝ) / (kB * (T : ℝ)) := by
  -- We rewrite the goal using the definition of `β` from the previous lemma `β_eq`, which gives us
  -- `⊢ ↑⟨1 / (kB * T.toReal), ⋯⟩ = 1 / (kB * T.toReal)`, where `↑` denotes the coercion from `ℝ≥0`
  -- to `ℝ`, and `⋯` represents the proof of non-negativity that we can ignore since it does not
  -- affect the real value.
  rw [β_eq]
  -- The coercion from `ℝ≥0` to `ℝ` for the left-hand side gives us the same expression as the
  -- right-hand side, since the coercion simply takes the underlying real value. Therefore, both
  -- sides are definitionally equal, and we can conclude that they are equal by reflexivity of
  -- equality (`rfl`). QED.
  rfl

/-- Function for `Temperature`:

Calculate the temperature associated with a given inverse temperature `β`.
-/
noncomputable def ofβ (β : ℝ≥0) : Temperature :=
  -- Given the formula `1 / (kB * β)`, we need to show that this is non-negative to fit the type
  -- `Temperature`.
  ⟨⟨1 / (kB * β), by
    -- To show that `1 / (kB * β)` is non-negative, we apply `div_nonneg`, which requires us to show
    -- that the numerator is non-negative and the denominator is non-negative.
    apply div_nonneg
    -- `case ha`: The goal is `⊢ 0 ≤ 1`, which is true by `zero_le_one`, since `1` is a non-negative
    -- real number. QED for this case.
    · exact zero_le_one
    -- `case hb`: The goal is `⊢ 0 ≤ kB * β`, which we can show by applying `mul_nonneg` to the
    -- product `kB * β`.
    · apply mul_nonneg
      -- `case hb.ha`: The goal is `⊢ 0 ≤ kB`, which is true by the lemma `kB_nonneg`, since the
      -- Boltzmann constant is a positive physical constant.
      · exact kB_nonneg
      -- `case hb.hb`: The goal is `⊢ 0 ≤ β`, which is true by the fact that `β : ℝ≥0` carries the
      -- proof of its non-negativity as part of its type. QED for this case.
      -- All cases have been proven. QED.
      · exact β.property⟩⟩

/-- Simplification lemma for `Temperature`:

The definition of `ofβ` unfolds to its explicit formula in terms of `kB` and `β`.
-/
@[simp]
lemma ofβ_eq : ofβ = fun (β : ℝ≥0) => ⟨⟨1 / (kB * β), by
    apply div_nonneg
    · exact zero_le_one
    · apply mul_nonneg
      · exact kB_nonneg
      · exact β.property⟩⟩ := by
  -- Since the definition of `ofβ` in the left-hand side is exactly the same as the right-hand side,
  -- this is true by reflexivity of equality (`rfl`). QED.
  rfl

/-- Simplification lemma for `Temperature`:

Applying `β` to the temperature constructed from `β'` returns `β'`.
-/
@[simp]
lemma β_ofβ (β' : ℝ≥0) : β (ofβ β') = β' := by
  -- We use `ext` to apply the extensionality lemma for `Temperature`, which reduces the goal to
  -- show that the `val` fields of both sides are equal. The goal is now
  -- `⊢ ↑(ofβ β').β = ↑β'`, where `↑` denotes the coercion from `ℝ≥0` to `ℝ`.
  ext
  -- We simplify the goal with `simp [β, ofβ, Temperature.toReal]`. The goal is now
  -- `⊢ kB * ↑β' * kB⁻¹ = ↑β'`.
  simp [β, ofβ, Temperature.toReal]
  -- We apply `field_simp [kB_ne_zero]` to reduce the `kB * ↑β' * kB⁻¹` to `↑β'`, as `kB_ne_zero`
  -- ensures that `kB` is nonzero and thus the simplification is valid. Since both sides are now
  -- `↑β'`, they are definitionally equal without needing to invoke reflexivity of equality. QED.
  field_simp [kB_ne_zero]

/-- Simplification lemma for `Temperature`:

Rebuilding a temperature `T` from its inverse temperature `β` gives back the original temperature.
-/
@[simp]
lemma ofβ_β (T : Temperature) : ofβ (β T) = T := by
  -- We use `ext` to apply the extensionality lemma for `Temperature`, which reduces the goal to
  -- show that the `val` fields of both sides are equal. The goal is now
  -- `⊢ ↑(ofβ T.β).val = ↑T.val`, where `↑` denotes the coercion from `ℝ≥0` to `ℝ`.
  ext
  -- We simplify the goal with `simp [β, ofβ, Temperature.toReal]`. The goal is now
  -- `⊢ kB * ↑T.val * kB⁻¹ = ↑T.val`.
  simp [β, ofβ, Temperature.toReal]
  -- We apply `field_simp [kB_ne_zero]` to reduce the `kB * ↑T.val * kB⁻¹` to `↑T.val`, as
  -- `kB_ne_zero` ensures that `kB` is nonzero and thus the simplification is valid. Since both
  -- sides are now `↑T.val`, they are definitionally equal without needing to invoke reflexivity of
  -- equality. QED.
  field_simp [kB_ne_zero]

/-- Lemma for `Temperature`:

The inverse temperature `β` is strictly positive when temperature `T` is strictly positive.
-/
lemma β_pos (T : Temperature) (h_T_pos : 0 < T.val) : 0 < (T.β : ℝ) := by
  -- We simplify the goal with `simp [Temperature.β]`, which unfolds the definition of `β` and gives
  -- us the goal `⊢ 0 < T.toReal⁻¹ * kB⁻¹`.
  simp [Temperature.β]
  -- We apply `mul_pos` to show that the product `T.toReal⁻¹ * kB⁻¹` is positive by showing that
  -- both factors are positive.
  apply mul_pos
  -- `case ha`: The goal is `⊢ 0 < T.toReal⁻¹`, which we can rewrite using `inv_eq_one_div` to get
  -- `⊢ 0 < 1 / T.toReal`. Then, we rewrite the goal using `one_div_pos`, which states that
  -- `1 / a > 0` if and only if `a > 0`. This gives us the goal `⊢ 0 < T.toReal`.
  · rw [inv_eq_one_div, one_div_pos]
    -- The goal is now `⊢ 0 < T.toReal`, which is true by the fact that `T.toReal` is defined as
    -- `NNReal.toReal T.val`, and since `T.val` is strictly positive (given by `h_T_pos`), its real
    -- representation is also strictly positive. QED for this case.
    exact h_T_pos
  -- `case hb`: The goal is `⊢ 0 < kB⁻¹`, which we can rewrite using `inv_eq_one_div` to get
  -- `⊢ 0 < 1 / kB`. Then, we rewrite the goal using `one_div_pos`, which states that `1 / a > 0`
  -- if and only if `a > 0`. This gives us the goal `⊢ 0 < kB`.
  · rw [inv_eq_one_div, one_div_pos]
    -- The goal is now `⊢ 0 < kB`, which is true by the lemma `kB_pos`, since the Boltzmann constant
    -- is a positive physical constant. QED for this case.
    -- All cases have been proven. QED.
    exact kB_pos

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

end Temperature

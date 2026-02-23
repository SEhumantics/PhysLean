/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.Meta.TODO.Basic

/-!
# Temperature

In this module we define the type `Temperature`, corresponding to absolute thermodynamic temperature measured in kelvin.

This is the version of temperature most often used in undergraduate and non-mathematical physics.

For affine display scales with offsets (such as Celsius and Fahrenheit), see
`PhysLean.Thermodynamics.Temperature.TemperatureScales`.
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

/-- Convert a `Temperature` to a real number.
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

/-- Calculate the inverse temperature `β` corresponding to a given temperature `T`.

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
lemma β_toReal (T : Temperature) : (β T : ℝ) = (1 :  ℝ) / (kB * (T : ℝ)) := by
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


/-- Calculate the temperature associated with a given inverse temperature `β`.
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

/-! ### Regularity of `ofβ` === TODO TIL THE END OF THE FILE -/

open Filter Topology

/-- Helper lemma for `Temperature`:

The denominator of `ofβ` is nonnegative.
-/
private lemma ofβ_den_nonneg (b : ℝ≥0) : 0 ≤ kB * (b : ℝ) := by
  -- We apply `mul_nonneg` to show that the product `kB * (b : ℝ)` is nonnegative by showing that
  -- both factors are nonnegative.
  apply mul_nonneg
  -- `case ha`: The goal is `⊢ 0 ≤ kB`, which is true by the lemma `kB_nonneg`, since the Boltzmann
  -- constant is a positive physical constant. QED for this case.
  · exact kB_nonneg
  -- `case hb`: The goal is `⊢ 0 ≤ (b : ℝ)`, which is true by the fact that `b` of type `ℝ≥0`
  -- carries the proof `b.property : 0 ≤ (b : ℝ)`. QED for this case.
  · exact b.property
  -- All cases have been proven. QED.

/-- Helper lemma for `Temperature`:

The real-valued expression `1 / (kB * b)` is nonnegative.
-/
private lemma ofβ_real_nonneg (b : ℝ≥0) : 0 ≤ (1 : ℝ) / (kB * (b : ℝ)) := by
  -- We apply `div_nonneg` to show that the fraction `1 / (kB * b)` is nonnegative by showing that
  -- both the numerator and the denominator are nonnegative.
  apply div_nonneg
  -- `case ha`: The goal is `⊢ 0 ≤ 1`, which is true by the lemma `zero_le_one`. QED for this case.
  · exact zero_le_one
  -- `case hb`: The goal is `⊢ 0 ≤ kB * (b : ℝ)`, which is true by the lemma `ofβ_den_nonneg b`.
  -- QED for this case.
  · exact ofβ_den_nonneg b
  -- All cases have been proven. QED.

/-- Helper lemma for `Temperature`:

Continuity at a positive point for the real formula `(t : ℝ) ↦ (1 :  ℝ) / (kB * t)`.
-/
private lemma ofβ_realExpr_continuousAt_real (x : ℝ≥0) (h_x_pos : 0 < x) :
    ContinuousAt (fun (t : ℝ) => (1 : ℝ) / (kB * t)) (x : ℝ) := by
  -- We refine the goal using `ContinuousAt.div₀`, which requires us to prove continuity of the
  -- numerator and denominator separately:
  refine ContinuousAt.div₀ ?_ ?_ ?_
  -- `case refine_1`: The goal is `⊢ ContinuousAt (fun t => 1) ↑x`.
  -- This is true because constant functions are continuous everywhere. We use `fun_prop` to
  -- establish this.
  · fun_prop
  -- `case refine_2`: The goal is `⊢ ContinuousAt (HMul.hMul kB) ↑x`.
  -- This is true because multiplication by a constant is continuous everywhere.
  -- We use `fun_prop` to establish this.
  · fun_prop
  -- `case refine_3`: The goal is `⊢ kB * ↑x ≠ 0`.
  -- We have the hypothesis `h_x_ne_zero : (x : ℝ) ≠ 0` derived from `ne_of_gt h_x_pos`;
  -- which means: "Given a and b, if a > b, then a ≠ b" - and since we have `0 < x`,
  -- we conclude `x ≠ 0`.
  · have h_x_ne_zero : (x : ℝ) ≠ 0 := by
      exact (ne_of_gt h_x_pos)
    exact mul_ne_zero kB_ne_zero h_x_ne_zero

/-- Helper lemma for `Temperature`:

Continuity at a positive point for the same formula on `ℝ≥0`.
-/
private lemma ofβ_realExpr_continuousAt_nnreal (x : ℝ≥0) (h_x_pos : 0 < x) :
    ContinuousAt (fun (b : ℝ≥0) => (1 : ℝ) / (kB * b)) x := by
  -- We define `f : ℝ≥0 → ℝ` as `f (b : ℝ≥0) := (1 : ℝ) / (kB * b)`.
  -- This is the same as the function in the goal, but we give it a name for clarity.
  let f : ℝ≥0 → ℝ := fun (b : ℝ≥0) => (1 : ℝ) / (kB * b)
  -- We define `g : ℝ → ℝ` as `g (t : ℝ) := (1 :  ℝ) / (kB * t)`.
  -- This is the same formula as `f`, but defined on `ℝ`.
  let g : ℝ → ℝ := fun (t : ℝ) => (1 :  ℝ) / (kB * t)
  -- We define `h : ℝ≥0 → ℝ` as `h (b : ℝ≥0) := (b : ℝ)`.
  -- This is the coercion from `ℝ≥0` to `ℝ`.
  let h : ℝ≥0 → ℝ := fun (b : ℝ≥0) => (b : ℝ)
  -- We then prove that `f = g ∘ h` by simplifying both sides and showing they are equal.
  -- This is done by `rfl`, since both sides are definitionally equal.
  have f_eq_g_comp_h : f = (g ∘ h) := by
    rfl
  -- We then prove that `g` is continuous at `x : ℝ` using the previous lemma `ofβ_realExpr_continuousAt_real x h_x_pos`, resulting in the hypothesis `h_continuousAt_real`.
  have h_continuousAt_real : ContinuousAt g (x : ℝ) := ofβ_realExpr_continuousAt_real x h_x_pos
  -- We also prove that `h` is continuous at `x : ℝ≥0` using `continuous_subtype_val.continuousAt`,
  -- which states that the coercion from a subtype to its parent type is continuous at every point,
  -- resulting in the hypothesis `h_continuousAt_subtype`.
  have h_continuousAt_subtype : ContinuousAt h (x : ℝ≥0) := continuous_subtype_val.continuousAt
  -- Finally, we conclude that `f` is continuous at `x` by using the composition of
  -- continuous functions: `h_continuousAt_real.comp h_continuousAt_subtype`. QED.
  exact h_continuousAt_real.comp h_continuousAt_subtype

/-- Helper lemma for `Temperature`:

Continuity at a positive point for the `ℝ≥0`-valued `val` component of `ofβ`.
-/
private lemma ofβ_val_continuousAt (x : ℝ≥0) (h_x_pos : 0 < x) :
    ContinuousAt (fun (b : ℝ≥0) => ((ofβ b).val : ℝ≥0)) x := by
  -- We define `f : ℝ≥0 → ℝ` as `f (b : ℝ≥0) := (1 : ℝ) / (kB * b)`,
  -- which is the real-valued formula used by `ofβ`.
  let f : ℝ≥0 → ℝ := fun b => (1 : ℝ) / (kB * b)
  -- Then, we prove that `f` is continuous at `x` using the previous lemma
  -- `ofβ_realExpr_continuousAt_nnreal x h_x_pos`,
  -- resulting in the hypothesis `h_f_continuousAt`.
  have h_continuousAt_nnreal : ContinuousAt f x := by
    exact ofβ_realExpr_continuousAt_nnreal x h_x_pos
  -- Next, we prove that `f` is nonnegative for all `b : ℝ≥0` using the lemma `ofβ_real_nonneg b`,
  -- resulting in the hypothesis `h_f_nonneg`.
  have h_f_nonneg : ∀ b : ℝ≥0, 0 ≤ f (b : ℝ≥0) := by
    intro b
    exact ofβ_real_nonneg b
  -- We then define `g : ℝ≥0 → ℝ≥0` as `g (b : ℝ≥0) := ⟨f b, h_f_nonneg b⟩`,
  -- which is the same formula as `f` but with codomain restricted to `ℝ≥0`.
  let g : ℝ≥0 → ℝ≥0 := fun b => (⟨f b, h_f_nonneg b⟩ : ℝ≥0)
  -- We prove that `g` is continuous at `x` by using the fact that if a real-valued function
  -- is continuous, then its codomain-restricted version is also continuous.
  -- This gives us the hypothesis `h_g_continuousAt`.
  have h_g_continuousAt : ContinuousAt g x := by
    exact h_continuousAt_nnreal.codRestrict h_f_nonneg
  -- Finally, we conclude that the `val` component of `ofβ` is continuous at `x`
  -- by using the hypothesis `h_g_continuousAt`,
  -- since `g` is definitionally equal to the function we want to prove continuous. QED.
  exact h_g_continuousAt

/-- Helper lemma for `Temperature`:

The topology on `Temperature` is induced by the coercion to `ℝ≥0`.
-/
private lemma temperature_val_isInducing :
    Topology.IsInducing (fun T : Temperature => (T.val : ℝ≥0)) := by
  -- This is immediate from the topology instance definition,
  -- which is exactly `induced` by this coercion map.
  -- Therefore the witness is `⟨rfl⟩`.
  exact ⟨rfl⟩

/-- Helper lemma for `Temperature`:

Continuity of `ofβ` at every strictly positive input.
-/
private lemma ofβ_continuousAt_of_pos (x : ℝ≥0) (h_x_pos : 0 < x) :
    ContinuousAt (ofβ : ℝ≥0 → Temperature) x := by
  -- We refine the goal using `temperature_val_isInducing.continuousAt_iff`,
  -- which states that continuity of a function into `Temperature` can be checked
  -- by continuity of its composition with the coercion to `ℝ≥0`.
  -- The goal is now `⊢ ContinuousAt ((fun T => T.val) ∘ ofβ) x`.
  refine (temperature_val_isInducing.continuousAt_iff).mpr ?_
  -- This is exactly the content of the previous lemma `ofβ_val_continuousAt x h_x_pos`,
  -- so we apply that to conclude. QED.
  exact ofβ_val_continuousAt x h_x_pos

/-- Lemma for `Temperature`:

The function `ofβ` is continuous on the interval `(0, ∞)`.
-/
lemma ofβ_continuousOn : ContinuousOn (ofβ : ℝ≥0 → Temperature) (Set.Ioi 0) := by
  -- We refine the goal using `continuousOn_of_forall_continuousAt`,
  -- which reduces continuity on a set to continuity at every point in that set.
  -- The goal is now `⊢ ∀ x ∈ Set.Ioi 0, ContinuousAt ofβ x`.
  refine continuousOn_of_forall_continuousAt ?_
  -- We introduce `x : ℝ≥0` and the hypothesis `h_x_in_set : x ∈ Set.Ioi 0` from the goal.
  intro x h_x_in_set
  -- From `h_x_in_set`, we derive `h_x_pos : 0 < x` by:
  have h_x_pos : 0 < x := by
    -- Simplifying the definition of `Set.Ioi 0`, which states that `x ∈ Set.Ioi 0` means `0 < x`.
    simp at h_x_in_set
    -- Extracting the strict inequality `0 < x` from this definition.
    exact h_x_in_set
  -- Given `x : ℝ≥0` and `h_x_pos : 0 < x`,
  -- we can prove the goal with `ofβ_continuousAt_of_pos x h_x_pos`. QED.
  exact ofβ_continuousAt_of_pos x h_x_pos

/-- Lemma for `Temperature`:

The function `ofβ` is differentiable on the interval `(0, ∞)`.
-/
lemma ofβ_differentiableOn :
    DifferentiableOn ℝ (fun (x : ℝ) => ((ofβ (Real.toNNReal x)).val : ℝ)) (Set.Ioi 0) := by
  -- We refine the goal using `DifferentiableOn.congr`, which allows us to prove differentiability
  -- by showing that the function is equal to a simpler function that we can easily differentiate.
  -- We now have two cases:
  refine DifferentiableOn.congr (f := fun (x : ℝ) => (1 :  ℝ) / (kB * x)) ?_ ?_
  -- `case refine_1` : The goal is `⊢ DifferentiableOn ℝ (fun x => 1 / (kB * x)) (Set.Ioi 0)`.
  -- We further refine this using `DifferentiableOn.fun_div`, which requires us
  -- to prove differentiability of the numerator and denominator separately,
  -- and that the denominator is nonzero on the set:
  · refine DifferentiableOn.fun_div ?_ ?_ ?_
    -- `case refine_1.refine_1` : The goal is `⊢ DifferentiableOn ℝ (fun x => 1) (Set.Ioi 0)`.
    -- This is true because constant functions are differentiable everywhere.
    -- We use `fun_prop` to establish this.
    · fun_prop
    -- `case refine_1.refine_2` : The goal is `⊢ DifferentiableOn ℝ (HMul.hMul kB) (Set.Ioi 0)`.
    -- This is true because multiplication by a constant is differentiable everywhere.
    -- We use `fun_prop` to establish this.
    · fun_prop
    -- `case refine_1.refine_3` : The goal is `⊢ ∀ x ∈ Set.Ioi 0, kB * x ≠ 0`.
    -- We introduce `x : ℝ` and the hypothesis `h_x_in_set : x ∈ Set.Ioi 0` from the goal.
    -- The goal is now `⊢ kB * x ≠ 0`.
    · intro x h_x_in_set
      -- We derive `h_x_ne_zero : x ≠ 0` from `h_x_in_set` by noting that
      -- if `x` is strictly greater than `0`, then it cannot be equal to `0`.
      have h_x_ne_zero : x ≠ 0 := by
        exact ne_of_gt h_x_in_set
      -- We then apply `mul_ne_zero` to conclude that `kB * x` is nonzero.
      apply mul_ne_zero
      -- The first factor `kB` is nonzero by `kB_ne_zero`.
      · exact kB_ne_zero
      -- The second factor `x` is nonzero by `h_x_ne_zero`.
      -- This completes the proof of this case. QED for `refine_1.refine_3`.
      -- QED for `refine_1`.
      · exact h_x_ne_zero
  -- `case refine_2` : The goal is
  -- `⊢ ∀ x ∈ Set.Ioi 0, ↑(ofβ x.toNNReal).val = (fun x => 1 / (kB * x)) x`.
  -- We introduce `x : ℝ` and the hypothesis `h_x_in_set : x ∈ Set.Ioi 0` from the goal.
  -- The goal is now `↑(ofβ x.toNNReal).val = (fun x => 1 / (kB * x)) x`.
  · intro x h_x_in_set
    -- We derive `h_x_pos : 0 < x` from `h_x_in_set` by simplifying the definition of `Set.Ioi 0`
    -- to extract the strict inequality `0 < x`.
    have h_x_pos : 0 < x := by
      simp at h_x_in_set
      exact h_x_in_set
    -- We also derive `h_x_nonneg : 0 ≤ x` from `h_x_pos` by noting that
    -- if `x` is strictly greater than `0`, then it can be considered as
    -- "greater than or equal to `0`" as well (since `0 < x` implies `0 ≤ x`).
    have h_x_nonneg : 0 ≤ x := by
      simpa using h_x_pos.le
    -- We then simplify the goal using `simp` to get a new goal
    -- that is a disjunction: `⊢ 0 ≤ x ∨ kB = 0`.
    simp
    -- We only have to prove the left disjunct `0 ≤ x` since `kB` is nonzero by `kB_ne_zero`
    -- (thus the right disjunct is false).
    left
    -- We have already established `h_x_nonneg : 0 ≤ x`, so we can conclude this case
    -- by left disjunction and using `h_x_nonneg`.
    -- This completes the proof of this case. QED for `refine_2`.
    -- All cases have been proven. QED.
    simp [h_x_nonneg]

/-! ### Convergence -/

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
  -- We then unfold the definition of `ofβ`
  -- to express `(ofβ b).toReal` as `{ val := ⟨1 / (kB * ↑b), ⋯⟩ }.toReal`.
  -- The `⋯` represents the proof of non-negativity that we can ignore since it does not
  -- affect the real value.
  unfold ofβ
  -- Finally, we conclude that the goal `(1 : ℝ) / (kB * (b : ℝ)) > 0` is true by `h_quotient_pos`.
  -- QED.
  exact h_quotient_pos

/-- Helper lemma: Positivity of the epsilon-delta bound construction. (TODO)
-/
private lemma tendsto_const_inv_mul_bound_pos (a ε : ℝ) (h_a_pos : 0 < a) (h_ε_pos : 0 < ε) : 0 < (1 / (a * ε)) + 1 := by
  -- We first prove that `1 / (a * ε)` is positive.
  have h_reciprocal_pos : 0 < (1 / (a * ε)) := by
    -- We derive `h_product_pos : 0 < a * ε` using `mul_pos h_a_pos h_ε_pos`, which states that the product of two positive numbers is positive (proof of `a` and `ε` being positive are given by `h_a_pos` and `h_ε_pos`).
    have h_product_pos : 0 < a * ε := by
      exact mul_pos h_a_pos h_ε_pos
    -- We then apply `one_div_pos.mpr h_product_pos` to conclude that `1 / (a * ε)` is positive, since the reciprocal of a positive number is also positive. We derive `h_reciprocal_pos : 0 < (1 / (a * ε))` from this.
    exact one_div_pos.mpr h_product_pos
  -- Finally, we conclude that `0 < (1 / (a * ε)) + 1` by applying `add_pos h_reciprocal_pos zero_lt_one`, which states that the sum of two positive numbers is positive. Here, `h_reciprocal_pos` provides the positivity of the first term, and `zero_lt_one` provides the positivity of the second term. QED.
  exact add_pos h_reciprocal_pos zero_lt_one

/-- Helper lemma: Product positivity via transitivity of ordering.
-/
private lemma tendsto_const_inv_mul_product_pos_of_le (a b_lower_bound b : ℝ) (h_a_pos : 0 < a) (h_b_lower_bound_pos : 0 < b_lower_bound) (h_b_lower_bound_le_b : b_lower_bound ≤ b) : 0 < a * b := by
  -- From `0 < b_lower_bound ≤ b`, we obtain `0 < b` by transitivity using `lt_of_lt_of_le` applied to `h_b_lower_bound_pos` (`0 < b_lower_bound`) and `h_b_lower_bound_le_b` (`b_lower_bound ≤ b`).
  have h_b_pos : 0 < b := lt_of_lt_of_le h_b_lower_bound_pos h_b_lower_bound_le_b
  -- Then apply `mul_pos` to `h_a_pos` and `h_b_pos` to get `0 < a * b`. QED.
  exact mul_pos h_a_pos h_b_pos

/-- Helper lemma: Antitonicity of reciprocal function with constant multiplier.
-/
private lemma tendsto_const_inv_mul_reciprocal_antitone (a b_lower_bound b : ℝ) (h_a_pos : 0 < a) (h_product_b_lower_bound_pos : 0 < a * b_lower_bound) (h_b_lower_bound_le_b : b_lower_bound ≤ b) : (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound) := by
  -- First, we derive `h_denom_le : (a * b_lower_bound) ≤ (a * b)` by applying `mul_le_mul_of_nonneg_left` to `h_b_lower_bound_le_b` and the nonnegativity of `a` (which follows from its positivity `h_a_pos`).
  have h_denom_le : (a * b_lower_bound) ≤ (a * b) := by
    exact mul_le_mul_of_nonneg_left h_b_lower_bound_le_b (le_of_lt h_a_pos)
  -- Then we apply `one_div_le_one_div_of_le` to `h_product_b_lower_bound_pos` and `h_denom_le` to conclude that the reciprocal of the larger denominator is less than or equal to the reciprocal of the smaller denominator, which establishes the antitonicity. QED.
  exact one_div_le_one_div_of_le h_product_b_lower_bound_pos h_denom_le

/-- Helper lemma: Evaluating the function at the constructed bound yields a value less than `ε`.
-/
private lemma tendsto_const_inv_mul_at_bound_lt_epsilon (a ε : ℝ) (h_a_pos : 0 < a) (h_ε_pos : 0 < ε) : (1 : ℝ) / (a * ((1 / (a * ε)) + 1)) < ε := by
  -- We first simplify the expression by performing field simplification with `field_simp` to rewrite the goal into `⊢ 1 < 1 + a * ε`.
  field_simp
  -- We then simplify further using `simp` to reduce the goal to `⊢ 0 < a * ε`.
  simp
  -- We derive `h_product_pos : 0 < a * ε` using `mul_pos h_a_pos h_ε_pos`, which states that the product of two positive numbers is positive. This gives us the desired inequality. QED.
  have h_product_pos : 0 < a * ε := by
    exact mul_pos h_a_pos h_ε_pos
  exact h_product_pos


/-- Helper lemma: Conversion from nonnegative inequality to metric space distance.
-/
private lemma tendsto_const_inv_mul_nonneg_to_dist (x ε : ℝ) (h_x_nonneg : 0 ≤ x) (h_x_lt_ε : x < ε) : dist x 0 < ε := by
  -- We first derive `h_abs_lt : |x| < ε` by calling `simpa [abs_of_nonneg h_x_nonneg] using h_x_lt_ε`, which simplifies the absolute value of `x` using the fact that `x` is nonnegative, and then applies the hypothesis that `x < ε`.
  have h_abs_lt : |x| < ε := by
    simpa [abs_of_nonneg h_x_nonneg] using h_x_lt_ε
  -- We then rewrite the goal `dist x 0 < ε` using `Real.dist_eq` to express the distance in terms of absolute value (`dist x 0` is equal to `|x - 0|`), and use `sub_zero` to simplify this to `|x| < ε`.
  rw [Real.dist_eq, sub_zero]
  -- Finally, we conclude that `|x| < ε` is true by `h_abs_lt`. QED.
  exact h_abs_lt

/-- Helper lemma: Given a lower bound on `b` that ensures the function value is less than `ε`, we can conclude that for any `b` greater than or equal to that lower bound, the function value is nonnegative and less than `ε`.
-/
private lemma tendsto_const_inv_mul_nonneg_and_lt_of_bound (a ε b_lower_bound b : ℝ) (h_a_pos : 0 < a)(h_b_lower_bound_pos : 0 < b_lower_bound) (h_b_lower_bound_le_b : b_lower_bound ≤ b) (h_at_bound_lt : (1 : ℝ) / (a * b_lower_bound) < ε) : 0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε := by
  -- We first derive `h_prod_lower_pos : 0 < a * b_lower_bound` using `mul_pos h_a_pos h_b_lower_bound_pos`, which states that the product of two positive numbers is positive.
  have h_prod_lower_pos : 0 < a * b_lower_bound := by
    exact mul_pos h_a_pos h_b_lower_bound_pos
  -- We then derive `h_prod_pos : 0 < a * b` using the previous lemma `tendsto_const_inv_mul_product_pos_of_le a b_lower_bound b h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b`, which states that if `b` is greater than or equal to a positive lower bound, then the product `a * b` is also positive.
  have h_prod_pos : 0 < a * b := by
    exact tendsto_const_inv_mul_product_pos_of_le a b_lower_bound b h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b
  -- Next, we derive `h_rec_le : (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound)` using the previous lemma `tendsto_const_inv_mul_reciprocal_antitone a b_lower_bound b h_a_pos h_prod_lower_pos h_b_lower_bound_le_b`, which states that the reciprocal function is antitone.
  have h_rec_le : (1 : ℝ) / (a * b) ≤ (1 : ℝ) / (a * b_lower_bound) := by
    exact tendsto_const_inv_mul_reciprocal_antitone a b_lower_bound b h_a_pos h_prod_lower_pos h_b_lower_bound_le_b
  -- We then derive `h_lt : (1 : ℝ) / (a * b) < ε` using `lt_of_le_of_lt h_rec_le h_at_bound_lt`, which states that if `1 / (a * b)` is less than or equal to `1 / (a * b_lower_bound)` and `1 / (a * b_lower_bound)` is less than `ε`, then `1 / (a * b)` is also less than `ε`.
  have h_lt : (1 : ℝ) / (a * b) < ε := by
    exact lt_of_le_of_lt h_rec_le h_at_bound_lt
  -- Finally, we derive `h_nonneg : 0 ≤ (1 : ℝ) / (a * b)` using `div_nonneg zero_le_one (le_of_lt h_prod_pos)`, which states that the reciprocal of a positive number is nonnegative.
  have h_nonneg : 0 ≤ (1 : ℝ) / (a * b) := by
    exact div_nonneg zero_le_one (le_of_lt h_prod_pos)
  -- We conclude that `0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε` by combining `h_nonneg` and `h_lt`. QED.
  exact ⟨h_nonneg, h_lt⟩

/-- Helper lemma: Given a lower bound on `b` that ensures the function value is less than `ε`, we can conclude that for any `b` greater than or equal to that lower bound, the distance from the function value to `0` is less than `ε`.
-/
private lemma tendsto_const_inv_mul_dist_lt_of_bound (a ε b_lower_bound b : ℝ) (h_a_pos : 0 < a) (h_b_lower_bound_pos : 0 < b_lower_bound) (h_b_lower_bound_le_b : b_lower_bound ≤ b) (h_at_bound_lt : (1 : ℝ) / (a * b_lower_bound) < ε) : dist ((1 : ℝ) / (a * b)) (0 : ℝ) < ε := by
  -- We first derive `h_nonneg_and_lt : 0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε` using the previous lemma `tendsto_const_inv_mul_nonneg_and_lt_of_bound a ε b_lower_bound b h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b h_at_bound_lt`, which states that for any `b` greater than or equal to the lower bound, the function value is nonnegative and less than `ε`.
  have h_nonneg_and_lt : 0 ≤ (1 : ℝ) / (a * b) ∧ (1 : ℝ) / (a * b) < ε :=
    tendsto_const_inv_mul_nonneg_and_lt_of_bound a ε b_lower_bound b
      h_a_pos h_b_lower_bound_pos h_b_lower_bound_le_b h_at_bound_lt
  -- We then apply `tendsto_const_inv_mul_nonneg_to_dist ((1 : ℝ) / (a * b)) ε h_nonneg_and_lt.left h_nonneg_and_lt.right` to conclude that the distance from the function value to `0` is less than `ε`, using the fact that if a value is nonnegative and less than `ε`, then its distance to `0` is also less than `ε`. QED.
  exact tendsto_const_inv_mul_nonneg_to_dist ((1 : ℝ) / (a * b)) ε h_nonneg_and_lt.left h_nonneg_and_lt.right

/-- Helper lemma: As `b` tends to infinity, the distance from the function value `1 / (a * b)` to `0` becomes less than any positive `ε` for sufficiently large `b`.
-/
private lemma tendsto_const_inv_mul_atTop_eventually_dist_lt (a : ℝ) (h_a_pos : 0 < a) (ε : ℝ) (h_ε_pos : 0 < ε) : ∀ᶠ b : ℝ≥0 in atTop, dist ((1 : ℝ) / (a * (b : ℝ))) (0 : ℝ) < ε := by
  -- We first construct a real number `B_real` defined as `(1 / (a * ε)) + 1`, which serves as a candidate lower bound for `b` to ensure that the function value is less than `ε`.
  let B_real : ℝ := (1 / (a * ε)) + 1
  -- We then derive `h_B_real_pos : 0 < B_real` using the previous lemma `tendsto_const_inv_mul_bound_pos a ε h_a_pos h_ε_pos`, which states that the constructed bound is positive.
  have h_B_real_pos : 0 < B_real := by
    exact tendsto_const_inv_mul_bound_pos a ε h_a_pos h_ε_pos
  -- We convert `B_real` to a nonnegative real number `B_nnreal` by taking the nonnegative part of `B_real`, ensuring that it is still positive.
  let B_nnreal : ℝ≥0 := ⟨B_real, le_of_lt h_B_real_pos⟩
  -- We derive `h_B_nnreal_pos : 0 < (B_nnreal : ℝ)` from `h_B_real_pos` by noting that the nonnegative part of a positive real number is also positive.
  have h_B_nnreal_pos : 0 < (B_nnreal : ℝ) := by simpa [B_nnreal] using h_B_real_pos
  -- We then refine the goal using `Filter.eventually_ge_atTop B_nnreal`, which states that eventually, all elements of the filter at infinity are greater than or equal to `B_nnreal`. The goal is now `⊢ ∀ (x : ℝ≥0), B_nnreal ≤ x → dist (1 / (a * ↑x)) 0 < ε`.
  refine (Filter.eventually_ge_atTop B_nnreal).mono ?_
  -- We introduce `b : ℝ≥0` and the hypothesis `h_B_nnreal_le_b : B_nnreal ≤ b` from the goal. The goal is now `⊢ dist (1 / (a * ↑b)) 0 < ε`.
  intro b h_B_nnreal_le_b
  -- We derive `h_atB_lt : (1 : ℝ) / (a * (B_nnreal : ℝ)) < ε` using the previous lemma `tendsto_const_inv_mul_at_bound_lt_epsilon a ε h_a_pos h_ε_pos`, which states that evaluating the function at the constructed bound yields a value less than `ε`.
  have h_atB_lt : (1 : ℝ) / (a * (B_nnreal : ℝ)) < ε := by
    exact tendsto_const_inv_mul_at_bound_lt_epsilon a ε h_a_pos h_ε_pos
  -- Finally, we apply `tendsto_const_inv_mul_dist_lt_of_bound a ε (B_nnreal : ℝ) (b : ℝ) h_a_pos h_B_nnreal_pos h_B_nnreal_le_b h_atB_lt` to conclude that the distance from the function value to `0` is less than `ε` for any `b` greater than or equal to the constructed bound. QED.
  exact tendsto_const_inv_mul_dist_lt_of_bound a ε (B_nnreal : ℝ) (b : ℝ) h_a_pos h_B_nnreal_pos h_B_nnreal_le_b h_atB_lt

/-- Helper lemma: As `b` tends to infinity, the function value `1 / (a * b)` tends to `0` in the sense of the metric space distance.
-/
private lemma tendsto_const_inv_mul_atTop (a : ℝ) (h_a_pos : 0 < a) : Tendsto (fun b : ℝ≥0 => (1 : ℝ) / (a * (b : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  -- We refine the goal using `Metric.tendsto_nhds.mpr`, which allows us to prove the convergence by showing that for every positive `ε`, the function values are eventually within `ε` of `0`. The new goal is now `⊢ ∀ ε > 0, ∀ᶠ (x : ℝ≥0) in atTop, dist (1 / (a * ↑x)) 0 < ε`.
  refine Metric.tendsto_nhds.mpr ?_
  -- We introduce `ε : ℝ` and the hypothesis `h_ε_pos : 0 < ε`. The goal is now `⊢ ∀ᶠ (x : ℝ≥0) in atTop, dist (1 / (a * ↑x)) 0 < ε`.
  intro ε h_ε_pos
  -- We apply the previous lemma `tendsto_const_inv_mul_atTop_eventually_dist_lt a h_a_pos ε h_ε_pos` to conclude that for sufficiently large `b`, the distance from the function value to `0` is less than `ε`. QED.
  exact tendsto_const_inv_mul_atTop_eventually_dist_lt a h_a_pos ε h_ε_pos

/-- Lemma: As the inverse temperature `β` tends to infinity, the real-valued representation of the temperature `ofβ β` tends to `0` in the sense of the metric space distance.
-/
lemma tendsto_toReal_ofβ_atTop : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  -- We apply the previous lemma `tendsto_const_inv_mul_atTop` with `a` set to `kB` and `h_a_pos` set to `kB_pos`, which states that as `b` tends to infinity, the function value `1 / (kB * b)` tends to `0`. Since `ofβ b` is defined as `1 / (kB * b)`, this directly implies the desired convergence. QED.
  exact tendsto_const_inv_mul_atTop kB kB_pos

/-- As β → ∞, T = ofβ β → 0+ in ℝ (within Ioi 0). -/
lemma tendsto_ofβ_atTop : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  have h_to0 := tendsto_toReal_ofβ_atTop
  have h_into : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ)) atTop (𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_principal.mpr (by simpa using Temperature.eventually_pos_ofβ)
  have : Tendsto (fun b : ℝ≥0 => (Temperature.ofβ b : ℝ))
      atTop ((nhds (0 : ℝ)) ⊓ 𝓟 (Set.Ioi (0 : ℝ))) :=
    tendsto_inf.mpr ⟨h_to0, h_into⟩
  simpa [nhdsWithin] using this

/-! ### Conversion to and from `ℝ≥0` -/

open Constants

/-- Simplification function: Build a temperature from a nonnegative real number.

- Input:
  - `t` of type `ℝ≥0`: The nonnegative real number representing the temperature.
- Output:
  - Result of type `Temperature`: The temperature constructed from the nonnegative real number.
-/
@[simp]
def ofNNReal (t : ℝ≥0) : Temperature := ⟨t⟩

/-- Simplification lemma: The `val` field of a temperature constructed from a nonnegative real number `t` is equal to `t`.

- Premises:
  - `t` of type `ℝ≥0`: The nonnegative real number used to construct the temperature.
- Conclusion:
  - The conclusion is `(ofNNReal t).val = t`: The `val` field of the temperature constructed from `t` is equal to `t`.
- Proof:
  - The proof is straightforward as it directly follows from the definition of `ofNNReal`.
  - We use `rfl` (reflexivity of equality) to conclude that both sides are equal. QED.
-/
@[simp]
lemma ofNNReal_val (t : ℝ≥0) : (ofNNReal t).val = t := by
  rfl

/-- Simplification lemma: Coercing a temperature constructed from a nonnegative real number `t` back to `ℝ≥0` returns `t`.

- Premises:
  - `t` of type `ℝ≥0`: The nonnegative real number used to construct the temperature.
- Conclusion:
  - The conclusion is `((ofNNReal t : Temperature) : ℝ≥0) = t`: Coercing the temperature back to `ℝ≥0` returns the original `t`.
- Proof:
  - The proof is straightforward as it directly follows from the definition of `ofNNReal` and the coercion.
  - We use `rfl` (reflexivity of equality) to conclude that both sides are equal. QED.
-/
@[simp]
lemma coe_ofNNReal_coe (t : ℝ≥0) : ((ofNNReal t : Temperature) : ℝ≥0) = t := by
  rfl

/-- Simplification lemma: Coercing a temperature constructed from a nonnegative real number `t` to `ℝ` returns `t`.

- Premises:
  - `t` of type `ℝ≥0`: The nonnegative real number used to construct the temperature.
- Conclusion:
  - The conclusion is `((ofNNReal t : Temperature) : ℝ) = t`: Coercing the temperature to `ℝ` returns the original `t`.
- Proof:
  - The proof is straightforward as it directly follows from the definition of `ofNNReal` and the coercion.
  - We use `rfl` (reflexivity of equality) to conclude that both sides are equal. QED.
-/
@[simp]
lemma coe_ofNNReal_real (t : ℝ≥0) : ((⟨t⟩ : Temperature) : ℝ) = t := by
  rfl

/-- Simplification function: Build a temperature from a real number, given a proof that it is nonnegative.

- Input:
  - `t` of type `ℝ`: The real number representing the temperature.
  - `h_zero_le_t` of type `0 ≤ t`: A proof that the real number is nonnegative.
- Output:
  - Result of type `Temperature`: The temperature constructed from the real number `t`.
-/
@[simp]
noncomputable def ofRealNonneg (t : ℝ) (h_zero_le_t : 0 ≤ t) : Temperature := ofNNReal ⟨t, h_zero_le_t⟩

/-- Simplification lemma: The `val` field of a temperature constructed from a nonnegative real number `t` is equal to `⟨t, h_zero_le_t⟩`.

- Premises:
  - `t` of type `ℝ` (implicit): The real number used to construct the temperature.
  - `h_zero_le_t` of type `0 ≤ t`: A proof that the real number is nonnegative.
- Conclusion:
  - The conclusion is `(ofRealNonneg t h_zero_le_t).val = ⟨t, h_zero_le_t⟩`: The `val` field of the temperature constructed from `t` is equal to `⟨t, h_zero_le_t⟩`.
- Proof:
  - The proof is straightforward as it directly follows from the definition of `ofRealNonneg`.
  - We use `rfl` (reflexivity of equality) to conclude that both sides are equal. QED.
-/
@[simp]
lemma ofRealNonneg_val {t : ℝ} (h_zero_le_t : 0 ≤ t) : (ofRealNonneg t h_zero_le_t).val = ⟨t, h_zero_le_t⟩ := by
  rfl

/-! ### Calculus relating T and β -/

open Set
open scoped ENNReal

/-- Map a real `t` to the inverse temperature `β` corresponding to the temperature `Real.toNNReal t`
(`max t 0`), returned as a real number. -/
noncomputable def βFromReal (t : ℝ) : ℝ :=
  ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ)

/-- Explicit closed-form for `β_fun_T t` when `t > 0`. -/
lemma β_fun_T_formula (t : ℝ) (ht : 0 < t) :
    βFromReal t = (1 :  ℝ) / (kB * t) := by
  have ht0 : (0 : ℝ) ≤ t := ht.le
  have : ((Temperature.ofNNReal (Real.toNNReal t)).β : ℝ) = (1 :  ℝ) / (kB * t) := by
    simp [Temperature.β, Temperature.ofNNReal, Temperature.toReal,
      Real.toNNReal_of_nonneg ht0, one_div, mul_comm]
  simpa [βFromReal] using this

/-- On `Ioi 0`, `β_fun_T t` equals `1 / (kB * t)`. -/
lemma β_fun_T_eq_on_Ioi :
    EqOn βFromReal (fun t : ℝ => (1 :  ℝ) / (kB * t)) (Set.Ioi 0) := by
  intro t ht
  exact β_fun_T_formula t ht

lemma deriv_β_wrt_T (T : Temperature) (hT_pos : 0 < T.val) :
    HasDerivWithinAt βFromReal (-1 / (kB * (T.val : ℝ)^2)) (Set.Ioi 0) (T.val : ℝ) := by
  let f : ℝ → ℝ := fun t => (1 :  ℝ) / (kB * t)
  have h_eq : EqOn βFromReal f (Set.Ioi 0) := β_fun_T_eq_on_Ioi
  have hTne : (T.val : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hf_def : f = fun t : ℝ => (kB)⁻¹ * t⁻¹ := by
    funext t
    by_cases ht : t = 0
    · simp [f, ht]
    · simp [f, one_div, *] at *
      ring
  have h_inv :
      HasDerivAt (fun t : ℝ => t⁻¹)
        (-((T.val : ℝ) ^ 2)⁻¹) (T.val : ℝ) := by
    simpa using (hasDerivAt_inv (x := (T.val : ℝ)) hTne)
  have h_deriv_aux :
      HasDerivAt (fun t : ℝ => (kB)⁻¹ * t⁻¹)
        ((kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹)) (T.val : ℝ) :=
    h_inv.const_mul ((kB)⁻¹)
  have h_pow_simp :
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹) = -1 / (kB * (T.val : ℝ)^2) := by
    calc
      (kB)⁻¹ * (-((T.val : ℝ) ^ 2)⁻¹)
          = -((kB)⁻¹ * ((T.val : ℝ) ^ 2)⁻¹) := by
            ring
      _ = -(1 / kB * (1 / (T.val : ℝ) ^ 2)) := by
            simp [one_div]
      _ = -1 / (kB * (T.val : ℝ) ^ 2) := by
        rw [one_div]
        field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc, kB_ne_zero, hTne]
  have h_deriv_f :
      HasDerivAt f (-1 / (kB * (T.val : ℝ)^2)) (T.val : ℝ) := by
    simpa [hf_def, h_pow_simp] using h_deriv_aux
  have h_mem : (T.val : ℝ) ∈ Set.Ioi (0 : ℝ) := hT_pos
  exact (h_deriv_f.hasDerivWithinAt).congr h_eq (h_eq h_mem)

/-- Chain rule for β(T) : d/dT F(β(T)) = F'(β(T)) * (-1 / (kB * T^2)), within `Ioi 0`. -/
lemma chain_rule_T_β {F : ℝ → ℝ} {F' : ℝ}
    (T : Temperature) (hT_pos : 0 < T.val)
    (hF_deriv : HasDerivWithinAt F F' (Set.Ioi 0) (T.β : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => F (βFromReal t))
      (F' * (-1 / (kB * (T.val : ℝ)^2))) (Set.Ioi 0) (T.val : ℝ) := by
  have hβ_deriv := deriv_β_wrt_T (T:=T) hT_pos
  have h_map : Set.MapsTo βFromReal (Set.Ioi 0) (Set.Ioi 0) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have : 0 < (1 :  ℝ) / (kB * t) := by
      have : 0 < kB * t := mul_pos kB_pos ht_pos
      exact one_div_pos.mpr this
    have h_eqt : βFromReal t = (1 :  ℝ) / (kB * t) := β_fun_T_eq_on_Ioi ht
    simpa [h_eqt] using this
  have h_β_at_T : βFromReal (T.val : ℝ) = (T.β : ℝ) := by
    have hTposR : 0 < (T.val : ℝ) := hT_pos
    have h_eqt := β_fun_T_eq_on_Ioi hTposR
    simpa [Temperature.β, Temperature.toReal] using h_eqt
  have hF_deriv' : HasDerivWithinAt F F' (Set.Ioi 0) (βFromReal (T.val : ℝ)) := by
    simpa [h_β_at_T] using hF_deriv
  have h_comp := hF_deriv'.comp (T.val : ℝ) hβ_deriv h_map
  simpa [mul_comm] using h_comp
end Temperature

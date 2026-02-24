/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Meta.TODO.Basic

/-!
# Regularity of the inverse temperature map

This file proves continuity and differentiability properties of
`Temperature.ofβ : ℝ≥0 → Temperature` on the open interval `(0, ∞)`.

## Main results

* `Temperature.ofβ_continuousOn` : `ofβ` is continuous on `(0, ∞)`.
* `Temperature.ofβ_differentiableOn` : `ofβ` is differentiable on `(0, ∞)`.
-/

open NNReal

namespace Temperature
open Constants
open Filter Topology

/-! ### Regularity of `ofβ` === TODO TIL THE END OF THE FILE -/

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

Continuity at a positive point for the real formula `(t : ℝ) ↦ (1 : ℝ) / (kB * t)`.
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
  -- We define `g : ℝ → ℝ` as `g (t : ℝ) := (1 : ℝ) / (kB * t)`.
  -- This is the same formula as `f`, but defined on `ℝ`.
  let g : ℝ → ℝ := fun (t : ℝ) => (1 : ℝ) / (kB * t)
  -- We define `h : ℝ≥0 → ℝ` as `h (b : ℝ≥0) := (b : ℝ)`.
  -- This is the coercion from `ℝ≥0` to `ℝ`.
  let h : ℝ≥0 → ℝ := fun (b : ℝ≥0) => (b : ℝ)
  -- We then prove that `f = g ∘ h` by simplifying both sides and showing they are equal.
  -- This is done by `rfl`, since both sides are definitionally equal.
  have f_eq_g_comp_h : f = (g ∘ h) := by
    rfl
  -- We then prove that `g` is continuous at `x : ℝ` using the previous lemma
  -- `ofβ_realExpr_continuousAt_real x h_x_pos`, resulting in the hypothesis `h_continuousAt_real`.
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
  refine DifferentiableOn.congr (f := fun (x : ℝ) => (1 : ℝ) / (kB * x)) ?_ ?_
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

end Temperature

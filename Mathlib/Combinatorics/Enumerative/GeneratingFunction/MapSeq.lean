/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Map
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.SeqEquation
public import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Closed form of the sequence GF over a (semi)ring / field

Casting the `listWeight` functional equation into a (semi)ring `R` (then a ring, then
a field) successively turns the `S = 1 + A·S` recurrence into `S = invOfUnit (1 - A) 1`
and finally `S = (1 - A)⁻¹`.

## Main results

* `genFunMap_listWeight_eq`: the functional equation over a semiring.
* `genFunMap_listWeight`: the closed form `invOfUnit (1 - A) 1` over any ring.
* `genFunMap_listWeight_inv`: the `(1 - A)⁻¹` form over a field.
-/

@[expose] public section

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

/-- The `listWeight` functional equation, base-changed into any (semi)ring `R`. -/
theorem genFunMap_listWeight_eq (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ)
    [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFunMap R (listWeight wt) = 1 + genFunMap R wt * genFunMap R (listWeight wt) := by
  simpa only [genFunMap, map_add, map_mul, map_one] using
    congrArg (MvPowerSeries.map (Nat.castRingHom R)) (genFun_listWeight wt h)

/-- The base-changed GF has zero constant term when no object has weight `0`. -/
private theorem constantCoeff_genFunMap_eq_zero (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ)
    (h : ∀ a, wt a ≠ 0) : MvPowerSeries.constantCoeff (genFunMap R wt) = 0 := by
  haveI : IsEmpty {a // wt a = (0 : σ →₀ ℕ)} := ⟨fun a => h a.1 a.2⟩
  have h0 := coeff_genFunMap R wt 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff, Nat.card_of_isEmpty, Nat.cast_zero] at h0

/-- The base-changed `1 - genFunMap R wt` has constant coefficient `1` when no object has
weight `0` — the unit-status witness used by the closed-form theorems below. -/
private theorem constantCoeff_one_sub_genFunMap (R : Type*) [Ring R] (wt : α → σ →₀ ℕ)
    (h : ∀ a, wt a ≠ 0) :
    MvPowerSeries.constantCoeff (1 - genFunMap R wt) = ((1 : Rˣ) : R) := by
  rw [map_sub, map_one, constantCoeff_genFunMap_eq_zero R wt h, sub_zero, Units.val_one]

/-- **The closed form of the sequence GF.** Over any ring `R`, `1 - genFunMap R wt` is a unit. -/
theorem genFunMap_listWeight (R : Type*) [Ring R] (wt : α → σ →₀ ℕ)
    [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFunMap R (listWeight wt) = MvPowerSeries.invOfUnit (1 - genFunMap R wt) 1 := by
  haveI := finiteFibers_listWeight wt h
  have hconst := constantCoeff_one_sub_genFunMap R wt h
  have hfe : (1 - genFunMap R wt) * genFunMap R (listWeight wt) = 1 := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact genFunMap_listWeight_eq R wt h
  calc genFunMap R (listWeight wt)
      = MvPowerSeries.invOfUnit (1 - genFunMap R wt) 1
          * ((1 - genFunMap R wt) * genFunMap R (listWeight wt)) := by
        rw [← mul_assoc, MvPowerSeries.invOfUnit_mul _ _ hconst, one_mul]
    _ = MvPowerSeries.invOfUnit (1 - genFunMap R wt) 1 * 1 := by rw [hfe]
    _ = MvPowerSeries.invOfUnit (1 - genFunMap R wt) 1 := mul_one _

/-- The sequence GF closed form in the usual `(1 - A)⁻¹` notation, over a field. -/
theorem genFunMap_listWeight_inv (K : Type*) [Field K] (wt : α → σ →₀ ℕ)
    [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFunMap K (listWeight wt) = (1 - genFunMap K wt)⁻¹ := by
  rw [genFunMap_listWeight K wt h,
    MvPowerSeries.invOfUnit_eq' _ _ (constantCoeff_one_sub_genFunMap K wt h)]

end Combinatorics

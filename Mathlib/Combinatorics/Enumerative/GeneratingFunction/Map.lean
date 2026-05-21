/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Atom
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Prod
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Sum

/-!
# Base change of the weighted GF into a (semi)ring

## Main definitions

* `genFunMap R wt`: the GF base-changed via `Nat.castRingHom R`.

## Main results

* `coeff_genFunMap`: coefficient extraction casts the fibre cardinality into `R`.
* `genFunMap_sum`, `genFunMap_prod`, `genFunMap_atomWeight_zero`: the basic
  identities transported under `MvPowerSeries.map`.
-/

@[expose] public section

universe u v w

namespace Combinatorics

variable {α : Type u} {β : Type v} {σ : Type w}

/-- The weighted GF base-changed into a (semi)ring `R`. -/
noncomputable def genFunMap (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ) :
    MvPowerSeries σ R :=
  MvPowerSeries.map (Nat.castRingHom R) (genFun wt)

/-- The `d`-coefficient of the base-changed GF is the fibre cardinality, cast into `R`. -/
@[simp]
theorem coeff_genFunMap (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (genFunMap R wt) = (Nat.card {a // wt a = d} : R) := by
  simp [genFunMap]

/-- The base-changed GF of a disjoint union is the sum of the base-changed GFs. -/
@[simp]
theorem genFunMap_sum (R : Type*) [Semiring R] {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFunMap R (Sum.elim wα wβ) = genFunMap R wα + genFunMap R wβ := by
  simp [genFunMap]

/-- The base-changed GF of a Cartesian product is the product of the base-changed GFs. -/
@[simp]
theorem genFunMap_prod (R : Type*) [Semiring R] {wα : α → σ →₀ ℕ}
    {wβ : β → σ →₀ ℕ} [FiniteFibers wα] [FiniteFibers wβ] :
    genFunMap R (prodWeight wα wβ) = genFunMap R wα * genFunMap R wβ := by
  simp [genFunMap]

/-- The base-changed GF of the neutral class (`atomWeight 0`) is `1`. -/
@[simp]
theorem genFunMap_atomWeight_zero (R : Type*) [Semiring R] :
    genFunMap R (atomWeight (0 : σ →₀ ℕ)) = 1 := by
  simp [genFunMap]

end Combinatorics

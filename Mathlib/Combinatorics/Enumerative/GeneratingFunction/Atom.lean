/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs

/-!
# The atomic class

A single object of weight `w`, carried by `PUnit`. Universe-polymorphic in the carrier
universe so that the sequence functional equation can combine it (at the empty-sequence
universe) with arbitrary-universe classes. `wepsilon = atomWeight 0`.

## Main definitions

* `atomWeight`: the constant weight `w` on `PUnit`.

## Main results

* `genFun_atomWeight`: the GF of the weight-`w` atom is the monomial `X^w`.
* `genFun_atomWeight_zero`: the GF of the neutral class is `1`.
-/

@[expose] public section

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

/-- The constant weight of the one-object atomic class, on `PUnit`. -/
def atomWeight (w : σ →₀ ℕ) : PUnit.{u + 1} → σ →₀ ℕ := fun _ => w

instance instFiniteFibersAtomWeight (w : σ →₀ ℕ) : FiniteFibers (atomWeight w) where
  finite_fiber _ := Finite.of_injective Subtype.val Subtype.val_injective

private theorem card_atomWeight_fiber [DecidableEq σ] (w d : σ →₀ ℕ) :
    Nat.card {_a : PUnit.{u + 1} // atomWeight w _a = d} = if d = w then 1 else 0 := by
  by_cases hd : d = w
  · subst hd
    have hall : ∀ _a : PUnit.{u + 1}, atomWeight d _a = d := fun _ => rfl
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv hall)]
    exact Nat.card_unique
  · rw [if_neg hd]
    haveI : IsEmpty {_a : PUnit.{u + 1} // atomWeight w _a = d} :=
      ⟨fun x => hd x.2.symm⟩
    exact Nat.card_of_isEmpty

/-- The weighted GF of the weight-`w` atom is the monomial `X^w`. -/
@[simp]
theorem genFun_atomWeight (w : σ →₀ ℕ) :
    genFun (atomWeight w) = MvPowerSeries.monomial w (1 : ℕ) := by
  classical
  ext d
  rw [coeff_genFun, card_atomWeight_fiber, MvPowerSeries.coeff_monomial]

/-- The weighted GF of the neutral class (`atomWeight 0`) is `1`. -/
@[simp]
theorem genFun_atomWeight_zero :
    genFun (atomWeight (0 : σ →₀ ℕ)) = (1 : MvPowerSeries σ ℕ) := by
  simp

end Combinatorics

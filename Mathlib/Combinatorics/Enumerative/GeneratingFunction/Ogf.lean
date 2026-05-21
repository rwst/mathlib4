/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Ordinary classes (the `σ = Unit` case)

`PowerSeries ℕ = MvPowerSeries Unit ℕ`, so an *ordinary* class — objects with an
`ℕ`-valued `size` — is the `σ = Unit` case, with weight monomial `single () (size a)`.
`FiniteFibers` specialises to `FiniteSizeFibers`; `genFun` to `ogf`.

## Main definitions

* `FiniteSizeFibers`: the ℕ-size analogue of `FiniteFibers`.
* `ogf`: the ordinary GF of a size function.

## Main results

* `instFiniteSizeFibersOfFinite`: a finite carrier has finite size-fibres.
* `instFiniteFibersSingleSize`: bridge from `FiniteSizeFibers` to `FiniteFibers`.
* `coeff_ogf`: coefficient extraction by size-fibre cardinality.
* `ogf_congr`: size-preserving isomorphic classes have equal OGF.
-/

@[expose] public section

universe u v

namespace Combinatorics

variable {α : Type u} {β : Type v}

/-- The `ℕ`-size analogue of `FiniteFibers`: only finitely many objects of each size. -/
class FiniteSizeFibers (size : α → ℕ) : Prop where
  finite_fiber (n : ℕ) : Finite {a // size a = n}

attribute [instance] FiniteSizeFibers.finite_fiber

/-- A class with a finite carrier has finite size-fibres. -/
instance instFiniteSizeFibersOfFinite [Finite α] (size : α → ℕ) : FiniteSizeFibers size :=
  ⟨fun _ => inferInstance⟩

instance instFiniteFibersSingleSize (size : α → ℕ) [FiniteSizeFibers size] :
    FiniteFibers (fun a => Finsupp.single () (size a)) where
  finite_fiber d := by
    have hiff (a : α) : size a = d () ↔ Finsupp.single () (size a) = d :=
      ⟨fun h => h ▸ (Finsupp.unique_single d).symm,
        fun h => by simpa using congrArg (· ()) h⟩
    haveI := FiniteSizeFibers.finite_fiber (size := size) (d ())
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight hiff)

/-- The ordinary generating function `A(X) = ∑ₙ |𝒜ₙ| Xⁿ` of an `ℕ`-valued size. -/
noncomputable def ogf (size : α → ℕ) : PowerSeries ℕ :=
  genFun (fun a => Finsupp.single () (size a))

@[simp]
theorem coeff_ogf (size : α → ℕ) (n : ℕ) :
    PowerSeries.coeff n (ogf size) = Nat.card {a // size a = n} := by
  rw [ogf, PowerSeries.coeff_def (s := Finsupp.single () n) Finsupp.single_eq_same,
    coeff_genFun]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => (Finsupp.single_injective ()).eq_iff)

/-- The OGF is an invariant of size-preserving isomorphism. -/
theorem ogf_congr {sα : α → ℕ} {sβ : β → ℕ} (e : α ≃ β) (he : ∀ a, sβ (e a) = sα a) :
    ogf sα = ogf sβ :=
  genFun_congr e fun a => by rw [he a]

end Combinatorics

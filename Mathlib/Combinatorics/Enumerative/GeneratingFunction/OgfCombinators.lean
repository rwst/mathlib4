/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Atom
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Ogf
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Prod
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Sum
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Tsum
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Combinators for the ordinary GF: sum, product, atom, tsum

The `σ = Unit` specialisations of `genFun_sum`, `genFun_prod`, `genFun_atomWeight`,
`genFun_eq_tsum`. The neutral and atomic ordinary classes match the conventional
`X^k` and `1`.

## Main results

* `ogf_sum`, `ogf_prod`: disjoint union and product specialisations.
* `ogf_atom`: `ogf (fun _ : PUnit => k) = X^k`.
* `ogf_eq_tsum`: the OGF is `∑' a, X^(size a)`.
-/

@[expose] public section

open PowerSeries

open scoped PowerSeries.WithPiTopology

universe u v

namespace Combinatorics

variable {α : Type u} {β : Type v}

/-- The OGF of a disjoint union is the sum of the OGFs. -/
@[simp]
theorem ogf_sum (sα : α → ℕ) (sβ : β → ℕ) [FiniteSizeFibers sα] [FiniteSizeFibers sβ] :
    ogf (Sum.elim sα sβ) = ogf sα + ogf sβ := by
  have hw : (fun x : α ⊕ β => Finsupp.single () (Sum.elim sα sβ x))
      = Sum.elim (fun a => Finsupp.single () (sα a))
          (fun b => Finsupp.single () (sβ b)) := by
    funext x; cases x <;> rfl
  simp only [ogf, hw, genFun_sum]

/-- The OGF of a Cartesian product (sizes added) is the product of the OGFs. -/
@[simp]
theorem ogf_prod (sα : α → ℕ) (sβ : β → ℕ) [FiniteSizeFibers sα] [FiniteSizeFibers sβ] :
    ogf (fun p : α × β => sα p.1 + sβ p.2) = ogf sα * ogf sβ := by
  have hw : (fun p : α × β => Finsupp.single () (sα p.1 + sβ p.2))
      = prodWeight (fun a => Finsupp.single () (sα a))
          (fun b => Finsupp.single () (sβ b)) := by
    funext p; simp [prodWeight, Finsupp.single_add]
  simp only [ogf, hw, genFun_prod]

/-- The OGF of the size-`k` atom (one object of size `k`, carried by `PUnit`) is `X^k`. -/
@[simp]
theorem ogf_atom (k : ℕ) :
    ogf (fun _ : PUnit.{u + 1} => k) = (PowerSeries.X : PowerSeries ℕ) ^ k :=
  (genFun_atomWeight (Finsupp.single () k)).trans (MvPowerSeries.X_pow_eq () k).symm

/-- The OGF is the sum of the size monomials `X^(size a)` over all objects — the
Flajolet–Sedgewick *defining* form. -/
theorem ogf_eq_tsum (size : α → ℕ) [FiniteSizeFibers size] :
    ogf size = ∑' a, (PowerSeries.X : PowerSeries ℕ) ^ size a := by
  refine (HasSum.tsum_eq ?_).symm
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [PowerSeries.coeff_X_pow, coeff_ogf]
  exact hasSum_count size d

end Combinatorics

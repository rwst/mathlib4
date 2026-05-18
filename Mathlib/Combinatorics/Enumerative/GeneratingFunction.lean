/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Finite.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Ordinary generating functions of combinatorial classes

A *combinatorial class* is a type together with a `size : carrier → ℕ` function whose fibers
(the objects of each given size) are finite. Its *ordinary generating function* (OGF) is the
formal power series `A(X) = ∑ₙ |𝒜ₙ| Xⁿ`, where `𝒜ₙ` is the set of objects of size `n`.

This file sets up the structure and proves the two basic *admissible constructions* of the
symbolic method (Flajolet–Sedgewick, *Analytic Combinatorics*):

* `CombinatorialClass.sum` (disjoint union) has OGF `A + B`;
* `CombinatorialClass.prod` (Cartesian product with additive size) has OGF `A * B`.

## Main definitions

* `CombinatorialClass`: a type with a size function and finite fibers.
* `CombinatorialClass.ogf`: its ordinary generating function in `PowerSeries ℕ`.
* `CombinatorialClass.sum`, `CombinatorialClass.prod`: the union and product constructions.

## Main results

* `CombinatorialClass.ogf_congr`: size-preserving isomorphic classes have equal OGF.
* `CombinatorialClass.ogf_sum`: `(𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf`.
* `CombinatorialClass.ogf_prod`: `(𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf`.

## TODO

* The sequence construction `SEQ` (OGF `(1 - A)⁻¹`), tying into `PowerSeries.Inverse`.
* Labelled classes and exponential generating functions.
* Refactor `PowerSeries.catalanSeries`, `PowerSeries.largeSchroderSeries`,
  `Nat.Partition.genFun` onto this framework.

## References

* [M. Bona, *Handbook of Enumerative Combinatorics*][Bona2015]
* [P. Flajolet and R. Sedgewick, *Analytic Combinatorics*][flajolet2009]
-/

@[expose] public section

open Finset PowerSeries

universe u

/-- A combinatorial class: a type `carrier` equipped with a `size` function whose fibers
(the objects of each fixed size) are finite. -/
structure CombinatorialClass where
  /-- The type of objects of the class. -/
  carrier : Type u
  /-- The size of an object. -/
  size : carrier → ℕ
  /-- There are only finitely many objects of any given size. -/
  finite_fiber (n : ℕ) : Finite {a : carrier // size a = n}

namespace CombinatorialClass

variable (𝒜 ℬ : CombinatorialClass)

/-- The type of objects of size `n`. -/
abbrev Fiber (n : ℕ) : Type _ := {a : 𝒜.carrier // 𝒜.size a = n}

instance instFiniteFiber (n : ℕ) : Finite (𝒜.Fiber n) := 𝒜.finite_fiber n

/-- The number of objects of size `n`. -/
noncomputable def card (n : ℕ) : ℕ := Nat.card (𝒜.Fiber n)

/-- The ordinary generating function `A(X) = ∑ₙ |𝒜ₙ| Xⁿ`. -/
noncomputable def ogf : PowerSeries ℕ := PowerSeries.mk 𝒜.card

@[simp]
theorem coeff_ogf (n : ℕ) : coeff n 𝒜.ogf = 𝒜.card n := by
  simp only [ogf, coeff_mk]

/-! ### Isomorphism invariance -/

/-- The OGF is an invariant of size-preserving isomorphism: two combinatorial classes
related by a size-preserving bijection have the same ordinary generating function. -/
theorem ogf_congr (e : 𝒜.carrier ≃ ℬ.carrier) (he : ∀ a, ℬ.size (e a) = 𝒜.size a) :
    𝒜.ogf = ℬ.ogf := by
  ext n
  rw [coeff_ogf, coeff_ogf]
  have key : 𝒜.Fiber n ≃ ℬ.Fiber n := Equiv.subtypeEquiv e fun a => by rw [he a]
  exact Nat.card_congr key

/-! ### Disjoint union -/

/-- The fiber of a disjoint union splits as the disjoint union of the fibers. -/
def sumFiberEquiv (n : ℕ) :
    {x : 𝒜.carrier ⊕ ℬ.carrier // Sum.elim 𝒜.size ℬ.size x = n} ≃ 𝒜.Fiber n ⊕ ℬ.Fiber n :=
  Equiv.subtypeSum

/-- The disjoint union of two combinatorial classes: objects are objects of `𝒜` or of `ℬ`,
with the same size. -/
def sum : CombinatorialClass where
  carrier := 𝒜.carrier ⊕ ℬ.carrier
  size := Sum.elim 𝒜.size ℬ.size
  finite_fiber n := Finite.of_equiv _ (𝒜.sumFiberEquiv ℬ n).symm

@[simp]
theorem sum_card (n : ℕ) : (𝒜.sum ℬ).card n = 𝒜.card n + ℬ.card n :=
  (Nat.card_congr (𝒜.sumFiberEquiv ℬ n)).trans Nat.card_sum

/-- The OGF of a disjoint union is the sum of the OGFs. -/
@[simp]
theorem ogf_sum : (𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf := by
  ext n
  simp [sum_card]

/-! ### Cartesian product -/

/-- The fiber of a product, at a fixed pair of component sizes, is the product of the fibers. -/
def prodPairEquiv (c : ℕ × ℕ) :
    {p : 𝒜.carrier × ℬ.carrier // (𝒜.size p.1, ℬ.size p.2) = c} ≃ 𝒜.Fiber c.1 × ℬ.Fiber c.2 where
  toFun := fun ⟨⟨a, b⟩, h⟩ => (⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩)
  invFun := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨(a, b), Prod.ext ha hb⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

instance instFiniteProdPair (c : ℕ × ℕ) :
    Finite {p : 𝒜.carrier × ℬ.carrier // (𝒜.size p.1, ℬ.size p.2) = c} :=
  Finite.of_equiv _ (𝒜.prodPairEquiv ℬ c).symm

/-- The fiber of a Cartesian product splits, over the antidiagonal, into the pair-fibers. -/
def prodFiberEquiv (n : ℕ) :
    {p : 𝒜.carrier × ℬ.carrier // 𝒜.size p.1 + ℬ.size p.2 = n} ≃
      Σ y : antidiagonal n,
        {p : 𝒜.carrier × ℬ.carrier // (𝒜.size p.1, ℬ.size p.2) = (y : ℕ × ℕ)} :=
  (Equiv.subtypeEquivRight fun _ => by simp [Finset.mem_antidiagonal]).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun p : 𝒜.carrier × ℬ.carrier => (𝒜.size p.1, ℬ.size p.2)) fun _ => Iff.rfl).symm

/-- The Cartesian product of two combinatorial classes: objects are pairs, with size the
sum of the component sizes. -/
def prod : CombinatorialClass where
  carrier := 𝒜.carrier × ℬ.carrier
  size p := 𝒜.size p.1 + ℬ.size p.2
  finite_fiber n := Finite.of_equiv _ (𝒜.prodFiberEquiv ℬ n).symm

@[simp]
theorem prod_card (n : ℕ) :
    (𝒜.prod ℬ).card n = ∑ p ∈ antidiagonal n, 𝒜.card p.1 * ℬ.card p.2 := by
  have h1 : (𝒜.prod ℬ).card n = Nat.card (Σ y : antidiagonal n,
      {p : 𝒜.carrier × ℬ.carrier // (𝒜.size p.1, ℬ.size p.2) = (y : ℕ × ℕ)}) :=
    Nat.card_congr (𝒜.prodFiberEquiv ℬ n)
  rw [h1, Nat.card_sigma,
    ← Finset.sum_coe_sort (antidiagonal n) fun p => 𝒜.card p.1 * ℬ.card p.2]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.card_congr (𝒜.prodPairEquiv ℬ _), Nat.card_prod]
  rfl

/-- The OGF of a Cartesian product is the product of the OGFs. -/
@[simp]
theorem ogf_prod : (𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf := by
  ext n
  simp [prod_card, coeff_mul]

end CombinatorialClass

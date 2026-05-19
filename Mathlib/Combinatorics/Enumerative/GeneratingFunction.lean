/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
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
* `CombinatorialClass.epsilon`: the neutral class (a single object of size `0`).
* `CombinatorialClass.seq`: the sequence construction (finite sequences of objects).
* `CombinatorialClass.ogfMap`: the OGF base-changed into an arbitrary (semi)ring `R`.

## Main results

* `CombinatorialClass.ogf_congr`: size-preserving isomorphic classes have equal OGF.
* `CombinatorialClass.ogf_sum`: `(𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf`.
* `CombinatorialClass.ogf_prod`: `(𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf`.
* `CombinatorialClass.ogf_epsilon`: `epsilon.ogf = 1`.
* `CombinatorialClass.ogf_seq`: `(𝒜.seq h).ogf = 1 + 𝒜.ogf * (𝒜.seq h).ogf`, the
  functional equation of the sequence construction.
* `CombinatorialClass.ogfMap_seq`: over a field `K`, the closed form
  `(𝒜.seq h).ogfMap K = (1 - 𝒜.ogfMap K)⁻¹` (`PowerSeries.Inverse`).

## TODO

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

variable (𝒜 ℬ : CombinatorialClass.{u})

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

/-! ### Neutral class -/

/-- The neutral class `ε`: a single object of size `0`. It is the unit for `prod` and
the base case of `seq`; its OGF is `1`. -/
def epsilon : CombinatorialClass.{u} where
  carrier := PUnit.{u + 1}
  size _ := 0
  finite_fiber _ := Finite.of_injective Subtype.val Subtype.val_injective

theorem epsilon_card (n : ℕ) : epsilon.card n = if n = 0 then 1 else 0 := by
  have hc : epsilon.card n = Nat.card {_u : PUnit // (0 : ℕ) = n} := rfl
  rw [hc]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ : PUnit => rfl)]
    exact Nat.card_unique
  · rw [if_neg hn]
    haveI : IsEmpty {_u : PUnit // (0 : ℕ) = n} := ⟨fun x => hn x.2.symm⟩
    exact Nat.card_of_isEmpty

/-- The OGF of the neutral class is `1`. -/
@[simp]
theorem ogf_epsilon : epsilon.ogf = (1 : PowerSeries ℕ) := by
  ext n
  rw [coeff_ogf, epsilon_card, coeff_one]

/-! ### Sequence -/

/-- When no object has size `0`, the length of a sequence is at most its total size
(every entry contributes at least `1`). -/
theorem length_le_sum_map (h : ∀ a, 𝒜.size a ≠ 0) (l : List 𝒜.carrier) :
    l.length ≤ (l.map 𝒜.size).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have : 1 ≤ 𝒜.size a := Nat.one_le_iff_ne_zero.mpr (h a)
      omega

/-- Fibers of the sequence construction are finite: a size-`n` sequence has length
`≤ n` and all of its entries lie among the (finitely many) objects of size `≤ n`. -/
theorem finite_seq_fiber (h : ∀ a, 𝒜.size a ≠ 0) (n : ℕ) :
    Finite {l : List 𝒜.carrier // (l.map 𝒜.size).sum = n} := by
  haveI : Finite {a : 𝒜.carrier // 𝒜.size a ≤ n} :=
    (Set.Finite.preimage' (Set.finite_Iic n)
      (fun b _ => Set.finite_coe_iff.mp (𝒜.finite_fiber b))).to_subtype
  haveI : Finite {m : List {a : 𝒜.carrier // 𝒜.size a ≤ n} // m.length ≤ n} :=
    (List.finite_length_le {a : 𝒜.carrier // 𝒜.size a ≤ n} n).to_subtype
  have hmem : ∀ {l : List 𝒜.carrier}, (l.map 𝒜.size).sum = n → ∀ a ∈ l, 𝒜.size a ≤ n :=
    fun {l} hl a ha =>
      le_of_le_of_eq (List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)) hl
  refine Finite.of_injective
    (fun l : {l : List 𝒜.carrier // (l.map 𝒜.size).sum = n} =>
      (⟨l.1.attachWith (fun a => 𝒜.size a ≤ n) (hmem l.2), by
          rw [List.length_attachWith]
          exact le_of_le_of_eq (𝒜.length_le_sum_map h l.1) l.2⟩ :
        {m : List {a : 𝒜.carrier // 𝒜.size a ≤ n} // m.length ≤ n})) ?_
  intro x y hxy
  apply Subtype.ext
  have h2 := congrArg (List.map Subtype.val) (congrArg Subtype.val hxy)
  rwa [List.attachWith_map_subtype_val, List.attachWith_map_subtype_val] at h2

/-- The fixed-point (cons) decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)`: a sequence is
empty, or a first object followed by a sequence. -/
def seqDecomp : List 𝒜.carrier ≃ epsilon.carrier ⊕ 𝒜.carrier × List 𝒜.carrier where
  toFun
    | [] => Sum.inl ⟨⟩
    | a :: l => Sum.inr (a, l)
  invFun
    | Sum.inl _ => []
    | Sum.inr (a, l) => a :: l
  left_inv := by rintro (_ | ⟨a, l⟩) <;> rfl
  right_inv := by rintro (⟨⟩ | ⟨a, l⟩) <;> rfl

/-- The sequence construction `SEQ(𝒜)`: finite sequences of objects of `𝒜` (which must
have no object of size `0`), with size the sum of the component sizes. -/
def seq (h : ∀ a, 𝒜.size a ≠ 0) : CombinatorialClass where
  carrier := List 𝒜.carrier
  size l := (l.map 𝒜.size).sum
  finite_fiber n := 𝒜.finite_seq_fiber h n

/-- **The OGF functional equation of the sequence construction.** It is read off the
cons decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)` through `ogf_congr`, `ogf_sum`, `ogf_prod`.
Over a base ring with subtraction this is the closed form `(SEQ 𝒜).ogf = (1 - 𝒜.ogf)⁻¹`
(`PowerSeries.Inverse`); over `ℕ` the functional equation is the available form. -/
theorem ogf_seq (h : ∀ a, 𝒜.size a ≠ 0) :
    (𝒜.seq h).ogf = 1 + 𝒜.ogf * (𝒜.seq h).ogf := by
  have hcongr : (𝒜.seq h).ogf = (epsilon.sum (𝒜.prod (𝒜.seq h))).ogf :=
    ogf_congr (𝒜 := 𝒜.seq h) (ℬ := epsilon.sum (𝒜.prod (𝒜.seq h)))
      𝒜.seqDecomp (by rintro (_ | ⟨a, l⟩) <;> rfl)
  nth_rewrite 1 [hcongr]
  rw [ogf_sum, ogf_prod, ogf_epsilon]

/-! ### Base change and closed forms

The combinatorial OGF lives in `PowerSeries ℕ` (coefficients *are* the counts). Casting
it into a ring — in particular a field — makes subtraction and inverses available, which
is what turns the `seq` functional equation into the closed form `(1 - A)⁻¹`. -/

/-- The OGF base-changed into a (semi)ring `R`: `𝒜.ogfMap R = ∑ₙ (|𝒜ₙ| : R) Xⁿ`,
the image of `𝒜.ogf` under `ℕ → R`. -/
noncomputable def ogfMap (R : Type*) [Semiring R] : PowerSeries R :=
  PowerSeries.map (Nat.castRingHom R) 𝒜.ogf

@[simp]
theorem coeff_ogfMap (R : Type*) [Semiring R] (n : ℕ) :
    coeff n (𝒜.ogfMap R) = (𝒜.card n : R) := by
  rw [ogfMap, PowerSeries.coeff_map, coeff_ogf, Nat.coe_castRingHom]

@[simp]
theorem ogfMap_sum (R : Type*) [Semiring R] :
    (𝒜.sum ℬ).ogfMap R = 𝒜.ogfMap R + ℬ.ogfMap R := by
  simp only [ogfMap, ogf_sum, map_add]

@[simp]
theorem ogfMap_prod (R : Type*) [Semiring R] :
    (𝒜.prod ℬ).ogfMap R = 𝒜.ogfMap R * ℬ.ogfMap R := by
  simp only [ogfMap, ogf_prod, map_mul]

@[simp]
theorem ogfMap_epsilon (R : Type*) [Semiring R] : epsilon.ogfMap R = 1 := by
  simp only [ogfMap, ogf_epsilon, map_one]

/-- The `seq` functional equation, base-changed into any (semi)ring `R`. -/
theorem ogfMap_seq_eq (R : Type*) [Semiring R] (h : ∀ a, 𝒜.size a ≠ 0) :
    (𝒜.seq h).ogfMap R = 1 + 𝒜.ogfMap R * (𝒜.seq h).ogfMap R := by
  have e := congrArg (PowerSeries.map (Nat.castRingHom R)) (𝒜.ogf_seq h)
  simpa only [ogfMap, map_add, map_mul, map_one] using e

/-- **The closed form of the sequence OGF.** Over a field `K`, base-changing the
counts makes `1 - 𝒜.ogfMap K` invertible (its constant term is `1`, since `seq`
forbids size-`0` objects), and the `seq` functional equation pins the sequence OGF to
`(1 - 𝒜.ogfMap K)⁻¹`. This is the closed form of the symbolic method's `SEQ`. -/
theorem ogfMap_seq (K : Type*) [Field K] (h : ∀ a, 𝒜.size a ≠ 0) :
    (𝒜.seq h).ogfMap K = (1 - 𝒜.ogfMap K)⁻¹ := by
  have hcard0 : 𝒜.card 0 = 0 := by
    haveI : IsEmpty (𝒜.Fiber 0) := ⟨fun a => h a.1 a.2⟩
    exact Nat.card_of_isEmpty
  have hA0 : PowerSeries.constantCoeff (𝒜.ogfMap K) = 0 := by
    have h0 := 𝒜.coeff_ogfMap K 0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff, hcard0, Nat.cast_zero] at h0
  have hconst : PowerSeries.constantCoeff (1 - 𝒜.ogfMap K) ≠ 0 := by
    rw [map_sub, map_one, hA0, sub_zero]
    exact one_ne_zero
  have hfe : (1 - 𝒜.ogfMap K) * (𝒜.seq h).ogfMap K = 1 := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact 𝒜.ogfMap_seq_eq K h
  calc (𝒜.seq h).ogfMap K
      = (1 - 𝒜.ogfMap K)⁻¹ * ((1 - 𝒜.ogfMap K) * (𝒜.seq h).ogfMap K) := by
        rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hconst, one_mul]
    _ = (1 - 𝒜.ogfMap K)⁻¹ * 1 := by rw [hfe]
    _ = (1 - 𝒜.ogfMap K)⁻¹ := mul_one _

end CombinatorialClass

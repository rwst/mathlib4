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
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
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

It also provides the multivariate generalisation `WeightedClass`, where objects carry a
*monomial weight* `σ →₀ ℕ` instead of an `ℕ` size and the generating function lives in
`MvPowerSeries σ ℕ`. Since `PowerSeries R = MvPowerSeries Unit R`, the `σ = Unit` case is
exactly the ordinary theory above; weighting tracks refined statistics (e.g. bivariate
marking) at no extra structural cost — `sum`, `prod`, `seq` and the closed form all carry
over.

## Main definitions

* `CombinatorialClass`: a type with a size function and finite fibers.
* `CombinatorialClass.ogf`: its ordinary generating function in `PowerSeries ℕ`.
* `CombinatorialClass.sum`, `CombinatorialClass.prod`: the union and product constructions.
* `CombinatorialClass.epsilon`: the neutral class (a single object of size `0`).
* `CombinatorialClass.seq`: the sequence construction (finite sequences of objects).
* `CombinatorialClass.ogfMap`: the OGF base-changed into an arbitrary (semi)ring `R`.
* `WeightedClass`: a type with a monomial-valued `weight : carrier → (σ →₀ ℕ)` and finite
  fibers; the multivariate generalisation of `CombinatorialClass` (`σ = Unit` recovers it).
* `WeightedClass.wgf`: its weighted generating function in `MvPowerSeries σ ℕ`.
* `WeightedClass.sum`, `WeightedClass.prod`, `WeightedClass.wepsilon`, `WeightedClass.seq`:
  the weighted admissible constructions.
* `WeightedClass.wgfMap`: the weighted GF base-changed into an arbitrary (semi)ring `R`.

## Main results

* `CombinatorialClass.ogf_congr`: size-preserving isomorphic classes have equal OGF.
* `CombinatorialClass.ogf_sum`: `(𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf`.
* `CombinatorialClass.ogf_prod`: `(𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf`.
* `CombinatorialClass.ogf_epsilon`: `epsilon.ogf = 1`.
* `CombinatorialClass.ogf_seq`: `(𝒜.seq h).ogf = 1 + 𝒜.ogf * (𝒜.seq h).ogf`, the
  functional equation of the sequence construction.
* `CombinatorialClass.ogfMap_seq`: over a field `K`, the closed form
  `(𝒜.seq h).ogfMap K = (1 - 𝒜.ogfMap K)⁻¹` (`PowerSeries.Inverse`).
* `WeightedClass.wgf_sum`, `WeightedClass.wgf_prod`, `WeightedClass.wgf_wepsilon`: the
  weighted analogues of the admissible-construction generating-function identities.
* `WeightedClass.wgf_seq`: `(𝒜.seq h).wgf = 1 + 𝒜.wgf * (𝒜.seq h).wgf`, the weighted
  sequence functional equation.
* `WeightedClass.wgfMap_seq`: over a field `K`, the multivariate closed form
  `(𝒜.seq h).wgfMap K = (1 - 𝒜.wgfMap K)⁻¹` (`MvPowerSeries.Inverse`).

## TODO

* Labelled classes and exponential generating functions.
* Refactor `PowerSeries.catalanSeries`, `PowerSeries.largeSchroderSeries`,
  `Nat.Partition.genFun` onto this framework.
* A `WeightedClass Unit ≃ CombinatorialClass` bridge, a `mark` primitive (introducing a
  fresh statistic variable), and the OGF-from-BGF grading-reindex specialisation.

## References

* [M. Bona, *Handbook of Enumerative Combinatorics*][Bona2015]
* [P. Flajolet and R. Sedgewick, *Analytic Combinatorics*][flajolet2009]
-/

@[expose] public section

open Finset PowerSeries

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

universe u v

/-- A finitely-fibred indicator sums (in the discrete topology on `ℕ`) to the cardinality
of the fibre: `∑_{a} [g a = d] = #{a : g a = d}`. This is the convergence engine behind
the “generating function = sum over elements” identities — the finiteness of the fibre
is exactly the summability hypothesis. -/
private theorem hasSum_count {α β : Type*} [DecidableEq β] (g : α → β) (d : β)
    [Finite {a : α // g a = d}] :
    HasSum (fun a : α => if d = g a then (1 : ℕ) else 0) (Nat.card {a : α // g a = d}) := by
  classical
  have hfinst : Finite {a : α | g a = d} := ‹Finite {a : α // g a = d}›
  have hfin : {a : α | g a = d}.Finite := Set.toFinite _
  have hsum : (∑ b ∈ hfin.toFinset, if d = g b then (1 : ℕ) else 0)
      = Nat.card {a : α // g a = d} := by
    have hone (b) (hb : b ∈ hfin.toFinset) : (if d = g b then (1 : ℕ) else 0) = 1 := by
      rw [Set.Finite.mem_toFinset] at hb
      rw [if_pos hb.symm]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
      ← Nat.card_eq_card_finite_toFinset hfin]
    rfl
  rw [← hsum]
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  rw [Set.Finite.mem_toFinset] at hb
  simp only [Set.mem_setOf_eq] at hb
  rw [if_neg]
  exact fun h => hb h.symm

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

/-! ### The generating function as a sum over elements -/

/-- **The OGF is the sum of `X^(size a)` over all objects.** This is the
Flajolet–Sedgewick *defining* form `A(X) = ∑_{a ∈ 𝒜} X^|a|`; the family is summable in
the coefficientwise (discrete) topology on `PowerSeries ℕ` precisely because every fibre
is finite (`finite_fiber`). It recovers the coefficient definition `ogf = mk card`. -/
theorem ogf_eq_tsum : 𝒜.ogf = ∑' a : 𝒜.carrier, (X : PowerSeries ℕ) ^ 𝒜.size a := by
  refine (HasSum.tsum_eq ?_).symm
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [coeff_X_pow, coeff_ogf]
  exact hasSum_count 𝒜.size d

end CombinatorialClass

/-! ## Weighted (multivariate) generating functions

Generalising `size : carrier → ℕ` to a *monomial-valued weight*
`weight : carrier → (σ →₀ ℕ)` yields multivariate generating functions in
`MvPowerSeries σ ℕ`: the coefficient of the monomial `X^d` counts the objects of
weight exactly `d`. Since `PowerSeries R = MvPowerSeries Unit R`, the `σ = Unit` case
is exactly the ordinary generating function above. The single ℕ size survives as the
total degree `deg`, which drives every finiteness argument. -/

/-- A *weighted combinatorial class*: a type `carrier` equipped with a monomial-valued
`weight` (an exponent vector `σ →₀ ℕ`) whose fibers — the objects of each fixed weight —
are finite. The `σ = Unit` case is an ordinary `CombinatorialClass`. -/
structure WeightedClass (σ : Type*) where
  /-- The type of objects of the class. -/
  carrier : Type u
  /-- The weight of an object, as a monomial exponent vector. -/
  weight : carrier → (σ →₀ ℕ)
  /-- There are only finitely many objects of any given weight. -/
  finite_fiber (d : σ →₀ ℕ) : Finite {a : carrier // weight a = d}

namespace WeightedClass

variable {σ : Type v} (𝒜 ℬ : WeightedClass.{u, v} σ)

/-- The type of objects of weight `d`. -/
abbrev WFiber (d : σ →₀ ℕ) : Type _ := {a : 𝒜.carrier // 𝒜.weight a = d}

instance instFiniteWFiber (d : σ →₀ ℕ) : Finite (𝒜.WFiber d) := 𝒜.finite_fiber d

/-- The number of objects of weight `d`. -/
noncomputable def wcard (d : σ →₀ ℕ) : ℕ := Nat.card (𝒜.WFiber d)

/-- The weighted ordinary generating function `A(X) = ∑_{a ∈ 𝒜} X^(weight a)`,
equivalently `∑_d |𝒜_d| X^d`, in `MvPowerSeries σ ℕ`. -/
noncomputable def wgf : MvPowerSeries σ ℕ := fun d => 𝒜.wcard d

@[simp]
theorem coeff_wgf (d : σ →₀ ℕ) : MvPowerSeries.coeff d 𝒜.wgf = 𝒜.wcard d :=
  MvPowerSeries.coeff_apply 𝒜.wgf d

/-- The weighted OGF is an invariant of weight-preserving isomorphism: two weighted
classes related by a weight-preserving bijection have the same weighted OGF. -/
theorem wgf_congr (e : 𝒜.carrier ≃ ℬ.carrier) (he : ∀ a, ℬ.weight (e a) = 𝒜.weight a) :
    𝒜.wgf = ℬ.wgf := by
  ext d
  rw [coeff_wgf, coeff_wgf]
  exact Nat.card_congr (Equiv.subtypeEquiv e fun a => by rw [he a])

/-- The total degree of an object: the sum of the exponents of its weight monomial.
This is the ℕ-valued “size” that drives all finiteness arguments. -/
def deg (a : 𝒜.carrier) : ℕ := (𝒜.weight a).sum fun _ n => n

theorem deg_eq_zero_iff (a : 𝒜.carrier) : 𝒜.deg a = 0 ↔ 𝒜.weight a = 0 := by
  rw [deg, Finsupp.sum, Finset.sum_eq_zero_iff, Finsupp.ext_iff]
  simp [Finsupp.mem_support_iff]

/-! ### Weighted disjoint union -/

/-- The fiber of a weighted disjoint union splits as the disjoint union of the fibers. -/
def wsumFiberEquiv (d : σ →₀ ℕ) :
    {x : 𝒜.carrier ⊕ ℬ.carrier // Sum.elim 𝒜.weight ℬ.weight x = d} ≃
      𝒜.WFiber d ⊕ ℬ.WFiber d :=
  Equiv.subtypeSum

/-- The disjoint union of two weighted classes: objects of `𝒜` or of `ℬ`, same weight. -/
def sum : WeightedClass σ where
  carrier := 𝒜.carrier ⊕ ℬ.carrier
  weight := Sum.elim 𝒜.weight ℬ.weight
  finite_fiber d := Finite.of_equiv _ (𝒜.wsumFiberEquiv ℬ d).symm

@[simp]
theorem sum_wcard (d : σ →₀ ℕ) : (𝒜.sum ℬ).wcard d = 𝒜.wcard d + ℬ.wcard d :=
  (Nat.card_congr (𝒜.wsumFiberEquiv ℬ d)).trans Nat.card_sum

/-- The weighted OGF of a disjoint union is the sum of the weighted OGFs. -/
@[simp]
theorem wgf_sum : (𝒜.sum ℬ).wgf = 𝒜.wgf + ℬ.wgf := by
  ext d
  simp [sum_wcard]

/-! ### Weighted Cartesian product -/

/-- The fiber of a product, at a fixed pair of component weights, is the product
of the fibers. -/
def wprodPairEquiv (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    {p : 𝒜.carrier × ℬ.carrier // (𝒜.weight p.1, ℬ.weight p.2) = c} ≃
      𝒜.WFiber c.1 × ℬ.WFiber c.2 where
  toFun := fun ⟨⟨a, b⟩, h⟩ => (⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩)
  invFun := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨(a, b), Prod.ext ha hb⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

instance instFiniteWProdPair (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    Finite {p : 𝒜.carrier × ℬ.carrier // (𝒜.weight p.1, ℬ.weight p.2) = c} :=
  Finite.of_equiv _ (𝒜.wprodPairEquiv ℬ c).symm

/-- The fiber of a product splits, over the antidiagonal, into the pair-fibers. -/
noncomputable def wprodFiberEquiv [DecidableEq σ] (d : σ →₀ ℕ) :
    {p : 𝒜.carrier × ℬ.carrier // 𝒜.weight p.1 + ℬ.weight p.2 = d} ≃
      Σ y : antidiagonal d,
        {p : 𝒜.carrier × ℬ.carrier //
          (𝒜.weight p.1, ℬ.weight p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))} :=
  (Equiv.subtypeEquivRight fun _ => by simp [Finset.mem_antidiagonal]).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun p : 𝒜.carrier × ℬ.carrier => (𝒜.weight p.1, ℬ.weight p.2)) fun _ => Iff.rfl).symm

/-- The Cartesian product of two weighted classes: pairs, weight the monomial product
(exponent sum) of the component weights. -/
noncomputable def prod [DecidableEq σ] : WeightedClass σ where
  carrier := 𝒜.carrier × ℬ.carrier
  weight p := 𝒜.weight p.1 + ℬ.weight p.2
  finite_fiber d := Finite.of_equiv _ (𝒜.wprodFiberEquiv ℬ d).symm

@[simp]
theorem prod_wcard [DecidableEq σ] (d : σ →₀ ℕ) :
    (𝒜.prod ℬ).wcard d = ∑ p ∈ antidiagonal d, 𝒜.wcard p.1 * ℬ.wcard p.2 := by
  have h1 : (𝒜.prod ℬ).wcard d = Nat.card (Σ y : antidiagonal d,
      {p : 𝒜.carrier × ℬ.carrier //
        (𝒜.weight p.1, ℬ.weight p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))}) :=
    Nat.card_congr (𝒜.wprodFiberEquiv ℬ d)
  rw [h1, Nat.card_sigma,
    ← Finset.sum_coe_sort (antidiagonal d) fun p => 𝒜.wcard p.1 * ℬ.wcard p.2]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.card_congr (𝒜.wprodPairEquiv ℬ _), Nat.card_prod]
  rfl

/-- The weighted OGF of a Cartesian product is the product of the weighted OGFs. -/
@[simp]
theorem wgf_prod [DecidableEq σ] : (𝒜.prod ℬ).wgf = 𝒜.wgf * ℬ.wgf := by
  ext d
  simp [prod_wcard, MvPowerSeries.coeff_mul]

/-! ### Weighted neutral class -/

/-- The weighted neutral class `ε`: a single object of weight `0` (the empty monomial).
It is the unit for `prod` and the base case of `seq`; its weighted OGF is `1`. -/
def wepsilon : WeightedClass.{u, v} σ where
  carrier := PUnit.{u + 1}
  weight _ := 0
  finite_fiber _ := Finite.of_injective Subtype.val Subtype.val_injective

theorem wepsilon_wcard [DecidableEq σ] (d : σ →₀ ℕ) :
    (wepsilon (σ := σ)).wcard d = if d = 0 then 1 else 0 := by
  have hc : (wepsilon (σ := σ)).wcard d = Nat.card {_u : PUnit // (0 : σ →₀ ℕ) = d} := rfl
  rw [hc]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ : PUnit => rfl)]
    exact Nat.card_unique
  · rw [if_neg hd]
    haveI : IsEmpty {_u : PUnit // (0 : σ →₀ ℕ) = d} := ⟨fun x => hd x.2.symm⟩
    exact Nat.card_of_isEmpty

/-- The weighted OGF of the neutral class is `1`. -/
@[simp]
theorem wgf_wepsilon : (wepsilon (σ := σ)).wgf = (1 : MvPowerSeries σ ℕ) := by
  classical
  ext d
  rw [coeff_wgf, wepsilon_wcard, MvPowerSeries.coeff_one]

/-! ### Weighted sequence -/

/-- The total degree of an exponent vector `d`, as a function of `d` alone: the
sum of all its exponents. Used as a length bound for weight-`d` sequences. -/
private noncomputable def tdeg (d : σ →₀ ℕ) : ℕ := Multiset.card (Finsupp.toMultiset d)

private theorem deg_eq_tdeg (a : 𝒜.carrier) : 𝒜.deg a = tdeg (𝒜.weight a) := by
  rw [tdeg, Finsupp.card_toMultiset, deg]
  rfl

private theorem tdeg_add (x y : σ →₀ ℕ) : tdeg (x + y) = tdeg x + tdeg y := by
  rw [tdeg, tdeg, tdeg, map_add, Multiset.card_add]

private theorem tdeg_zero : tdeg (0 : σ →₀ ℕ) = 0 := by
  rw [tdeg, map_zero, Multiset.card_zero]

private theorem tdeg_list_map_sum (l : List 𝒜.carrier) :
    (l.map 𝒜.deg).sum = tdeg ((l.map 𝒜.weight).sum) := by
  induction l with
  | nil => rw [List.map_nil, List.map_nil, List.sum_nil, List.sum_nil, tdeg_zero]
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, tdeg_add,
        𝒜.deg_eq_tdeg a, ih]

/-- When no object has weight `0`, the length of a sequence is at most the total
degree of its weight (every entry contributes degree at least `1`). -/
theorem length_le_deg_map (h : ∀ a, 𝒜.weight a ≠ 0) (l : List 𝒜.carrier) :
    l.length ≤ (l.map 𝒜.deg).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have : 1 ≤ 𝒜.deg a :=
        Nat.one_le_iff_ne_zero.mpr fun hz => h a ((𝒜.deg_eq_zero_iff a).mp hz)
      omega

/-- Fibers of the weighted sequence construction are finite: a weight-`d` sequence has
length bounded by the total degree of `d`, and all of its entries have weight `≤ d`,
so lie among the (finitely many) objects of weight `≤ d`. -/
theorem finite_wseq_fiber (h : ∀ a, 𝒜.weight a ≠ 0) (d : σ →₀ ℕ) :
    Finite {l : List 𝒜.carrier // (l.map 𝒜.weight).sum = d} := by
  classical
  have hIic : (Set.Iic d).Finite :=
    (Set.finite_Icc 0 d).subset fun e he => Set.mem_Icc.mpr ⟨bot_le, he⟩
  haveI : Finite {a : 𝒜.carrier // 𝒜.weight a ≤ d} :=
    (Set.Finite.preimage' hIic
      (fun b _ => Set.finite_coe_iff.mp (𝒜.finite_fiber b))).to_subtype
  haveI : Finite {m : List {a : 𝒜.carrier // 𝒜.weight a ≤ d} // m.length ≤ tdeg d} :=
    (List.finite_length_le {a : 𝒜.carrier // 𝒜.weight a ≤ d} (tdeg d)).to_subtype
  have hmem : ∀ {l : List 𝒜.carrier}, (l.map 𝒜.weight).sum = d → ∀ a ∈ l, 𝒜.weight a ≤ d :=
    fun {l} hl a ha =>
      le_of_le_of_eq (List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)) hl
  refine Finite.of_injective
    (fun l : {l : List 𝒜.carrier // (l.map 𝒜.weight).sum = d} =>
      (⟨l.1.attachWith (fun a => 𝒜.weight a ≤ d) (hmem l.2), by
          rw [List.length_attachWith]
          refine (𝒜.length_le_deg_map h l.1).trans ?_
          rw [𝒜.tdeg_list_map_sum l.1, l.2]⟩ :
        {m : List {a : 𝒜.carrier // 𝒜.weight a ≤ d} // m.length ≤ tdeg d})) ?_
  intro x y hxy
  apply Subtype.ext
  have h2 := congrArg (List.map Subtype.val) (congrArg Subtype.val hxy)
  rwa [List.attachWith_map_subtype_val, List.attachWith_map_subtype_val] at h2

/-- The fixed-point (cons) decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)`: a sequence is
empty, or a first object followed by a sequence. -/
def wseqDecomp :
    List 𝒜.carrier ≃ (wepsilon (σ := σ)).carrier ⊕ 𝒜.carrier × List 𝒜.carrier where
  toFun
    | [] => Sum.inl ⟨⟩
    | a :: l => Sum.inr (a, l)
  invFun
    | Sum.inl _ => []
    | Sum.inr (a, l) => a :: l
  left_inv := by rintro (_ | ⟨a, l⟩) <;> rfl
  right_inv := by rintro (⟨⟩ | ⟨a, l⟩) <;> rfl

/-- The weighted sequence construction `SEQ(𝒜)`: finite sequences of objects of `𝒜`
(which must have no object of weight `0`), with weight the product (exponent sum) of
the component weights. -/
noncomputable def seq (h : ∀ a, 𝒜.weight a ≠ 0) : WeightedClass σ where
  carrier := List 𝒜.carrier
  weight l := (l.map 𝒜.weight).sum
  finite_fiber d := 𝒜.finite_wseq_fiber h d

/-- **The weighted OGF functional equation of the sequence construction.** Read off
the cons decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)` through `wgf_congr`, `wgf_sum`,
`wgf_prod`. Over a base ring with subtraction this becomes the closed form
`(SEQ 𝒜).wgf = (1 - 𝒜.wgf)⁻¹`; over `ℕ` the functional equation is the available form. -/
theorem wgf_seq (h : ∀ a, 𝒜.weight a ≠ 0) :
    (𝒜.seq h).wgf = 1 + 𝒜.wgf * (𝒜.seq h).wgf := by
  classical
  have hcongr : (𝒜.seq h).wgf = ((wepsilon (σ := σ)).sum (𝒜.prod (𝒜.seq h))).wgf :=
    wgf_congr (𝒜 := 𝒜.seq h) (ℬ := (wepsilon (σ := σ)).sum (𝒜.prod (𝒜.seq h)))
      𝒜.wseqDecomp (by rintro (_ | ⟨a, l⟩) <;> rfl)
  nth_rewrite 1 [hcongr]
  rw [wgf_sum, wgf_prod, wgf_wepsilon]

/-! ### Weighted base change and closed forms

The weighted OGF lives in `MvPowerSeries σ ℕ` (coefficients *are* the counts). Casting
it into a ring — in particular a field — makes subtraction and inverses available, which
turns the `seq` functional equation into the closed form `(1 - A)⁻¹`. -/

/-- The weighted OGF base-changed into a (semi)ring `R`: the image of `𝒜.wgf` under the
coefficientwise map `ℕ → R`. -/
noncomputable def wgfMap (R : Type*) [Semiring R] : MvPowerSeries σ R :=
  MvPowerSeries.map (Nat.castRingHom R) 𝒜.wgf

@[simp]
theorem coeff_wgfMap (R : Type*) [Semiring R] (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (𝒜.wgfMap R) = (𝒜.wcard d : R) := by
  rw [wgfMap, MvPowerSeries.coeff_map, coeff_wgf, Nat.coe_castRingHom]

@[simp]
theorem wgfMap_sum (R : Type*) [Semiring R] :
    (𝒜.sum ℬ).wgfMap R = 𝒜.wgfMap R + ℬ.wgfMap R := by
  simp only [wgfMap, wgf_sum, map_add]

@[simp]
theorem wgfMap_prod [DecidableEq σ] (R : Type*) [Semiring R] :
    (𝒜.prod ℬ).wgfMap R = 𝒜.wgfMap R * ℬ.wgfMap R := by
  simp only [wgfMap, wgf_prod, map_mul]

@[simp]
theorem wgfMap_wepsilon (R : Type*) [Semiring R] :
    (wepsilon (σ := σ)).wgfMap R = 1 := by
  simp only [wgfMap, wgf_wepsilon, map_one]

/-- The weighted `seq` functional equation, base-changed into any (semi)ring `R`. -/
theorem wgfMap_seq_eq (R : Type*) [Semiring R] (h : ∀ a, 𝒜.weight a ≠ 0) :
    (𝒜.seq h).wgfMap R = 1 + 𝒜.wgfMap R * (𝒜.seq h).wgfMap R := by
  have e := congrArg (MvPowerSeries.map (Nat.castRingHom R)) (𝒜.wgf_seq h)
  simpa only [wgfMap, map_add, map_mul, map_one] using e

/-- **The closed form of the weighted sequence OGF.** Over a field `K`, base-changing
the counts makes `1 - 𝒜.wgfMap K` invertible (its constant term is `1`, since `seq`
forbids weight-`0` objects), and the `seq` functional equation pins the sequence OGF to
`(1 - 𝒜.wgfMap K)⁻¹` — the multivariate closed form of the symbolic method's `SEQ`. -/
theorem wgfMap_seq (K : Type*) [Field K] (h : ∀ a, 𝒜.weight a ≠ 0) :
    (𝒜.seq h).wgfMap K = (1 - 𝒜.wgfMap K)⁻¹ := by
  have hcard0 : 𝒜.wcard 0 = 0 := by
    haveI : IsEmpty (𝒜.WFiber 0) := ⟨fun a => h a.1 a.2⟩
    exact Nat.card_of_isEmpty
  have hA0 : MvPowerSeries.constantCoeff (𝒜.wgfMap K) = 0 := by
    have h0 := 𝒜.coeff_wgfMap K 0
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff, hcard0, Nat.cast_zero] at h0
  have hconst : MvPowerSeries.constantCoeff (1 - 𝒜.wgfMap K) ≠ 0 := by
    rw [map_sub, map_one, hA0, sub_zero]
    exact one_ne_zero
  have hfe : (1 - 𝒜.wgfMap K) * (𝒜.seq h).wgfMap K = 1 := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact 𝒜.wgfMap_seq_eq K h
  calc (𝒜.seq h).wgfMap K
      = (1 - 𝒜.wgfMap K)⁻¹ * ((1 - 𝒜.wgfMap K) * (𝒜.seq h).wgfMap K) := by
        rw [← mul_assoc, MvPowerSeries.inv_mul_cancel _ hconst, one_mul]
    _ = (1 - 𝒜.wgfMap K)⁻¹ * 1 := by rw [hfe]
    _ = (1 - 𝒜.wgfMap K)⁻¹ := mul_one _

/-! ### The weighted generating function as a sum over elements -/

/-- **The weighted OGF is the sum of the weight monomials `X^(weight a)` over all
objects** — the Flajolet–Sedgewick *defining* form `A_wt = ∑_{a ∈ 𝒜} wt(a)`. The family
is summable in the coefficientwise (discrete) product topology on `MvPowerSeries σ ℕ`
exactly because every fibre is finite (`finite_fiber`). -/
theorem wgf_eq_tsum :
    𝒜.wgf = ∑' a : 𝒜.carrier, MvPowerSeries.monomial (𝒜.weight a) (1 : ℕ) := by
  classical
  refine (HasSum.tsum_eq ?_).symm
  rw [MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [MvPowerSeries.coeff_monomial, coeff_wgf]
  exact hasSum_count 𝒜.weight d

end WeightedClass

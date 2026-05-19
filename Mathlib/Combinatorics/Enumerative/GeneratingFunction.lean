/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
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

It also provides the multivariate generalisation `WeightedCombinatorialClass`, where objects carry a
*monomial weight* `σ →₀ ℕ` instead of an `ℕ` size and the generating function lives in
`MvPowerSeries σ ℕ`. Since `PowerSeries R = MvPowerSeries Unit R`, the `σ = Unit` case is
exactly the ordinary theory above; weighting tracks refined statistics (e.g. bivariate
marking) at no extra structural cost — `sum`, `prod`, `seq` and the closed form all carry
over.

## Main definitions

* `CombinatorialClass`: an abbreviation for the `σ = Unit` weighted class — objects
  with an `ℕ`-valued size, recovered as the single weight exponent.
* `CombinatorialClass.ofSize`: build one from an `ℕ`-valued size with finite size-fibres.
* `CombinatorialClass.atom`: the atomic class of a single object of a given size.
* `CombinatorialClass.ogf`: its ordinary generating function in `PowerSeries ℕ`.
* `CombinatorialClass.sum`, `CombinatorialClass.prod`: the union and product constructions.
* `CombinatorialClass.epsilon`: the neutral class (a single object of size `0`).
* `CombinatorialClass.seq`: the sequence construction (finite sequences of objects).
* `CombinatorialClass.ogfMap`: the OGF base-changed into an arbitrary (semi)ring `R`.
* `WeightedCombinatorialClass`: a type with a monomial-valued
  `weight : carrier → (σ →₀ ℕ)` and finite fibers; the multivariate generalisation of
  `CombinatorialClass` (`σ = Unit` recovers it).
* `WeightedCombinatorialClass.wgf`: its weighted generating function in `MvPowerSeries σ ℕ`.
* `WeightedCombinatorialClass.watom`/`sum`/`prod`/`wepsilon`/`seq`: the weighted
  admissible constructions (`wepsilon = watom 0`).
* `WeightedCombinatorialClass.wgfMap`: the weighted GF base-changed into a (semi)ring `R`.
* `CombinatorialClass.toWeighted`: an ordinary class as the `σ = Unit` weighted class.
* `WeightedCombinatorialClass.mark`: refine the weight by a statistic (add a marking
  variable).

## Main results

* `CombinatorialClass.ogf_congr`: size-preserving isomorphic classes have equal OGF.
* `CombinatorialClass.ogf_sum`: `(𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf`.
* `CombinatorialClass.ogf_prod`: `(𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf`.
* `CombinatorialClass.ogf_epsilon`: `epsilon.ogf = 1`.
* `CombinatorialClass.ogf_atom` / `WeightedCombinatorialClass.wgf_watom`: the atom's GF
  is the monomial `Xᵏ` / `X^w`.
* `CombinatorialClass.ogf_seq`: `(𝒜.seq h).ogf = 1 + 𝒜.ogf * (𝒜.seq h).ogf`, the
  functional equation of the sequence construction.
* `CombinatorialClass.ogfMap_seq`: over a field `K`, the closed form
  `(𝒜.seq h).ogfMap K = (1 - 𝒜.ogfMap K)⁻¹` (`PowerSeries.Inverse`).
* `WeightedCombinatorialClass.wgf_sum`/`wgf_prod`/`wgf_wepsilon`: the weighted analogues
  of the admissible-construction generating-function identities.
* `WeightedCombinatorialClass.wgf_seq`: `(𝒜.seq h).wgf = 1 + 𝒜.wgf * (𝒜.seq h).wgf`,
  the weighted sequence functional equation.
* `WeightedCombinatorialClass.wgfMap_seq`: over a field `K`, the multivariate closed
  form `(𝒜.seq h).wgfMap K = (1 - 𝒜.wgfMap K)⁻¹` (`MvPowerSeries.Inverse`).
* `CombinatorialClass.ogf_eq_tsum`, `WeightedCombinatorialClass.wgf_eq_tsum`: the GF is
  the sum of the weight monomials over all objects (the Flajolet–Sedgewick defining
  form), via the discrete/product topology `{Mv,}PowerSeries.WithPiTopology`.
* `CombinatorialClass.toWeighted_wgf`: the collapse identity `𝒜.toWeighted.wgf = 𝒜.ogf`
  (now `rfl` — `CombinatorialClass` *is* `WeightedCombinatorialClass Unit`).
* `WeightedCombinatorialClass.wcard_eq_tsum_mark`: the OGF is recovered from the marked
  BGF by summing over the statistic (forgetting the mark — grading-aggregation).

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

/-! ## Weighted (multivariate) generating functions

Generalising `size : carrier → ℕ` to a *monomial-valued weight*
`weight : carrier → (σ →₀ ℕ)` yields multivariate generating functions in
`MvPowerSeries σ ℕ`: the coefficient of the monomial `X^d` counts the objects of
weight exactly `d`. Since `PowerSeries R = MvPowerSeries Unit R`, the `σ = Unit` case
is exactly the ordinary generating function below. The single ℕ size survives as the
total degree `deg`, which drives every finiteness argument. -/

/-- A *weighted combinatorial class*: a type `carrier` equipped with a monomial-valued
`weight` (an exponent vector `σ →₀ ℕ`) whose fibers — the objects of each fixed weight —
are finite. The `σ = Unit` case is an ordinary `CombinatorialClass`. -/
structure WeightedCombinatorialClass (σ : Type*) where
  /-- The type of objects of the class. -/
  carrier : Type u
  /-- The weight of an object, as a monomial exponent vector. -/
  weight : carrier → (σ →₀ ℕ)
  /-- There are only finitely many objects of any given weight. -/
  finite_fiber (d : σ →₀ ℕ) : Finite {a : carrier // weight a = d}

namespace WeightedCombinatorialClass

variable {σ : Type v} (𝒜 ℬ : WeightedCombinatorialClass.{u, v} σ)

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
def sum : WeightedCombinatorialClass σ where
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
noncomputable def prod [DecidableEq σ] : WeightedCombinatorialClass σ where
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

/-! ### The atomic weighted class -/

/-- The atomic weighted class `watom w`: a single object of weight `w`. This is the
building block of the symbolic method — `wepsilon` is `watom 0`, and an ordinary size-`k`
atom is `watom (Finsupp.single () k)` (see `CombinatorialClass.atom`). -/
def watom (w : σ →₀ ℕ) : WeightedCombinatorialClass.{u, v} σ where
  carrier := PUnit.{u + 1}
  weight _ := w
  finite_fiber _ := Finite.of_injective Subtype.val Subtype.val_injective

theorem watom_wcard [DecidableEq σ] (w d : σ →₀ ℕ) :
    (watom (σ := σ) w).wcard d = if d = w then 1 else 0 := by
  have hc : (watom (σ := σ) w).wcard d = Nat.card {_u : PUnit // w = d} := rfl
  rw [hc]
  by_cases hd : d = w
  · subst hd
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ : PUnit => rfl)]
    exact Nat.card_unique
  · rw [if_neg hd]
    haveI : IsEmpty {_u : PUnit // w = d} := ⟨fun x => hd x.2.symm⟩
    exact Nat.card_of_isEmpty

/-- The weighted OGF of the weight-`w` atom is the monomial `X^w`. -/
@[simp]
theorem wgf_watom (w : σ →₀ ℕ) :
    (watom (σ := σ) w).wgf = MvPowerSeries.monomial w (1 : ℕ) := by
  classical
  ext d
  rw [coeff_wgf, watom_wcard, MvPowerSeries.coeff_monomial]

/-! ### Weighted neutral class -/

/-- The weighted neutral class `ε`: a single object of weight `0` (the empty monomial),
i.e. the weight-`0` atom `watom 0`. It is the unit for `prod` and the base case of `seq`;
its weighted OGF is `1`. -/
def wepsilon : WeightedCombinatorialClass.{u, v} σ := watom 0

theorem wepsilon_wcard [DecidableEq σ] (d : σ →₀ ℕ) :
    (wepsilon (σ := σ)).wcard d = if d = 0 then 1 else 0 := by
  simp only [wepsilon]
  exact watom_wcard 0 d

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
noncomputable def seq (h : ∀ a, 𝒜.weight a ≠ 0) : WeightedCombinatorialClass σ where
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

/-! ### Marking a statistic, and recovering the OGF by forgetting it -/

/-- For a function out of a finite type, the family of fibre cardinalities sums (in the
discrete topology on `ℕ`) to the cardinality of the domain: only the finitely many
values in the range have a nonempty fibre. This is the convergence engine behind
`wcard_eq_tsum_mark` (summing the marked counts over the statistic). -/
private theorem hasSum_card_fiber {α β : Type*} [Finite α] (f : α → β) :
    HasSum (fun b : β => Nat.card {a : α // f a = b}) (Nat.card α) := by
  classical
  have hrange : (Set.range f).Finite := Set.finite_range f
  have hpre : f ⁻¹' (hrange.toFinset : Set β) = Set.univ := by
    ext a; simp
  have hcard : Nat.card α = ∑ b ∈ hrange.toFinset, Nat.card {a : α // f a = b} := by
    rw [← Finset.card_preimage_eq_sum_card_image_eq
        (fun b _ => Set.toFinite {a | f a = b}), hpre]
    exact (Nat.card_congr (Equiv.Set.univ α)).symm
  rw [hcard]
  apply hasSum_sum_of_ne_finset_zero
  intro b hb
  rw [Set.Finite.mem_toFinset] at hb
  have : IsEmpty {a : α // f a = b} := ⟨fun a => hb ⟨a.1, a.2⟩⟩
  exact Nat.card_of_isEmpty

/-- `Finsupp.sumElim` is injective in its two arguments jointly: a glued exponent vector
on `τ ⊕ ι` determines its `τ`-part and its `ι`-part. This is what splits a marked fibre
(weight `sumElim e d`) into the `𝒜`-weight condition `= e` and the statistic `= d`. -/
private theorem sumElim_inj_iff {τ ι : Type*} (f e : τ →₀ ℕ) (g d : ι →₀ ℕ) :
    Finsupp.sumElim f g = Finsupp.sumElim e d ↔ f = e ∧ g = d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h2 := congrArg (fun t => Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) h
      simpa only [Finsupp.comapDomain_inl_sumElim] using h2
    · have h2 := congrArg (fun t => Finsupp.comapDomain Sum.inr t Sum.inr_injective.injOn) h
      simpa only [Finsupp.comapDomain_inr_sumElim] using h2
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **The marking primitive.** Refine the weight by a statistic `χ : carrier → (ι →₀ ℕ)`,
appending it in fresh variables: `weight a := sumElim (𝒜.weight a) (χ a)` in
`(σ ⊕ ι) →₀ ℕ`. Marking only *refines* the partition into fibres, so finiteness is
inherited from `𝒜` (each marked fibre injects into a `𝒜`-fibre). -/
noncomputable def mark {ι : Type*} (χ : 𝒜.carrier → (ι →₀ ℕ)) :
    WeightedCombinatorialClass (σ ⊕ ι) where
  carrier := 𝒜.carrier
  weight a := Finsupp.sumElim (𝒜.weight a) (χ a)
  finite_fiber e := by
    refine Finite.of_injective
      (fun a : {a : 𝒜.carrier // Finsupp.sumElim (𝒜.weight a) (χ a) = e} =>
        (⟨a.1, ?_⟩ : 𝒜.WFiber (Finsupp.comapDomain Sum.inl e Sum.inl_injective.injOn)))
      (fun x y h => Subtype.ext (Subtype.mk.injEq .. ▸ h))
    have h2 := congrArg (fun t => Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) a.2
    simpa only [Finsupp.comapDomain_inl_sumElim] using h2

variable {ι : Type*} (χ : 𝒜.carrier → (ι →₀ ℕ))

/-- The marked count is the *bivariate* (refined) count: objects of `𝒜`-weight `e`
*and* statistic `d`. -/
theorem mark_wcard (e : σ →₀ ℕ) (d : ι →₀ ℕ) :
    (𝒜.mark χ).wcard (Finsupp.sumElim e d) =
      Nat.card {a : 𝒜.carrier // 𝒜.weight a = e ∧ χ a = d} := by
  simp only [wcard, WFiber, mark]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  exact sumElim_inj_iff (𝒜.weight a) e (χ a) d

/-- **The OGF is recovered from the BGF by forgetting the mark.** Summing the marked
counts over all values of the statistic returns the original counts; the family is
summable in discrete `ℕ` because the `e`-fibre of `𝒜` is finite. This is the
grading-aggregation form of "specialise the marking variables to `1`" (D2a), needing
no power-series substitution. -/
theorem wcard_eq_tsum_mark (e : σ →₀ ℕ) :
    HasSum (fun d : ι →₀ ℕ => (𝒜.mark χ).wcard (Finsupp.sumElim e d)) (𝒜.wcard e) := by
  have hfun (d : ι →₀ ℕ) :
      (𝒜.mark χ).wcard (Finsupp.sumElim e d)
        = Nat.card {a : 𝒜.WFiber e // χ a.1 = d} := by
    rw [𝒜.mark_wcard χ e d]
    refine Nat.card_congr ?_
    exact
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  simp only [hfun]
  rw [wcard]
  exact hasSum_card_fiber (α := 𝒜.WFiber e) (fun a => χ a.1)

end WeightedCombinatorialClass

/-! ## Ordinary combinatorial classes (the `σ = Unit` case)

`PowerSeries ℕ = MvPowerSeries Unit ℕ`, so an *ordinary* combinatorial class — objects
with an `ℕ`-valued `size` — is exactly the `σ = Unit` weighted class, with weight
monomial `X^(size a) = single () (size a)`. `CombinatorialClass` is that abbreviation;
the `size`/`ogf` API below is a thin layer over the weighted theory. -/

/-- An (ordinary) combinatorial class: the `σ = Unit` weighted class — objects with an
`ℕ`-valued size, recovered as the single weight exponent. -/
abbrev CombinatorialClass := WeightedCombinatorialClass.{u} Unit

namespace CombinatorialClass

variable (𝒜 ℬ : CombinatorialClass.{u})

/-- The size of an object: its single (`Unit`) weight exponent. -/
def size (a : 𝒜.carrier) : ℕ := 𝒜.weight a ()

theorem weight_eq_single (a : 𝒜.carrier) :
    𝒜.weight a = Finsupp.single () (𝒜.size a) := Finsupp.unique_single _

theorem size_ne_zero_iff (a : 𝒜.carrier) : 𝒜.size a ≠ 0 ↔ 𝒜.weight a ≠ 0 := by
  rw [weight_eq_single, ne_eq, ne_eq, Finsupp.single_eq_zero]

/-- Build a combinatorial class from an `ℕ`-valued size with finite size-fibres. -/
noncomputable def ofSize {carrier : Type u} (size : carrier → ℕ)
    (hfin : ∀ n, Finite {a : carrier // size a = n}) : CombinatorialClass where
  carrier := carrier
  weight a := Finsupp.single () (size a)
  finite_fiber d := by
    have hiff (a : carrier) : size a = d () ↔ Finsupp.single () (size a) = d := by
      constructor
      · rintro h; rw [h]; exact (Finsupp.unique_single d).symm
      · intro h; have h2 := congrArg (fun f : Unit →₀ ℕ => f ()) h; simpa using h2
    haveI := hfin (d ())
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight hiff)

@[simp] theorem ofSize_carrier {carrier : Type u} (size : carrier → ℕ) (hfin) :
    (ofSize size hfin).carrier = carrier := rfl

@[simp] theorem ofSize_size {carrier : Type u} (size : carrier → ℕ) (hfin)
    (a : carrier) : (ofSize size hfin).size a = size a := by
  simp only [CombinatorialClass.size, ofSize, Finsupp.single_eq_same]

/-- The type of objects of size `n`. -/
abbrev Fiber (n : ℕ) : Type _ := {a : 𝒜.carrier // 𝒜.size a = n}

/-- A size-`n` fibre is the weight-`single () n` fibre of the underlying weighted class. -/
def fiber_equiv_wfiber (n : ℕ) :
    𝒜.Fiber n ≃ 𝒜.WFiber (Finsupp.single () n) :=
  Equiv.subtypeEquivRight fun a => by
    rw [weight_eq_single]
    exact ⟨fun h => by rw [h], fun h => (Finsupp.single_injective ()).eq_iff.mp h⟩

instance instFiniteFiber (n : ℕ) : Finite (𝒜.Fiber n) :=
  Finite.of_equiv _ (𝒜.fiber_equiv_wfiber n).symm

/-- The number of objects of size `n`. -/
noncomputable def card (n : ℕ) : ℕ := Nat.card (𝒜.Fiber n)

theorem card_eq_wcard (n : ℕ) : 𝒜.card n = 𝒜.wcard (Finsupp.single () n) :=
  Nat.card_congr (𝒜.fiber_equiv_wfiber n)

/-- The ordinary generating function `A(X) = ∑ₙ |𝒜ₙ| Xⁿ`. -/
noncomputable def ogf : PowerSeries ℕ := 𝒜.wgf

@[simp] theorem coeff_ogf (n : ℕ) : PowerSeries.coeff n 𝒜.ogf = 𝒜.card n := by
  rw [ogf, PowerSeries.coeff_def (s := Finsupp.single () n) Finsupp.single_eq_same,
    WeightedCombinatorialClass.coeff_wgf, ← card_eq_wcard]

theorem ogf_congr (e : 𝒜.carrier ≃ ℬ.carrier) (he : ∀ a, ℬ.size (e a) = 𝒜.size a) :
    𝒜.ogf = ℬ.ogf :=
  WeightedCombinatorialClass.wgf_congr 𝒜 ℬ e fun a => by
    rw [weight_eq_single, weight_eq_single, he a]

/-- The disjoint union. -/
def sum : CombinatorialClass := WeightedCombinatorialClass.sum 𝒜 ℬ

@[simp] theorem ogf_sum : (𝒜.sum ℬ).ogf = 𝒜.ogf + ℬ.ogf :=
  WeightedCombinatorialClass.wgf_sum 𝒜 ℬ

/-- The Cartesian product (additive size). -/
noncomputable def prod : CombinatorialClass := WeightedCombinatorialClass.prod 𝒜 ℬ

@[simp] theorem ogf_prod : (𝒜.prod ℬ).ogf = 𝒜.ogf * ℬ.ogf :=
  WeightedCombinatorialClass.wgf_prod 𝒜 ℬ

/-- The neutral class (a single object of size `0`). -/
noncomputable def epsilon : CombinatorialClass := WeightedCombinatorialClass.wepsilon

@[simp] theorem ogf_epsilon : epsilon.ogf = (1 : PowerSeries ℕ) :=
  WeightedCombinatorialClass.wgf_wepsilon

/-- The atomic class of a single object of size `k` — the symbolic-method atom; the unit
atom `Z` is `atom 1`. It is `watom (Finsupp.single () k)`. -/
noncomputable def atom (k : ℕ) : CombinatorialClass :=
  WeightedCombinatorialClass.watom (Finsupp.single () k)

@[simp] theorem atom_size (k : ℕ) (a : (atom k).carrier) : (atom k).size a = k := by
  simp only [CombinatorialClass.size, atom, WeightedCombinatorialClass.watom,
    Finsupp.single_eq_same]

theorem atom_card (k m : ℕ) : (atom k).card m = if m = k then 1 else 0 := by
  rw [card_eq_wcard, atom, WeightedCombinatorialClass.watom_wcard]
  have hiff : (Finsupp.single () m = Finsupp.single () k) ↔ m = k :=
    (Finsupp.single_injective ()).eq_iff
  by_cases h : m = k
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (hiff.not.mpr h)]

@[simp] theorem ogf_atom (k : ℕ) : (atom k).ogf = (X : PowerSeries ℕ) ^ k := by
  ext m
  rw [coeff_ogf, atom_card, PowerSeries.coeff_X_pow]

/-- The sequence construction. -/
noncomputable def seq (h : ∀ a, 𝒜.size a ≠ 0) : CombinatorialClass :=
  WeightedCombinatorialClass.seq 𝒜 fun a => (𝒜.size_ne_zero_iff a).mp (h a)

theorem ogf_seq (h : ∀ a, 𝒜.size a ≠ 0) :
    (𝒜.seq h).ogf = 1 + 𝒜.ogf * (𝒜.seq h).ogf :=
  WeightedCombinatorialClass.wgf_seq 𝒜 _

/-- The OGF base-changed into a (semi)ring `R`. -/
noncomputable def ogfMap (R : Type*) [Semiring R] : PowerSeries R := 𝒜.wgfMap R

theorem ogfMap_seq (K : Type*) [Field K] (h : ∀ a, 𝒜.size a ≠ 0) :
    (𝒜.seq h).ogfMap K = (1 - 𝒜.ogfMap K)⁻¹ :=
  WeightedCombinatorialClass.wgfMap_seq 𝒜 K _

theorem ogf_eq_tsum : 𝒜.ogf = ∑' a : 𝒜.carrier, (X : PowerSeries ℕ) ^ 𝒜.size a := by
  refine (HasSum.tsum_eq ?_).symm
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [coeff_X_pow, coeff_ogf]
  exact hasSum_count 𝒜.size d

/-- `CombinatorialClass` *is* `WeightedCombinatorialClass Unit`; `toWeighted` is the
identity, kept so the weighted API (`mark`, `wcard`, …) applies to ordinary classes. -/
abbrev toWeighted : WeightedCombinatorialClass Unit := 𝒜

@[simp] theorem toWeighted_wgf : 𝒜.toWeighted.wgf = 𝒜.ogf := rfl

end CombinatorialClass


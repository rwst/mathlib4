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

A *combinatorial class* is, informally, a type together with a `size : α → ℕ` function whose
fibers (the objects of each given size) are finite. Its *ordinary generating function* (OGF)
is the formal power series `A(X) = ∑ₙ |𝒜ₙ| Xⁿ`, where `𝒜ₙ` is the set of objects of size `n`.

Rather than bundling the type, the weight and the finiteness proof into a structure, this file
keeps the *weight unbundled*: every construction is a plain Mathlib type (`Sum`, `Prod`,
`List`, `PUnit`) equipped with an explicit weight function, and the finiteness requirement is
the `Prop`-valued typeclass `FiniteFibers` (a sibling of `Finite`). This integrates natively
with the rest of Mathlib — the symbolic-method algebra is literally the algebra of `⊕`, `×`
and `List` — and the finiteness side-conditions propagate by instance resolution.

It works with *monomial-valued weights* `weight : α → (σ →₀ ℕ)`, so the generating function
lives in `MvPowerSeries σ ℕ` (the coefficient of `X^d` counts the objects of weight `d`).
Since `PowerSeries R = MvPowerSeries Unit R`, the `σ = Unit` case is the ordinary theory; the
thin `ogf` layer at the end specialises it to an `ℕ`-valued size.

This file proves the basic *admissible constructions* of the symbolic method
(Flajolet–Sedgewick, *Analytic Combinatorics*):

* disjoint union `α ⊕ β` with weight `Sum.elim` has GF `A + B`;
* Cartesian product `α × β` with weight `prodWeight` (additive) has GF `A * B`;
* the neutral class (`PUnit`, weight `0`) has GF `1`;
* the sequence class (`List α`, weight `listWeight`) satisfies `S = 1 + A * S`.

## Main definitions

* `FiniteFibers`: the `Prop` class "only finitely many objects of each weight".
* `genFun`: the weighted generating function `∑_d |𝒜_d| X^d` of a weight `α → σ →₀ ℕ`.
* `Sum.elim`, `prodWeight`, `atomWeight`, `listWeight`, `markWeight`: the weight combinators
  realising disjoint union, product, atom/neutral class, sequence and marking.
* `genFunMap`: the generating function base-changed into an arbitrary (semi)ring `R`.
* `FiniteSizeFibers`, `ogf`, `ogfMap`: the `σ = Unit` (`ℕ`-size) specialisation.

## Main results

* `genFun_congr`: weight-preserving isomorphic classes have equal GF (no finiteness needed).
* `genFun_sum`: `genFun (Sum.elim wα wβ) = genFun wα + genFun wβ`.
* `genFun_prod`: `genFun (prodWeight wα wβ) = genFun wα * genFun wβ`.
* `genFun_atomWeight` / `genFun_atomWeight_zero`: the atom's GF is `X^w` / `1`.
* `genFun_listWeight`: `genFun (listWeight wt) = 1 + genFun wt * genFun (listWeight wt)`,
  the sequence functional equation.
* `genFunMap_listWeight`: over *any ring*, the closed form `invOfUnit (1 - genFunMap R wt) 1`
  (`genFunMap_listWeight_inv` gives the `(1 - ·)⁻¹` form over a field).
* `genFun_eq_tsum`: the GF is `∑' a, X^(wt a)` (the Flajolet–Sedgewick defining form), via
  the discrete/product topology `{Mv,}PowerSeries.WithPiTopology`.
* `card_eq_tsum_markWeight`: the unmarked count is recovered from the marked (bivariate)
  counts by summing over the statistic (grading-aggregation).
* `ogf_sum`/`ogf_prod`/`ogf_atom`/`ogf_seq`/`ogf_eq_tsum`/`ogfMap_seq` (+ `ogfMap_seq_inv`):
  the `ℕ`-size specialisations.

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

universe u v w

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

/-- For a function out of a finite type, the family of fibre cardinalities sums (in the
discrete topology on `ℕ`) to the cardinality of the domain: only the finitely many
values in the range have a nonempty fibre. This is the convergence engine behind
`card_eq_tsum_markWeight` (summing the marked counts over the statistic). -/
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
(weight `sumElim e d`) into the `wt`-condition `= e` and the statistic `= d`. -/
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

namespace Combinatorics

variable {α : Type u} {β : Type v} {σ : Type w}

/-! ## Finite fibres

The only finiteness the generating-function identities use is that the objects of each
fixed weight are finite. Made a `Prop` class (a sibling of `Finite`): no diamond, no
canonicity issue — it is a *property* of the weight, not chosen data, so the weight stays
explicit while the side-condition propagates by instance resolution. -/

/-- The objects of each fixed weight form a finite type. -/
class FiniteFibers (wt : α → σ →₀ ℕ) : Prop where
  /-- There are only finitely many objects of any given weight. -/
  finite_fiber (d : σ →₀ ℕ) : Finite {a // wt a = d}

attribute [instance] FiniteFibers.finite_fiber

/-! ## The weighted generating function -/

/-- The weighted generating function `A(X) = ∑_{a} X^(wt a)`, equivalently
`∑_d |𝒜_d| X^d`, in `MvPowerSeries σ ℕ`. It is total: `Nat.card` is junk-`0` on infinite
types, so no finiteness is needed to *define* it (only to prove the identities). -/
noncomputable def genFun (wt : α → σ →₀ ℕ) : MvPowerSeries σ ℕ :=
  fun d => Nat.card {a // wt a = d}

@[simp]
theorem coeff_genFun (wt : α → σ →₀ ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (genFun wt) = Nat.card {a // wt a = d} :=
  MvPowerSeries.coeff_apply (genFun wt) d

/-- The weighted GF is an invariant of weight-preserving isomorphism. No finiteness is
needed: `Nat.card_congr` is total. -/
theorem genFun_congr {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ} (e : α ≃ β)
    (he : ∀ a, wβ (e a) = wα a) : genFun wα = genFun wβ := by
  ext d
  rw [coeff_genFun, coeff_genFun]
  exact Nat.card_congr (Equiv.subtypeEquiv e fun a => by rw [he a])

/-- The total degree of an object: the sum of the exponents of its weight monomial.
This is the ℕ-valued “size” that drives all finiteness arguments. -/
def deg (wt : α → σ →₀ ℕ) (a : α) : ℕ := (wt a).sum fun _ n => n

theorem deg_eq_zero_iff (wt : α → σ →₀ ℕ) (a : α) : deg wt a = 0 ↔ wt a = 0 := by
  rw [deg, Finsupp.sum, Finset.sum_eq_zero_iff, Finsupp.ext_iff]
  simp [Finsupp.mem_support_iff]

/-! ### Disjoint union -/

/-- The fiber of a disjoint union splits as the disjoint union of the fibers. -/
def sumFiberEquiv (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) (d : σ →₀ ℕ) :
    {x : α ⊕ β // Sum.elim wα wβ x = d} ≃ {a // wα a = d} ⊕ {b // wβ b = d} :=
  Equiv.subtypeSum

instance instFiniteFibersSumElim {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] : FiniteFibers (Sum.elim wα wβ) where
  finite_fiber d := Finite.of_equiv _ (sumFiberEquiv wα wβ d).symm

private theorem card_sumElim_fiber {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] (d : σ →₀ ℕ) :
    Nat.card {x : α ⊕ β // Sum.elim wα wβ x = d}
      = Nat.card {a // wα a = d} + Nat.card {b // wβ b = d} :=
  (Nat.card_congr (sumFiberEquiv wα wβ d)).trans Nat.card_sum

/-- The weighted GF of a disjoint union is the sum of the weighted GFs. -/
@[simp]
theorem genFun_sum {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFun (Sum.elim wα wβ) = genFun wα + genFun wβ := by
  ext d
  simp [coeff_genFun, card_sumElim_fiber]

/-! ### Cartesian product -/

/-- The weight of a Cartesian product: the monomial product (exponent sum) of the
component weights. -/
noncomputable def prodWeight (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) : α × β → σ →₀ ℕ :=
  fun p => wα p.1 + wβ p.2

/-- The fiber of a product, at a fixed pair of component weights, is the product
of the fibers. -/
def prodPairEquiv (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    {p : α × β // (wα p.1, wβ p.2) = c} ≃ {a // wα a = c.1} × {b // wβ b = c.2} where
  toFun := fun ⟨⟨a, b⟩, h⟩ => (⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩)
  invFun := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨(a, b), Prod.ext ha hb⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl

instance instFiniteProdPair {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] (c : (σ →₀ ℕ) × (σ →₀ ℕ)) :
    Finite {p : α × β // (wα p.1, wβ p.2) = c} :=
  Finite.of_equiv _ (prodPairEquiv wα wβ c).symm

/-- The fiber of a product splits, over the antidiagonal, into the pair-fibers. -/
noncomputable def prodFiberEquiv [DecidableEq σ] (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ)
    (d : σ →₀ ℕ) :
    {p : α × β // wα p.1 + wβ p.2 = d} ≃
      Σ y : antidiagonal d,
        {p : α × β // (wα p.1, wβ p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))} :=
  (Equiv.subtypeEquivRight fun _ => by simp [Finset.mem_antidiagonal]).trans
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (fun p : α × β => (wα p.1, wβ p.2)) fun _ => Iff.rfl).symm

instance instFiniteFibersProdWeight {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] : FiniteFibers (prodWeight wα wβ) where
  finite_fiber d := by classical exact Finite.of_equiv _ (prodFiberEquiv wα wβ d).symm

private theorem card_prodWeight_fiber [DecidableEq σ] (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ)
    [FiniteFibers wα] [FiniteFibers wβ] (d : σ →₀ ℕ) :
    Nat.card {p : α × β // prodWeight wα wβ p = d}
      = ∑ p ∈ antidiagonal d, Nat.card {a // wα a = p.1} * Nat.card {b // wβ b = p.2} := by
  have h1 : Nat.card {p : α × β // prodWeight wα wβ p = d}
      = Nat.card (Σ y : antidiagonal d,
          {p : α × β // (wα p.1, wβ p.2) = (y : (σ →₀ ℕ) × (σ →₀ ℕ))}) :=
    Nat.card_congr (prodFiberEquiv wα wβ d)
  rw [h1, Nat.card_sigma,
    ← Finset.sum_coe_sort (antidiagonal d)
      fun p => Nat.card {a // wα a = p.1} * Nat.card {b // wβ b = p.2}]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.card_congr (prodPairEquiv wα wβ _), Nat.card_prod]

/-- The weighted GF of a Cartesian product is the product of the weighted GFs. -/
@[simp]
theorem genFun_prod {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFun (prodWeight wα wβ) = genFun wα * genFun wβ := by
  classical
  ext d
  simp [coeff_genFun, card_prodWeight_fiber, MvPowerSeries.coeff_mul]

/-! ### The atomic class

A single object of weight `w`, carried by `PUnit`. Universe-polymorphic in the carrier
universe so that `genFun_listWeight` can combine it (at the empty-sequence universe) with
arbitrary-universe classes. `wepsilon = atomWeight 0`. -/

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
  classical
  ext d
  rw [coeff_genFun, card_atomWeight_fiber, MvPowerSeries.coeff_one]

/-! ### The sequence class -/

/-- The total degree of an exponent vector `d`, as a function of `d` alone: the
sum of all its exponents. Used as a length bound for weight-`d` sequences. -/
private noncomputable def tdeg (d : σ →₀ ℕ) : ℕ := Multiset.card (Finsupp.toMultiset d)

private theorem deg_eq_tdeg (wt : α → σ →₀ ℕ) (a : α) : deg wt a = tdeg (wt a) := by
  rw [tdeg, Finsupp.card_toMultiset, deg]
  rfl

private theorem tdeg_add (x y : σ →₀ ℕ) : tdeg (x + y) = tdeg x + tdeg y := by
  rw [tdeg, tdeg, tdeg, map_add, Multiset.card_add]

private theorem tdeg_zero : tdeg (0 : σ →₀ ℕ) = 0 := by
  rw [tdeg, map_zero, Multiset.card_zero]

private theorem tdeg_list_map_sum (wt : α → σ →₀ ℕ) (l : List α) :
    (l.map (deg wt)).sum = tdeg ((l.map wt).sum) := by
  induction l with
  | nil => rw [List.map_nil, List.map_nil, List.sum_nil, List.sum_nil, tdeg_zero]
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, tdeg_add,
        deg_eq_tdeg wt a, ih]

/-- When no object has weight `0`, the length of a sequence is at most the total
degree of its weight (every entry contributes degree at least `1`). -/
theorem length_le_deg_map (wt : α → σ →₀ ℕ) (h : ∀ a, wt a ≠ 0) (l : List α) :
    l.length ≤ (l.map (deg wt)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have : 1 ≤ deg wt a :=
        Nat.one_le_iff_ne_zero.mpr fun hz => h a ((deg_eq_zero_iff wt a).mp hz)
      omega

/-- The weight of the sequence class: the product (exponent sum) of the entry weights. -/
noncomputable def listWeight (wt : α → σ →₀ ℕ) : List α → σ →₀ ℕ := fun l => (l.map wt).sum

/-- Fibers of the sequence construction are finite: a weight-`d` sequence has
length bounded by the total degree of `d`, and all of its entries have weight `≤ d`,
so lie among the (finitely many) objects of weight `≤ d`. -/
theorem finite_listWeight_fiber (wt : α → σ →₀ ℕ) [FiniteFibers wt] (h : ∀ a, wt a ≠ 0)
    (d : σ →₀ ℕ) : Finite {l : List α // (l.map wt).sum = d} := by
  classical
  have hIic : (Set.Iic d).Finite :=
    (Set.finite_Icc 0 d).subset fun e he => Set.mem_Icc.mpr ⟨bot_le, he⟩
  haveI : Finite {a : α // wt a ≤ d} :=
    (Set.Finite.preimage' hIic
      (fun b _ => Set.finite_coe_iff.mp (FiniteFibers.finite_fiber (wt := wt) b))).to_subtype
  haveI : Finite {m : List {a : α // wt a ≤ d} // m.length ≤ tdeg d} :=
    (List.finite_length_le {a : α // wt a ≤ d} (tdeg d)).to_subtype
  have hmem : ∀ {l : List α}, (l.map wt).sum = d → ∀ a ∈ l, wt a ≤ d :=
    fun {l} hl a ha =>
      le_of_le_of_eq (List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)) hl
  refine Finite.of_injective
    (fun l : {l : List α // (l.map wt).sum = d} =>
      (⟨l.1.attachWith (fun a => wt a ≤ d) (hmem l.2), by
          rw [List.length_attachWith]
          refine (length_le_deg_map wt h l.1).trans ?_
          rw [tdeg_list_map_sum wt l.1, l.2]⟩ :
        {m : List {a : α // wt a ≤ d} // m.length ≤ tdeg d})) ?_
  intro x y hxy
  apply Subtype.ext
  have h2 := congrArg (List.map Subtype.val) (congrArg Subtype.val hxy)
  rwa [List.attachWith_map_subtype_val, List.attachWith_map_subtype_val] at h2

/-- The sequence class has finite fibres when no object has weight `0`. This is a *lemma*,
not an instance: the side-condition `∀ a, wt a ≠ 0` is not inferable, so (unlike `Sum`,
`Prod`, `mark`) `SEQ` cannot propagate by instance resolution — it is invoked explicitly. -/
theorem finiteFibers_listWeight (wt : α → σ →₀ ℕ) [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    FiniteFibers (listWeight wt) :=
  ⟨fun d => finite_listWeight_fiber wt h d⟩

/-- The fixed-point (cons) decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)`: a sequence is
empty, or a first object followed by a sequence. -/
def listConsEquiv : List α ≃ PUnit.{u + 1} ⊕ α × List α where
  toFun
    | [] => Sum.inl ⟨⟩
    | a :: l => Sum.inr (a, l)
  invFun
    | Sum.inl _ => []
    | Sum.inr (a, l) => a :: l
  left_inv := by rintro (_ | ⟨a, l⟩) <;> rfl
  right_inv := by rintro (⟨⟩ | ⟨a, l⟩) <;> rfl

/-- **The weighted GF functional equation of the sequence construction.** Read off
the cons decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)` through `genFun_congr`, `genFun_sum`,
`genFun_prod`. Over a base ring with subtraction this becomes the closed form
`(1 - genFun wt)⁻¹`; over `ℕ` the functional equation is the available form. -/
theorem genFun_listWeight (wt : α → σ →₀ ℕ) [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFun (listWeight wt) = 1 + genFun wt * genFun (listWeight wt) := by
  classical
  haveI := finiteFibers_listWeight wt h
  have hcongr : genFun (listWeight wt)
      = genFun (Sum.elim (atomWeight (0 : σ →₀ ℕ)) (prodWeight wt (listWeight wt))) :=
    genFun_congr listConsEquiv (by rintro (_ | ⟨a, l⟩) <;> rfl)
  nth_rewrite 1 [hcongr]
  rw [genFun_sum, genFun_prod, genFun_atomWeight_zero]

/-! ### Base change and closed forms

The weighted GF lives in `MvPowerSeries σ ℕ` (coefficients *are* the counts). Casting it
into a ring — in particular a field — makes subtraction and inverses available, which
turns the `listWeight` functional equation into the closed form `(1 - A)⁻¹`. -/

/-- The weighted GF base-changed into a (semi)ring `R`. -/
noncomputable def genFunMap (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ) :
    MvPowerSeries σ R :=
  MvPowerSeries.map (Nat.castRingHom R) (genFun wt)

@[simp]
theorem coeff_genFunMap (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (genFunMap R wt) = (Nat.card {a // wt a = d} : R) := by
  rw [genFunMap, MvPowerSeries.coeff_map, coeff_genFun, Nat.coe_castRingHom]

@[simp]
theorem genFunMap_sum (R : Type*) [Semiring R] {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFunMap R (Sum.elim wα wβ) = genFunMap R wα + genFunMap R wβ := by
  simp only [genFunMap, genFun_sum, map_add]

@[simp]
theorem genFunMap_prod (R : Type*) [Semiring R] {wα : α → σ →₀ ℕ}
    {wβ : β → σ →₀ ℕ} [FiniteFibers wα] [FiniteFibers wβ] :
    genFunMap R (prodWeight wα wβ) = genFunMap R wα * genFunMap R wβ := by
  simp only [genFunMap, genFun_prod, map_mul]

@[simp]
theorem genFunMap_atomWeight_zero (R : Type*) [Semiring R] :
    genFunMap R (atomWeight (0 : σ →₀ ℕ)) = 1 := by
  simp only [genFunMap, genFun_atomWeight_zero, map_one]

/-- The `listWeight` functional equation, base-changed into any (semi)ring `R`. -/
theorem genFunMap_listWeight_eq (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ)
    [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFunMap R (listWeight wt) = 1 + genFunMap R wt * genFunMap R (listWeight wt) := by
  have e := congrArg (MvPowerSeries.map (Nat.castRingHom R)) (genFun_listWeight wt h)
  simpa only [genFunMap, map_add, map_mul, map_one] using e

/-- The base-changed GF has zero constant term when no object has weight `0`. -/
private theorem constantCoeff_genFunMap_eq_zero (R : Type*) [Semiring R] (wt : α → σ →₀ ℕ)
    (h : ∀ a, wt a ≠ 0) : MvPowerSeries.constantCoeff (genFunMap R wt) = 0 := by
  have hcard0 : Nat.card {a // wt a = (0 : σ →₀ ℕ)} = 0 := by
    haveI : IsEmpty {a // wt a = (0 : σ →₀ ℕ)} := ⟨fun a => h a.1 a.2⟩
    exact Nat.card_of_isEmpty
  have h0 := coeff_genFunMap R wt 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff, hcard0, Nat.cast_zero] at h0

/-- **The closed form of the sequence GF.** Over *any ring* `R` (no field, not even
commutativity, needed), `1 - genFunMap R wt` is a unit — its constant term is `1`, since
`listWeight` forbids weight-`0` objects — and the functional equation pins the sequence GF
to its inverse, the closed form of the symbolic method's `SEQ`. See
`genFunMap_listWeight_inv` for the usual `(1 - ·)⁻¹` notation over a field. -/
theorem genFunMap_listWeight (R : Type*) [Ring R] (wt : α → σ →₀ ℕ)
    [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    genFunMap R (listWeight wt) = MvPowerSeries.invOfUnit (1 - genFunMap R wt) 1 := by
  haveI := finiteFibers_listWeight wt h
  have hconst : MvPowerSeries.constantCoeff (1 - genFunMap R wt) = ((1 : Rˣ) : R) := by
    rw [map_sub, map_one, constantCoeff_genFunMap_eq_zero R wt h, sub_zero, Units.val_one]
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
  have hconst : MvPowerSeries.constantCoeff (1 - genFunMap K wt) = ((1 : Kˣ) : K) := by
    rw [map_sub, map_one, constantCoeff_genFunMap_eq_zero K wt h, sub_zero, Units.val_one]
  rw [genFunMap_listWeight K wt h, MvPowerSeries.invOfUnit_eq' _ _ hconst]

/-! ### The generating function as a sum over elements -/

/-- **The weighted GF is the sum of the weight monomials `X^(wt a)` over all objects** —
the Flajolet–Sedgewick *defining* form `A = ∑_{a} wt(a)`. The family is summable in the
coefficientwise (discrete) product topology exactly because every fibre is finite. -/
theorem genFun_eq_tsum (wt : α → σ →₀ ℕ) [FiniteFibers wt] :
    genFun wt = ∑' a, MvPowerSeries.monomial (wt a) (1 : ℕ) := by
  classical
  refine (HasSum.tsum_eq ?_).symm
  rw [MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [MvPowerSeries.coeff_monomial, coeff_genFun]
  exact hasSum_count wt d

/-! ### Marking a statistic, and recovering the count by forgetting it -/

/-- **The marking primitive.** Refine the weight by a statistic `χ : α → (ι →₀ ℕ)`,
appending it in fresh variables: `markWeight wt χ a = sumElim (wt a) (χ a)` in
`(σ ⊕ ι) →₀ ℕ`. This *re-weights the same carrier* — exactly why the weight must be
explicit data, not a typeclass field keyed on the type. Marking only refines the
partition into fibres, so finiteness is inherited from `wt`. -/
def markWeight (wt : α → σ →₀ ℕ) {ι : Type*} (χ : α → (ι →₀ ℕ)) : α → (σ ⊕ ι) →₀ ℕ :=
  fun a => Finsupp.sumElim (wt a) (χ a)

instance instFiniteFibersMarkWeight (wt : α → σ →₀ ℕ) [FiniteFibers wt] {ι : Type*}
    (χ : α → ι →₀ ℕ) : FiniteFibers (markWeight wt χ) where
  finite_fiber e := by
    refine Finite.of_injective
      (fun a : {a // markWeight wt χ a = e} =>
        (⟨a.1, ?_⟩ : {a // wt a = Finsupp.comapDomain Sum.inl e Sum.inl_injective.injOn}))
      (fun x y h => Subtype.ext (Subtype.mk.injEq .. ▸ h))
    have h2 := congrArg (fun t => Finsupp.comapDomain Sum.inl t Sum.inl_injective.injOn) a.2
    simpa only [markWeight, Finsupp.comapDomain_inl_sumElim] using h2

variable {ι : Type*}

/-- The marked count is the *bivariate* (refined) count: objects of weight `e` *and*
statistic `d`. -/
theorem card_markWeight_fiber (wt : α → σ →₀ ℕ) (χ : α → ι →₀ ℕ) (e : σ →₀ ℕ)
    (d : ι →₀ ℕ) :
    Nat.card {a // markWeight wt χ a = Finsupp.sumElim e d}
      = Nat.card {a // wt a = e ∧ χ a = d} := by
  simp only [markWeight]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  exact sumElim_inj_iff (wt a) e (χ a) d

/-- **The count is recovered from the marked (bivariate) counts by forgetting the
mark.** Summing the marked counts over all values of the statistic returns the original
count; the family is summable in discrete `ℕ` because the `e`-fibre is finite. This is
the grading-aggregation form of "specialise the marking variables to `1`", needing no
power-series substitution. -/
theorem card_eq_tsum_markWeight (wt : α → σ →₀ ℕ) [FiniteFibers wt] (χ : α → ι →₀ ℕ)
    (e : σ →₀ ℕ) :
    HasSum (fun d : ι →₀ ℕ => Nat.card {a // markWeight wt χ a = Finsupp.sumElim e d})
      (Nat.card {a // wt a = e}) := by
  have hfun (d : ι →₀ ℕ) :
      Nat.card {a // markWeight wt χ a = Finsupp.sumElim e d}
        = Nat.card {a : {a // wt a = e} // χ a.1 = d} := by
    rw [card_markWeight_fiber wt χ e d]
    refine Nat.card_congr ?_
    exact
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  simp only [hfun]
  exact hasSum_card_fiber (α := {a // wt a = e}) (fun a => χ a.1)

/-! ## Ordinary classes (the `σ = Unit` case)

`PowerSeries ℕ = MvPowerSeries Unit ℕ`, so an *ordinary* class — objects with an
`ℕ`-valued `size` — is the `σ = Unit` case, with weight monomial `single () (size a)`.
`FiniteFibers` specialises to `FiniteSizeFibers`; `genFun` to `ogf`. -/

/-- The `ℕ`-size analogue of `FiniteFibers`: only finitely many objects of each size. -/
class FiniteSizeFibers (size : α → ℕ) : Prop where
  /-- There are only finitely many objects of any given size. -/
  finite_fiber (n : ℕ) : Finite {a // size a = n}

attribute [instance] FiniteSizeFibers.finite_fiber

instance instFiniteFibersSingleSize (size : α → ℕ) [FiniteSizeFibers size] :
    FiniteFibers (fun a => Finsupp.single () (size a)) where
  finite_fiber d := by
    have hiff (a : α) : size a = d () ↔ Finsupp.single () (size a) = d := by
      constructor
      · rintro h; rw [h]; exact (Finsupp.unique_single d).symm
      · intro h; have h2 := congrArg (fun f : Unit →₀ ℕ => f ()) h; simpa using h2
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

theorem ogf_congr {sα : α → ℕ} {sβ : β → ℕ} (e : α ≃ β) (he : ∀ a, sβ (e a) = sα a) :
    ogf sα = ogf sβ :=
  genFun_congr e fun a => by rw [he a]

@[simp]
theorem ogf_sum (sα : α → ℕ) (sβ : β → ℕ) [FiniteSizeFibers sα] [FiniteSizeFibers sβ] :
    ogf (Sum.elim sα sβ) = ogf sα + ogf sβ := by
  have hw : (fun x : α ⊕ β => Finsupp.single () (Sum.elim sα sβ x))
      = Sum.elim (fun a => Finsupp.single () (sα a))
          (fun b => Finsupp.single () (sβ b)) := by
    funext x; cases x <;> rfl
  simp only [ogf, hw, genFun_sum]

@[simp]
theorem ogf_prod (sα : α → ℕ) (sβ : β → ℕ) [FiniteSizeFibers sα] [FiniteSizeFibers sβ] :
    ogf (fun p : α × β => sα p.1 + sβ p.2) = ogf sα * ogf sβ := by
  have hw : (fun p : α × β => Finsupp.single () (sα p.1 + sβ p.2))
      = prodWeight (fun a => Finsupp.single () (sα a))
          (fun b => Finsupp.single () (sβ b)) := by
    funext p; simp [prodWeight, Finsupp.single_add]
  classical
  simp only [ogf, hw, genFun_prod]

@[simp]
theorem ogf_atom (k : ℕ) :
    ogf (fun _ : PUnit.{u + 1} => k) = (PowerSeries.X : PowerSeries ℕ) ^ k := by
  ext m
  rw [coeff_ogf, PowerSeries.coeff_X_pow]
  by_cases h : m = k
  · subst h
    rw [if_pos rfl, Nat.card_congr (Equiv.subtypeUnivEquiv fun _ : PUnit.{u + 1} => rfl)]
    exact Nat.card_unique
  · rw [if_neg h]
    haveI : IsEmpty {_a : PUnit.{u + 1} // (fun _ => k) _a = m} := ⟨fun x => h x.2.symm⟩
    exact Nat.card_of_isEmpty

private theorem single_listSum_eq_listWeight (size : α → ℕ) :
    (fun l : List α => Finsupp.single () ((l.map size).sum))
      = listWeight (fun a => Finsupp.single () (size a)) := by
  funext l
  rw [listWeight]
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Finsupp.single_add, ih]

theorem ogf_seq (size : α → ℕ) [FiniteSizeFibers size] (h : ∀ a, size a ≠ 0) :
    ogf (fun l : List α => (l.map size).sum)
      = 1 + ogf size * ogf (fun l : List α => (l.map size).sum) := by
  have h' (a : α) : (fun a => Finsupp.single () (size a)) a ≠ 0 := by
    simpa [Finsupp.single_eq_zero] using h a
  have hbridge : ogf (fun l : List α => (l.map size).sum)
      = genFun (listWeight (fun a => Finsupp.single () (size a))) := by
    simp only [ogf, single_listSum_eq_listWeight]
  conv_lhs => rw [hbridge, genFun_listWeight (fun a => Finsupp.single () (size a)) h',
    ← hbridge]
  simp only [ogf]

theorem ogf_eq_tsum (size : α → ℕ) [FiniteSizeFibers size] :
    ogf size = ∑' a, (PowerSeries.X : PowerSeries ℕ) ^ size a := by
  refine (HasSum.tsum_eq ?_).symm
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [PowerSeries.coeff_X_pow, coeff_ogf]
  exact hasSum_count size d

/-- The ordinary GF base-changed into a (semi)ring `R`. -/
noncomputable def ogfMap (R : Type*) [Semiring R] (size : α → ℕ) : PowerSeries R :=
  genFunMap R (fun a => Finsupp.single () (size a))

/-- **The closed form of the ordinary sequence OGF.** Over *any ring* `R`, the sequence
OGF is the inverse of `1 - ogfMap R size`. See `ogfMap_seq_inv` for the `(1 - ·)⁻¹` form
over a field. -/
theorem ogfMap_seq (R : Type*) [Ring R] (size : α → ℕ) [FiniteSizeFibers size]
    (h : ∀ a, size a ≠ 0) :
    ogfMap R (fun l : List α => (l.map size).sum)
      = PowerSeries.invOfUnit (1 - ogfMap R size) 1 := by
  have h' (a : α) : (fun a => Finsupp.single () (size a)) a ≠ 0 := by
    simpa [Finsupp.single_eq_zero] using h a
  have hbridge : ogfMap R (fun l : List α => (l.map size).sum)
      = genFunMap R (listWeight (fun a => Finsupp.single () (size a))) := by
    simp only [ogfMap, single_listSum_eq_listWeight]
  rw [hbridge, genFunMap_listWeight R (fun a => Finsupp.single () (size a)) h']
  rfl

/-- The ordinary sequence OGF closed form in the usual `(1 - A)⁻¹` notation, over a
field. -/
theorem ogfMap_seq_inv (K : Type*) [Field K] (size : α → ℕ) [FiniteSizeFibers size]
    (h : ∀ a, size a ≠ 0) :
    ogfMap K (fun l : List α => (l.map size).sum) = (1 - ogfMap K size)⁻¹ := by
  have h' (a : α) : (fun a => Finsupp.single () (size a)) a ≠ 0 := by
    simpa [Finsupp.single_eq_zero] using h a
  have hbridge : ogfMap K (fun l : List α => (l.map size).sum)
      = genFunMap K (listWeight (fun a => Finsupp.single () (size a))) := by
    simp only [ogfMap, single_listSum_eq_listWeight]
  rw [hbridge, genFunMap_listWeight_inv K (fun a => Finsupp.single () (size a)) h']
  rfl

end Combinatorics

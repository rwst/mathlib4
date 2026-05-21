/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Marking a statistic, and recovering the count by forgetting it

The `markWeight` primitive refines a weight by appending a statistic in fresh
variables; the count of the unmarked class is recovered from the marked
(bivariate) count by summing over the statistic ("grading-aggregation",
needing no power-series substitution).

## Main definitions

* `markWeight wt χ`: append the statistic `χ : α → ι →₀ ℕ` to the weight `wt`.

## Main results

* `instFiniteFibersMarkWeight`: marking preserves finite-fibres.
* `card_markWeight_fiber`: the marked count is the bivariate count.
* `card_eq_tsum_markWeight`: summing over the statistic returns the original count.
-/

@[expose] public section

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

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

/-- **The marking primitive.** Refine the weight by a statistic `χ : α → (ι →₀ ℕ)`,
appending it in fresh variables: `markWeight wt χ a = sumElim (wt a) (χ a)` in
`(σ ⊕ ι) →₀ ℕ`. -/
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

/-- The marked count is the bivariate (refined) count: objects of weight `e` and statistic `d`. -/
theorem card_markWeight_fiber (wt : α → σ →₀ ℕ) (χ : α → ι →₀ ℕ) (e : σ →₀ ℕ)
    (d : ι →₀ ℕ) :
    Nat.card {a // markWeight wt χ a = Finsupp.sumElim e d}
      = Nat.card {a // wt a = e ∧ χ a = d} := by
  simp only [markWeight]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  exact sumElim_inj_iff (wt a) e (χ a) d

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

/-- The count is recovered from the marked (bivariate) counts by forgetting the mark. -/
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

end Combinatorics

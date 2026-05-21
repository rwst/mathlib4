/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.RingTheory.MvPowerSeries.PiTopology

/-!
# The weighted GF as a sum over elements

The Flajolet–Sedgewick defining form `A = ∑_{a} X^(wt a)` of the weighted GF,
proved as a `HasSum` in the coefficientwise (discrete) product topology
`MvPowerSeries.WithPiTopology`. Summability is exactly the `FiniteFibers`
side-condition.
-/

@[expose] public section

open scoped MvPowerSeries.WithPiTopology

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

/-- A finitely-fibred indicator sums (in the discrete topology on `ℕ`) to the cardinality
of the fibre: `∑_{a} [g a = d] = #{a : g a = d}`. -/
theorem hasSum_count {α β : Type*} [DecidableEq β] (g : α → β) (d : β)
    [Finite {a : α // g a = d}] :
    HasSum (fun a : α => if d = g a then (1 : ℕ) else 0) (Nat.card {a : α // g a = d}) := by
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

/-- The weighted GF is the sum of the weight monomials `X^(wt a)` over all objects. -/
theorem genFun_eq_tsum (wt : α → σ →₀ ℕ) [FiniteFibers wt] :
    genFun wt = ∑' a, MvPowerSeries.monomial (wt a) (1 : ℕ) := by
  classical
  refine (HasSum.tsum_eq ?_).symm
  rw [MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [MvPowerSeries.coeff_monomial, coeff_genFun]
  exact hasSum_count wt d

end Combinatorics

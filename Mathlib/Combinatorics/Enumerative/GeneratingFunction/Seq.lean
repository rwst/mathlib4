/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Set.Finite.List

/-!
# The sequence class — weight and finiteness of fibres

The weight of a sequence (`List α`, weight = sum of entry weights) and the proof
that fibres are finite when no atom has weight `0`: a weight-`d` sequence has
length bounded by the total degree of `d`, and every entry has weight `≤ d`.

## Main definitions

* `listWeight`: the weight of a sequence is the sum of entry weights.

## Main results

* `length_le_deg_map`: a sequence's length is bounded by its weight degree.
* `finite_listWeight_fiber` / `finiteFibers_listWeight`: fibres are finite under
  the side-condition `∀ a, wt a ≠ 0`.
-/

@[expose] public section

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

/-- The total degree of an exponent vector `d`, as a function of `d` alone: the
sum of all its exponents. Used as a length bound for weight-`d` sequences. -/
private noncomputable def tdeg (d : σ →₀ ℕ) : ℕ := Multiset.card (Finsupp.toMultiset d)

private theorem deg_eq_tdeg (wt : α → σ →₀ ℕ) (a : α) : deg wt a = tdeg (wt a) := by
  rw [tdeg, Finsupp.card_toMultiset, deg]
  rfl

private theorem tdeg_add (x y : σ →₀ ℕ) : tdeg (x + y) = tdeg x + tdeg y := by
  simp [tdeg]

private theorem tdeg_zero : tdeg (0 : σ →₀ ℕ) = 0 := rfl

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

/-- The sequence class has finite fibres when no object has weight `0`. -/
theorem finiteFibers_listWeight (wt : α → σ →₀ ℕ) [FiniteFibers wt] (h : ∀ a, wt a ≠ 0) :
    FiniteFibers (listWeight wt) :=
  ⟨fun d => finite_listWeight_fiber wt h d⟩

end Combinatorics

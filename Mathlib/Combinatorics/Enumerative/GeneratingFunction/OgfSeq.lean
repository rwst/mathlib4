/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.MapSeq
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Ogf
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Ordinary GF of the sequence class, and its closed form

The `σ = Unit` specialisations of `genFun_listWeight`, `genFunMap_listWeight`,
`genFunMap_listWeight_inv`: the sequence functional equation `S = 1 + A · S` (over `ℕ`),
the closed form `invOfUnit (1 - A) 1` (over any ring), and the `(1 - A)⁻¹` form
(over a field).

## Main definitions

* `ogfMap`: the ordinary GF base-changed into a (semi)ring `R`.

## Main results

* `ogf_seq`: the sequence functional equation over `ℕ`.
* `ogfMap_seq` / `ogfMap_seq_inv`: closed forms over any ring / field.
-/

@[expose] public section

universe u

namespace Combinatorics

variable {α : Type u}

private theorem single_listSum_eq_listWeight (size : α → ℕ) :
    (fun l : List α => Finsupp.single () ((l.map size).sum))
      = listWeight (fun a => Finsupp.single () (size a)) := by
  funext l
  rw [listWeight]
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Finsupp.single_add, ih]

private theorem single_size_ne_zero {size : α → ℕ} (h : ∀ a, size a ≠ 0) (a : α) :
    Finsupp.single () (size a) ≠ 0 := by simpa [Finsupp.single_eq_zero] using h a

/-- **The sequence functional equation, over `ℕ`.** -/
theorem ogf_seq (size : α → ℕ) [FiniteSizeFibers size] (h : ∀ a, size a ≠ 0) :
    ogf (fun l : List α => (l.map size).sum)
      = 1 + ogf size * ogf (fun l : List α => (l.map size).sum) := by
  simp only [ogf, single_listSum_eq_listWeight]
  exact genFun_listWeight _ (single_size_ne_zero h)

/-- The ordinary GF base-changed into a (semi)ring `R`. -/
noncomputable def ogfMap (R : Type*) [Semiring R] (size : α → ℕ) : PowerSeries R :=
  genFunMap R (fun a => Finsupp.single () (size a))

/-- **The closed form of the ordinary sequence OGF.** -/
theorem ogfMap_seq (R : Type*) [Ring R] (size : α → ℕ) [FiniteSizeFibers size]
    (h : ∀ a, size a ≠ 0) :
    ogfMap R (fun l : List α => (l.map size).sum)
      = PowerSeries.invOfUnit (1 - ogfMap R size) 1 := by
  simp only [ogfMap, single_listSum_eq_listWeight]
  exact genFunMap_listWeight R _ (single_size_ne_zero h)

/-- The ordinary sequence OGF closed form in the usual `(1 - A)⁻¹` notation, over a
field. -/
theorem ogfMap_seq_inv (K : Type*) [Field K] (size : α → ℕ) [FiniteSizeFibers size]
    (h : ∀ a, size a ≠ 0) :
    ogfMap K (fun l : List α => (l.map size).sum) = (1 - ogfMap K size)⁻¹ := by
  simp only [ogfMap, single_listSum_eq_listWeight]
  exact genFunMap_listWeight_inv K _ (single_size_ne_zero h)

end Combinatorics

/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Atom
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Prod
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Seq
public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Sum

/-!
# The weighted GF functional equation for sequences

The cons decomposition `SEQ(𝒜) ≅ ε ⊕ 𝒜 × SEQ(𝒜)`, read off via `genFun_congr`,
`genFun_sum`, `genFun_prod`, `genFun_atomWeight_zero`, gives the symbolic method's
sequence functional equation `S = 1 + A · S` (over `ℕ`).

## Main results

* `listConsEquiv`: the cons decomposition.
* `genFun_listWeight`: the sequence functional equation.
-/

@[expose] public section

universe u w

namespace Combinatorics

variable {α : Type u} {σ : Type w}

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
  conv_lhs => rw [hcongr, genFun_sum, genFun_prod, genFun_atomWeight_zero]

end Combinatorics

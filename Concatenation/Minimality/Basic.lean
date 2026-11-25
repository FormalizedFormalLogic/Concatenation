module

public import Concatenation.BT.Basic
public import Concatenation.Coding
public import Concatenation.D.Basic
public import Concatenation.ToFoundation.Decidability

/-!
# Axioms of $\mathsf{D}$, $\mathsf{ID}$ and $\mathsf{BT}$

The axioms of $\mathsf{D}$, $\mathsf{ID}$ and $\mathsf{BT}$ whose removal is studied, as sentences.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation

/-- The axiom on the prefixes of $y0$. -/
def prefixConcatZero : Sentence ℒ⌢⊑ :=
  “∀ x y, x ⊑ y ⌢ !!(op(0).const) ↔ x = y ⌢ !!(op(0).const) ∨ x ⊑ y”

lemma prefixConcatZero_mem_D : prefixConcatZero ∈ 𝗗 := IsDAxiom.prefixConcatZero

/-- The axiom on the prefixes of $y1$. -/
def prefixConcatOne : Sentence ℒ⌢⊑ :=
  “∀ x y, x ⊑ y ⌢ !!(op(1).const) ↔ x = y ⌢ !!(op(1).const) ∨ x ⊑ y”

lemma prefixConcatOne_mem_D : prefixConcatOne ∈ 𝗗 := IsDAxiom.prefixConcatOne

section

variable {L : Language} [L.Zero] [L.One] [L.Concat] [L.Eq]

/-- Associativity of the concatenation. -/
def concatAssoc : Sentence L := “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”

/-- Right cancellation for the letters. -/
def concatRightCancel : Sentence L :=
  “∀ x y, x ≠ y →
    x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”

/-- A string does not end with both letters. -/
def concatZeroNeConcatOne : Sentence L :=
  “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”

end

lemma concatRightCancel_mem_ID : concatRightCancel ∈ 𝗜𝗗 := IsIDAxiom.concatRightCancel

lemma concatZeroNeConcatOne_mem_ID : concatZeroNeConcatOne ∈ 𝗜𝗗 := IsIDAxiom.concatZeroNeConcatOne

lemma concatAssoc_mem_BT : concatAssoc ∈ 𝗕𝗧 := IsBTAxiom.concatAssoc

lemma concatRightCancel_mem_BT : concatRightCancel ∈ 𝗕𝗧 := IsBTAxiom.concatRightCancel

lemma concatZeroNeConcatOne_mem_BT : concatZeroNeConcatOne ∈ 𝗕𝗧 := IsBTAxiom.concatZeroNeConcatOne

end Concatenation

end FFL.FirstOrder

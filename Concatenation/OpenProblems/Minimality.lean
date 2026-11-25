module

public import Concatenation.BT.Basic
public import Concatenation.Coding
public import Concatenation.D.Basic
public import Concatenation.ToFoundation.Decidability
import Concatenation.OpenProblem

/-!
# Open problems on minimal essentially undecidable theories

The theories $\mathsf{D}$, $\mathsf{ID}$ and $\mathsf{BT}$ without one of their axioms.
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

/--
Is $\mathsf{D} - \mathsf{D}_5$, without the axiom
$x \preceq y0 \leftrightarrow x = y0 \lor x \preceq y$, not essentially undecidable?
- [Mur22, Open Problem 2]
-/
open_problem not_essentiallyUndecidable_D_diff_prefixConcatZero :=
  ¬(𝗗 \ {prefixConcatZero} : Theory ℒ⌢⊑).EssentiallyUndecidable

/--
Is $\mathsf{D} - \mathsf{D}_6$, without the axiom
$x \preceq y1 \leftrightarrow x = y1 \lor x \preceq y$, not essentially undecidable?
- [Mur22, Open Problem 2]
-/
open_problem not_essentiallyUndecidable_D_diff_prefixConcatOne :=
  ¬(𝗗 \ {prefixConcatOne} : Theory ℒ⌢⊑).EssentiallyUndecidable

/--
Is $\mathsf{ID}$, also called $\mathsf{C}$, not essentially undecidable without the axiom
$x \neq y \to x0 \neq y0 \land x1 \neq y1$?
- [Mur22, Open Problem 3]
-/
open_problem not_essentiallyUndecidable_ID_diff_concatRightCancel :=
  ¬(𝗜𝗗 \ {concatRightCancel} : Theory ℒ⌢⊑).EssentiallyUndecidable

/--
Is $\mathsf{ID}$, also called $\mathsf{C}$, not essentially undecidable without the axiom
$x0 \neq y1$?
- [Mur22, Open Problem 3]
-/
open_problem not_essentiallyUndecidable_ID_diff_concatZeroNeConcatOne :=
  ¬(𝗜𝗗 \ {concatZeroNeConcatOne} : Theory ℒ⌢⊑).EssentiallyUndecidable

/--
Is $\mathsf{BT}$ not essentially undecidable without the axiom $(xy)z = x(yz)$?
- [Mur22, Open Problem 3]
-/
open_problem not_essentiallyUndecidable_BT_diff_concatAssoc :=
  ¬(𝗕𝗧 \ {concatAssoc} : Theory ℒ⌢).EssentiallyUndecidable

/--
Is $\mathsf{BT}$ not essentially undecidable without the axiom
$x \neq y \to x0 \neq y0 \land x1 \neq y1$?
- [Mur22, Open Problem 3]
-/
open_problem not_essentiallyUndecidable_BT_diff_concatRightCancel :=
  ¬(𝗕𝗧 \ {concatRightCancel} : Theory ℒ⌢).EssentiallyUndecidable

/--
Is $\mathsf{BT}$ not essentially undecidable without the axiom $x0 \neq y1$?
- [Mur22, Open Problem 3]
-/
open_problem not_essentiallyUndecidable_BT_diff_concatZeroNeConcatOne :=
  ¬(𝗕𝗧 \ {concatZeroNeConcatOne} : Theory ℒ⌢).EssentiallyUndecidable

end Concatenation

end FFL.FirstOrder

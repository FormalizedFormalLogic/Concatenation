module

public import Concatenation.Language
public import Foundation.FirstOrder.LK.Eq

/-!
# Damnjanovic's theory of concatenation $\mathsf{QT}^+$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/-- The successor of a string. -/
def successor : Semiterm ℒ⌢ₛ Empty 1 := Semiterm.func (Sum.inr Language.SuccessorFunc.succ) ![#0]

/--
Axioms of the theory of concatenation $\mathsf{QT}^+$ of nonempty strings over two letters.
- [Dam17, §1]
- [Dam17a, §1]
-/
inductive IsQTPlusAxiom : Sentence ℒ⌢ₛ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₛ, IsQTPlusAxiom φ
  | concatAssoc : IsQTPlusAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatNeLetter : IsQTPlusAxiom
      “∀ x y, x ⌢ y ≠ !!(op(0).const) ∧ x ⌢ y ≠ !!(op(1).const)”
  | letterCancel : IsQTPlusAxiom
      “∀ x y,
        (x ⌢ !!(op(0).const) = y ⌢ !!(op(0).const) → x = y) ∧
        (x ⌢ !!(op(1).const) = y ⌢ !!(op(1).const) → x = y) ∧
        (!!(op(0).const) ⌢ x = !!(op(0).const) ⌢ y → x = y) ∧
        (!!(op(1).const) ⌢ x = !!(op(1).const) ⌢ y → x = y)”
  | letterNe : IsQTPlusAxiom
      “∀ x y, !!(op(0).const) ⌢ x ≠ !!(op(1).const) ⌢ y ∧
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | cases : IsQTPlusAxiom
      “∀ x, x = !!(op(0).const) ∨ x = !!(op(1).const) ∨
        ((∃ y, !!(op(0).const) ⌢ y = x ∨ !!(op(1).const) ⌢ y = x) ∧
        ∃ z, z ⌢ !!(op(0).const) = x ∨ z ⌢ !!(op(1).const) = x)”
  | successor : IsQTPlusAxiom
      “∀ x y, !successor x = y ↔
        ((x = !!(op(0).const) ∧ y = !!(op(1).const)) ∨
        (x ≠ !!(op(0).const) ∧ x ⌢ !!(op(1).const) = y))”

/--
The theory of concatenation $\mathsf{QT}^+$.
- [Dam17, §1]
- [Dam17a, §1]
-/
abbrev QTPlus : Theory ℒ⌢ₛ := Set.ofPred IsQTPlusAxiom

@[inherit_doc]
notation "𝗤𝗧⁺" => QTPlus

instance : 𝗘𝗤 ℒ⌢ₛ ⪯ 𝗤𝗧⁺ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsQTPlusAxiom.equal φ hφ

/--
`x` is an initial segment of `y`: `x` is $0$ and `y` is not, or `y` extends `x`.
- [Dam17, §1]
- [Dam17a, §1]
-/
def isInitialSegment : Semisentence ℒ⌢ₛ 2 :=
  “x y. (x = !!(op(0).const) ∧ y ≠ !!(op(0).const)) ∨ ∃ z, x ⌢ z = y”

end FFL.FirstOrder.Concatenation

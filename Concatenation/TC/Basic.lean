module

public import Concatenation.Language
public import Foundation.FirstOrder.LK.Eq

/-!
# Grzegorczyk's theory of concatenation $\mathsf{TC}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of Grzegorczyk's theory of concatenation of nonempty strings over two letters.
- [GZ08, §1]
- [Vis09, §2]
-/
inductive IsTCAxiom : ConcatenationSentence → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsTCAxiom φ
  | concatAssoc : IsTCAxiom “∀ x y z, x ⌢ (y ⌢ z) = (x ⌢ y) ⌢ z”
  | editor : IsTCAxiom “∀ x y z w, x ⌢ y = z ⌢ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ⌢ u = z ∧ y = u ⌢ w) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”
  | zeroNeConcat : IsTCAxiom “∀ x y, !!(op(0).const) ≠ x ⌢ y”
  | oneNeConcat : IsTCAxiom “∀ x y, !!(op(1).const) ≠ x ⌢ y”
  | zeroNeOne : IsTCAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
Grzegorczyk's theory of concatenation.
- [GZ08, §1]
-/
abbrev TC : ConcatenationTheory := Set.ofPred IsTCAxiom

@[inherit_doc]
notation "𝗧𝗖" => TC

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗧𝗖 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsTCAxiom.equal φ hφ

end FFL.FirstOrder.Concatenation

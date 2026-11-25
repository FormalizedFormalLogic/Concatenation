module

public import Concatenation.Language
public import Foundation.FirstOrder.LK.Eq

/-!
# The theory of concatenation $\mathsf{TC}$ with the empty string
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the theory of concatenation with the empty string.
- [HH14, Definition 1]
- [Vis09, §2]
-/
inductive IsTCEmptyAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsTCEmptyAxiom φ
  | emptyConcat : IsTCEmptyAxiom “∀ x, ⋆ ⌢ x = x”
  | concatEmpty : IsTCEmptyAxiom “∀ x, x ⌢ ⋆ = x”
  | concatAssoc : IsTCEmptyAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor : IsTCEmptyAxiom “∀ x y s t, x ⌢ y = s ⌢ t →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | zeroNeEmpty : IsTCEmptyAxiom “!!(op(0).const) ≠ ⋆”
  | zeroAtom : IsTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(0).const) → x = ⋆ ∨ y = ⋆”
  | oneNeEmpty : IsTCEmptyAxiom “!!(op(1).const) ≠ ⋆”
  | oneAtom : IsTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(1).const) → x = ⋆ ∨ y = ⋆”
  | zeroNeOne : IsTCEmptyAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The theory of concatenation with the empty string.
- [HH14, Definition 1]
- [Vis09, §2]
-/
abbrev TCEmpty : Theory ℒ⌢ₑ := Set.ofPred IsTCEmptyAxiom

@[inherit_doc]
notation "𝗧𝗖ₑ" => TCEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗧𝗖ₑ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsTCEmptyAxiom.equal φ hφ

end FFL.FirstOrder.Concatenation

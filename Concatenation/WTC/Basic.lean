module

public import Concatenation.Biteral
public import Foundation.FirstOrder.LK.Eq

/-!
# The weak theory of concatenation $\mathsf{WTC}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the weak theory of concatenation without the empty string.
- [HH14, Definition 5]
- [Mur22, §1]
-/
inductive IsWTCAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsWTCAxiom φ
  | concatAssoc (u : FreeSemigroup Bool) : IsWTCAxiom
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteral u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteral u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : FreeSemigroup Bool) : IsWTCAxiom
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteral u) →
      (x = s ∧ y = t) ∨ ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | concatNeZero : IsWTCAxiom “∀ x y, x ⌢ y ≠ !!(op(0).const)”
  | concatNeOne : IsWTCAxiom “∀ x y, x ⌢ y ≠ !!(op(1).const)”
  | zeroNeOne : IsWTCAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The weak theory of concatenation without the empty string.
- [HH14, Definition 5]
- [Mur22, §1]
-/
abbrev WTC : ConcatenationTheory := Set.ofPred IsWTCAxiom

@[inherit_doc]
notation "𝗪𝗧𝗖" => WTC

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗪𝗧𝗖 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCAxiom.equal φ hφ

/--
Axioms of the weak theory of concatenation with the empty string.
- [HH14, Definition 2]
-/
inductive IsWTCEmptyAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsWTCEmptyAxiom φ
  | emptyUnit (u : List Bool) : IsWTCEmptyAxiom
      “∀ x, !isSubstring x !!(biteralEmpty u) → x ⌢ ⋆ = x ∧ ⋆ ⌢ x = x”
  | concatAssoc (u : List Bool) : IsWTCEmptyAxiom
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteralEmpty u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteralEmpty u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : List Bool) : IsWTCEmptyAxiom
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteralEmpty u) →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | zeroNeEmpty : IsWTCEmptyAxiom “!!(op(0).const) ≠ ⋆”
  | zeroAtom : IsWTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(0).const) → x = ⋆ ∨ y = ⋆”
  | oneNeEmpty : IsWTCEmptyAxiom “!!(op(1).const) ≠ ⋆”
  | oneAtom : IsWTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(1).const) → x = ⋆ ∨ y = ⋆”
  | zeroNeOne : IsWTCEmptyAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The weak theory of concatenation with the empty string.
- [HH14, Definition 2]
-/
abbrev WTCEmpty : ConcatenationEmptyTheory := Set.ofPred IsWTCEmptyAxiom

@[inherit_doc]
notation "𝗪𝗧𝗖ₑ" => WTCEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗪𝗧𝗖ₑ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCEmptyAxiom.equal φ hφ

end FFL.FirstOrder.Concatenation

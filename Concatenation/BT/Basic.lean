module

public import Concatenation.Biteral
public import Foundation.FirstOrder.LK.Eq

/-!
# The theories $\mathsf{WBT}$, $\mathsf{BT}$ and $\mathsf{BTQ}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the weakest $\Sigma_1$-complete theory of concatenation $\mathsf{WBT}$.
- [Mur22, §2]
-/
inductive IsWBTAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsWBTAxiom φ
  | concat (α β : FreeSemigroup Bool) : IsWBTAxiom
      “!!(biteral α) ⌢ !!(biteral β) = !!(biteral (α * β))”
  | ne (α β : FreeSemigroup Bool) (h : α ≠ β) : IsWBTAxiom “!!(biteral α) ≠ !!(biteral β)”
  | substring (α : FreeSemigroup Bool) : IsWBTAxiom
      “∀ x, !isSubstring x !!(biteral α) → !(isOneOf α.substrings) x”

/--
The weakest $\Sigma_1$-complete theory of concatenation $\mathsf{WBT}$.
- [Mur22, §2]
-/
abbrev WBT : Theory ℒ⌢ := Set.ofPred IsWBTAxiom

@[inherit_doc]
notation "𝗪𝗕𝗧" => WBT

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗪𝗕𝗧 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWBTAxiom.equal φ hφ

/--
Axioms of the theory $\mathsf{BT}$, also called $\mathsf{ID}^*$.
- [Mur22, §2]
- [Mur24, §1]
-/
inductive IsBTAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsBTAxiom φ
  | concatAssoc : IsBTAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatRightCancel : IsBTAxiom
      “∀ x y, x ≠ y →
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”
  | concatZeroNeConcatOne : IsBTAxiom “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | substring (α : FreeSemigroup Bool) : IsBTAxiom
      “∀ x, !isSubstring x !!(biteral α) → !(isOneOf α.substrings) x”

/--
The theory $\mathsf{BT}$, also called $\mathsf{ID}^*$.
- [Mur22, §2]
- [Mur24, §1]
-/
abbrev BT : Theory ℒ⌢ := Set.ofPred IsBTAxiom

@[inherit_doc]
notation "𝗕𝗧" => BT

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗕𝗧 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsBTAxiom.equal φ hφ

/--
Axioms of the theory $\mathsf{BTQ}$.
- [Mur22, §2]
-/
inductive IsBTQAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsBTQAxiom φ
  | concatAssoc : IsBTQAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatRightCancel : IsBTQAxiom
      “∀ x y, x ≠ y →
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”
  | concatZeroNeConcatOne : IsBTQAxiom “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | cases : IsBTQAxiom
      “∀ x, x = !!(op(0).const) ∨ x = !!(op(1).const) ∨
        ∃ y, x = y ⌢ !!(op(0).const) ∨ x = y ⌢ !!(op(1).const)”

/--
The theory $\mathsf{BTQ}$.
- [Mur22, §2]
-/
abbrev BTQ : Theory ℒ⌢ := Set.ofPred IsBTQAxiom

@[inherit_doc]
notation "𝗕𝗧𝗤" => BTQ

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗕𝗧𝗤 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsBTQAxiom.equal φ hφ

end FFL.FirstOrder.Concatenation

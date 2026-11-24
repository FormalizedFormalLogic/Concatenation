module

public import Concatenation.Biteral
public import Foundation.FirstOrder.LK.Eq

/-!
# The theories $\mathsf{WD}$, $\mathsf{ID}$ and $\mathsf{D}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the weakest $\Sigma_1$-complete theory $\mathsf{WD}$ of concatenation and prefixes.
- [Mur22, §2]
-/
inductive IsWDAxiom : Sentence ℒ⌢⊑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢⊑, IsWDAxiom φ
  | concat (α β : FreeSemigroup Bool) : IsWDAxiom
      “!!(biteral α) ⌢ !!(biteral β) = !!(biteral (α * β))”
  | ne (α β : FreeSemigroup Bool) (h : α ≠ β) : IsWDAxiom “!!(biteral α) ≠ !!(biteral β)”
  | pref (α : FreeSemigroup Bool) : IsWDAxiom “∀ x, x ⊑ !!(biteral α) ↔ !(isOneOf α.prefixes) x”

/--
The weakest $\Sigma_1$-complete theory $\mathsf{WD}$ of concatenation and prefixes.
- [Mur22, §2]
-/
abbrev WD : ConcatenationPrefixTheory := Set.ofPred IsWDAxiom

@[inherit_doc]
notation "𝗪𝗗" => WD

instance : 𝗘𝗤 ℒ⌢⊑ ⪯ 𝗪𝗗 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWDAxiom.equal φ hφ

/--
Axioms of the theory $\mathsf{ID}$, also called $\mathsf{C}$.
- [Mur22, §2]
- [Mur24, §1]
-/
inductive IsIDAxiom : Sentence ℒ⌢⊑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢⊑, IsIDAxiom φ
  | concatAssoc : IsIDAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatRightCancel : IsIDAxiom
      “∀ x y, x ≠ y →
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”
  | concatZeroNeConcatOne : IsIDAxiom “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | pref (α : FreeSemigroup Bool) : IsIDAxiom “∀ x, x ⊑ !!(biteral α) ↔ !(isOneOf α.prefixes) x”

/--
The theory $\mathsf{ID}$, also called $\mathsf{C}$.
- [Mur22, §2]
- [Mur24, §1]
-/
abbrev ID : ConcatenationPrefixTheory := Set.ofPred IsIDAxiom

@[inherit_doc]
notation "𝗜𝗗" => ID

instance : 𝗘𝗤 ℒ⌢⊑ ⪯ 𝗜𝗗 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsIDAxiom.equal φ hφ

/--
Axioms of the theory $\mathsf{D}$, without $\forall x\,[x \sqsubseteq 1 \leftrightarrow x = 1]$.
- [Mur22, §2]
-/
inductive IsDAxiom : Sentence ℒ⌢⊑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢⊑, IsDAxiom φ
  | concatAssoc : IsDAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatRightCancel : IsDAxiom
      “∀ x y, x ≠ y →
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”
  | concatZeroNeConcatOne : IsDAxiom “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | prefixZero : IsDAxiom “∀ x, x ⊑ !!(op(0).const) ↔ x = !!(op(0).const)”
  | prefixConcatZero : IsDAxiom “∀ x y, x ⊑ y ⌢ !!(op(0).const) ↔ x = y ⌢ !!(op(0).const) ∨ x ⊑ y”
  | prefixConcatOne : IsDAxiom “∀ x y, x ⊑ y ⌢ !!(op(1).const) ↔ x = y ⌢ !!(op(1).const) ∨ x ⊑ y”

/--
The theory $\mathsf{D}$, without the axiom $\forall x\,[x \sqsubseteq 1 \leftrightarrow x = 1]$.
- [Mur22, §2]
-/
abbrev D : ConcatenationPrefixTheory := Set.ofPred IsDAxiom

@[inherit_doc]
notation "𝗗" => D

instance : 𝗘𝗤 ℒ⌢⊑ ⪯ 𝗗 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsDAxiom.equal φ hφ

end FFL.FirstOrder.Concatenation

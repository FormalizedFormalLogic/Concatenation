module

public import Concatenation.Seq.Basic

/-!
# The theory of sequences $\mathsf{Seq}^*$ with the editor axiom
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Sequence

/--
Axioms of the theory of sequences $\mathsf{Seq}^*$ with the editor axiom.
- [KM24, §4.2, Figure 4]
-/
inductive IsSeqStarAxiom : SequenceSentence → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⊢, IsSeqStarAxiom φ
  | snocNeEmpty : IsSeqStarAxiom “∀ x y, x ⊢ y ≠ ⋆”
  | snocInj : IsSeqStarAxiom “∀ x₁ x₂ y₁ y₂, x₁ ⊢ x₂ = y₁ ⊢ y₂ → x₁ = y₁ ∧ x₂ = y₂”
  | emptyUnit : IsSeqStarAxiom “∀ x, x ⌢ ⋆ = x ∧ ⋆ ⌢ x = x”
  | concatSnoc : IsSeqStarAxiom “∀ x y z, x ⌢ (y ⊢ z) = (x ⌢ y) ⊢ z”
  | editor : IsSeqStarAxiom
      “∀ x y z w, x ⌢ y = z ⌢ w ↔ ∃ u, (z = x ⌢ u ∧ u ⌢ w = y) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”

/--
The theory of sequences $\mathsf{Seq}^*$ with the editor axiom.
- [KM24, §4.2, Figure 4]
-/
abbrev SeqStar : SequenceTheory := Set.ofPred IsSeqStarAxiom

@[inherit_doc]
notation "𝗦𝗲𝗾⋆" => SeqStar

instance : 𝗘𝗤 ℒ⊢ ⪯ 𝗦𝗲𝗾⋆ := Entailment.WeakerThan.ofSubset IsSeqStarAxiom.equal

end Sequence

end FFL.FirstOrder

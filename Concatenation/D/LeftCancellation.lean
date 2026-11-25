module

public import Concatenation.D.Basic

/-!
# The theory $\overline{\mathsf{ID}}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the theory $\overline{\mathsf{ID}}$: those of $\mathsf{ID}$, and left cancellation for the
letters.
- [Mur24, §1, §3.6]
-/
inductive IsIDLeftAxiom : Sentence ℒ⌢⊑ → Prop
  | id : ∀ φ ∈ 𝗜𝗗, IsIDLeftAxiom φ
  | concatLeftCancel : IsIDLeftAxiom
      “∀ x y, x ≠ y →
        !!(op(0).const) ⌢ x ≠ !!(op(0).const) ⌢ y ∧ !!(op(1).const) ⌢ x ≠ !!(op(1).const) ⌢ y”
  | zeroConcatNeOneConcat : IsIDLeftAxiom “∀ x y, !!(op(0).const) ⌢ x ≠ !!(op(1).const) ⌢ y”

/--
The theory $\overline{\mathsf{ID}}$.
- [Mur24, §1, §3.6]
-/
abbrev IDLeft : Theory ℒ⌢⊑ := Set.ofPred IsIDLeftAxiom

@[inherit_doc]
notation "𝗜𝗗ₗ" => IDLeft

instance : 𝗜𝗗 ⪯ 𝗜𝗗ₗ := Entailment.WeakerThan.ofSubset IsIDLeftAxiom.id

instance : 𝗘𝗤 ℒ⌢⊑ ⪯ 𝗜𝗗ₗ := Entailment.WeakerThan.trans (𝓣 := 𝗜𝗗) inferInstance inferInstance

end FFL.FirstOrder.Concatenation

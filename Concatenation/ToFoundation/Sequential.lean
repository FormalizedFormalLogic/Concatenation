module

public import Concatenation.ToFoundation.Interpretability.Basic
public import Foundation.FirstOrder.SetTheory.Basic.Misc

/-!
# Adjunctive set theory and sequential theories
-/

@[expose] public section

namespace FFL.FirstOrder

namespace SetTheory

/--
Axioms of adjunctive set theory.
- [Mur24a, Figure 2]
- [Mur23, Figure 8.33]
-/
inductive IsASAxiom : Sentence ℒₛₑₜ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, IsASAxiom φ
  | empty : IsASAxiom “∃ x, ∀ y, y ∉ x”
  | adjunction : IsASAxiom “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w ∈ x ∨ w = y”

/--
Adjunctive set theory $\mathsf{AS}$.
- [Mur24a, Figure 2]
- [Mur23, Figure 8.33]
-/
abbrev AS : Theory ℒₛₑₜ := Set.ofPred IsASAxiom

@[inherit_doc]
notation "𝗔𝗦" => AS

instance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗔𝗦 := Entailment.WeakerThan.ofSubset IsASAxiom.equal

end SetTheory

/--
`T` is sequential: it interprets adjunctive set theory on its whole universe, preserving equality.
- [Mur23, Definition 198]
- [KM24, §1, §3]
-/
def Theory.Sequential {L : Language} [L.Eq] (T : Theory L) [𝗘𝗤 _ ⪯ T] : Prop :=
  UnrelativizedInterprets T SetTheory.AS

end FFL.FirstOrder

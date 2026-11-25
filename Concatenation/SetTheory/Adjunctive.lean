module

public import Foundation.FirstOrder.SetTheory.Basic.Misc

/-!
# Adjunctive set theory
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

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

/--
Axioms of the theory $\mathsf{AS}^+$.
- [Mur24a, §4.1]
-/
inductive IsASPlusAxiom : Sentence ℒₛₑₜ → Prop
  | adjunctive : ∀ φ ∈ 𝗔𝗦, IsASPlusAxiom φ
  | remove : IsASPlusAxiom “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w ∈ x ∧ w ≠ y”
  | inter : IsASPlusAxiom “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w ∈ x ∧ w ∈ y”
  | union : IsASPlusAxiom “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w ∈ x ∨ w ∈ y”
  | notUniversal : IsASPlusAxiom “∀ x, ∃ y, y ∉ x”

/--
The theory $\mathsf{AS}^+$: adjunctive set theory with subtraction of an element, binary
intersections and unions, and no universal set.
- [Mur24a, §4.1]
-/
abbrev ASPlus : Theory ℒₛₑₜ := Set.ofPred IsASPlusAxiom

@[inherit_doc]
notation "𝗔𝗦⁺" => ASPlus

instance : 𝗔𝗦 ⪯ 𝗔𝗦⁺ := Entailment.WeakerThan.ofSubset IsASPlusAxiom.adjunctive

instance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗔𝗦⁺ := Entailment.WeakerThan.trans (𝓣 := 𝗔𝗦) inferInstance inferInstance

end FFL.FirstOrder.SetTheory

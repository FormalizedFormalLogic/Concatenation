module

public import Concatenation.Language
public import Foundation.FirstOrder.LK.Eq

/-!
# Theories of building blocks

The theory $\mathsf{BB}$ of parthood, and its variants with weaker axioms on the atoms.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

/--
Language of parthood: equality and the relation `⊑` of being a part.
- [Mur24a, §2]
-/
abbrev parthood : Language := equal.add prefixRel

@[inherit_doc]
notation "ℒ⊑" => parthood

instance : equal.Eq := ⟨EqRel.equal⟩

instance : (ℒ⊑).Prefix := ⟨Sum.inr PrefixRel.pref⟩

end Language

namespace BuildingBlocks

/--
`x` is an atom: it has no proper part.
- [Mur24a, §2.3]
-/
def isAtom : Semisentence ℒ⊑ 1 := “x. ∀ y, y ⊑ x ↔ y = x”

/-- The variables are distinct atoms. -/
def areDistinctAtoms (n : ℕ) : Semisentence ℒ⊑ n :=
  (Matrix.conj fun i : Fin n ↦ “!isAtom #i”) ⋏
    Matrix.conj fun i : Fin n ↦ Matrix.conj fun j : Fin n ↦ if i = j then ⊤ else “#i ≠ #j”

/--
There are `n` distinct atoms.
- [Mur24a, §5]
-/
def existsAtoms (n : ℕ) : Sentence ℒ⊑ := ∃¹* areDistinctAtoms n

/--
Axioms of composition and of partial order.
- [Mur24a, §2]
-/
inductive IsPartCompositionAxiom : Sentence ℒ⊑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⊑, IsPartCompositionAxiom φ
  | composition : IsPartCompositionAxiom “∀ x y, ∃ z, ∀ w, w ⊑ z ↔ w = z ∨ w ⊑ x ∨ w ⊑ y”
  | refl : IsPartCompositionAxiom “∀ x, x ⊑ x”
  | antisymm : IsPartCompositionAxiom “∀ x y, x ⊑ y ∧ y ⊑ x → x = y”
  | trans : IsPartCompositionAxiom “∀ x y z, x ⊑ y ∧ y ⊑ z → x ⊑ z”

/--
The theory of composition and of partial order, without axioms on the atoms.
- [Mur24a, §2]
-/
abbrev PartComposition : Theory ℒ⊑ := Set.ofPred IsPartCompositionAxiom

/--
The theory $\mathsf{BB}$ of building blocks: for each thing there is an atom which is not a part
of it.
- [Mur24a, §2]
-/
abbrev BB : Theory ℒ⊑ := insert “∀ x, ∃ y, ¬y ⊑ x ∧ !isAtom y” PartComposition

@[inherit_doc]
notation "𝗕𝗕" => BB

/--
The theory $\mathsf{BB}'$: for each thing there is a thing without common part with it.
- [Mur24a, §3.4]
-/
abbrev BBDisjoint : Theory ℒ⊑ := insert “∀ x, ∃ y, ∀ z, z ⊑ y → ¬z ⊑ x” PartComposition

/--
The theory of building blocks with `n` distinct atoms.
- [Mur24a, §5]
-/
abbrev BBAtoms (n : ℕ) : Theory ℒ⊑ := insert (existsAtoms n) PartComposition

/--
The theory $\mathsf{BB}^-$: there are `n` distinct atoms, for each `n`.
- [Mur24a, §5]
-/
abbrev BBMinus : Theory ℒ⊑ := PartComposition ∪ Set.range existsAtoms

@[inherit_doc]
notation "𝗕𝗕⁻" => BBMinus

instance : 𝗘𝗤 ℒ⊑ ⪯ PartComposition :=
  Entailment.WeakerThan.ofSubset IsPartCompositionAxiom.equal

instance : 𝗘𝗤 ℒ⊑ ⪯ 𝗕𝗕 :=
  Entailment.WeakerThan.trans (𝓣 := PartComposition) inferInstance <|
    Entailment.WeakerThan.ofSubset <| Set.subset_insert _ _

instance : 𝗘𝗤 ℒ⊑ ⪯ BBDisjoint :=
  Entailment.WeakerThan.trans (𝓣 := PartComposition) inferInstance <|
    Entailment.WeakerThan.ofSubset <| Set.subset_insert _ _

instance (n : ℕ) : 𝗘𝗤 ℒ⊑ ⪯ BBAtoms n :=
  Entailment.WeakerThan.trans (𝓣 := PartComposition) inferInstance <|
    Entailment.WeakerThan.ofSubset <| Set.subset_insert _ _

instance : 𝗘𝗤 ℒ⊑ ⪯ 𝗕𝗕⁻ :=
  Entailment.WeakerThan.trans (𝓣 := PartComposition) inferInstance <|
    Entailment.WeakerThan.ofSubset Set.subset_union_left

end BuildingBlocks

end FFL.FirstOrder

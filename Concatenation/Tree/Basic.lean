module

public import Concatenation.ToFoundation.Prefix
public import Foundation.FirstOrder.LK.Eq

/-!
# Theories of full binary trees
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

namespace Tree

inductive Func : ℕ → Type
  | empty : Func 0
  | pair : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2
  | subtree : Rel 2

end Tree

/--
Language of full binary trees: the empty tree, the tree with two given immediate subtrees, and the
relation `⊑` of being a subtree.
- [Mur23, §VIII.1]
-/
@[reducible]
def tree : Language where
  Func := Tree.Func
  Rel := Tree.Rel

instance : tree.Eq := ⟨Tree.Rel.eq⟩

instance : tree.Prefix := ⟨Tree.Rel.subtree⟩

namespace UnorderedTree

inductive Rel : ℕ → Type
  | eq : Rel 2
  | subtree : Rel 2
  | pair : Rel 3

end UnorderedTree

/--
Language of unordered full binary trees: the relation of being an unordered pair, and the relation
`⊑` of being a subtree.
- [Mur24a, §3.5]
-/
@[reducible]
def unorderedTree : Language where
  Func := fun _ ↦ Empty
  Rel := UnorderedTree.Rel

instance : unorderedTree.Eq := ⟨UnorderedTree.Rel.eq⟩

instance : unorderedTree.Prefix := ⟨UnorderedTree.Rel.subtree⟩

end Language

namespace Tree

open Language

/-- The empty tree. -/
def empty : ClosedSemiterm tree 0 := Semiterm.func Tree.Func.empty ![]

/-- The tree whose immediate subtrees are `x` and `y`. -/
def pair : ClosedSemiterm tree 2 := Semiterm.func Tree.Func.pair ![#0, #1]

/--
Axioms of the theory $\mathsf{T}$ of full binary trees.
- [Mur24a, Figure 4]
- [Mur23, Figure 8.34]
-/
inductive IsTreeAxiom : Sentence tree → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 tree, IsTreeAxiom φ
  | pairNeEmpty : IsTreeAxiom “∀ x y, !pair x y ≠ !empty”
  | pairInj : IsTreeAxiom “∀ x y z w, !pair x y = !pair z w → x = z ∧ y = w”
  | subtreeEmpty : IsTreeAxiom “∀ x, x ⊑ !empty ↔ x = !empty”
  | subtreePair : IsTreeAxiom “∀ x y z, x ⊑ !pair y z ↔ x = !pair y z ∨ x ⊑ y ∨ x ⊑ z”

/--
The theory $\mathsf{T}$ of full binary trees.
- [Mur24a, Figure 4]
- [Mur23, Figure 8.34]
-/
abbrev TreeTheory : Theory tree := Set.ofPred IsTreeAxiom

/--
The theory $\mathsf{T}^{(1)}$: no tree is a subtree of its left immediate subtree.
- [Mur23, §VIII.1]
-/
abbrev TreeTheoryLeft : Theory tree := insert “∀ x y, ¬!pair x y ⊑ x” TreeTheory

instance : 𝗘𝗤 tree ⪯ TreeTheory := Entailment.WeakerThan.ofSubset IsTreeAxiom.equal

instance : 𝗘𝗤 tree ⪯ TreeTheoryLeft :=
  Entailment.WeakerThan.trans (𝓣 := TreeTheory) inferInstance <|
    Entailment.WeakerThan.ofSubset <| Set.subset_insert _ _

/--
`z` is an unordered pair of `x` and `y`.
- [Mur24a, §3.5]
-/
def isUnorderedPair : Semisentence unorderedTree 3 :=
  Semiformula.rel UnorderedTree.Rel.pair ![#0, #1, #2]

/--
Axioms of the theory $\mathsf{BT}$ of unordered full binary trees.
- [Mur24a, §3.5]
-/
inductive IsUnorderedTreeAxiom : Sentence unorderedTree → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 unorderedTree, IsUnorderedTreeAxiom φ
  | pairInj : IsUnorderedTreeAxiom “∀ x y z v w, !isUnorderedPair z x y → !isUnorderedPair z v w →
      (x = v ∧ y = w) ∨ (x = w ∧ y = v)”
  | pair : IsUnorderedTreeAxiom “∀ x y, ∃ z, !isUnorderedPair z x y ∧ ¬z ⊑ x ∧
      ∀ w, w ⊑ z ↔ w = z ∨ w ⊑ x ∨ w ⊑ y”

/--
The theory $\mathsf{BT}$ of unordered full binary trees.
- [Mur24a, §3.5]
-/
abbrev UnorderedTreeTheory : Theory unorderedTree := Set.ofPred IsUnorderedTreeAxiom

instance : 𝗘𝗤 unorderedTree ⪯ UnorderedTreeTheory :=
  Entailment.WeakerThan.ofSubset IsUnorderedTreeAxiom.equal

end Tree

end FFL.FirstOrder

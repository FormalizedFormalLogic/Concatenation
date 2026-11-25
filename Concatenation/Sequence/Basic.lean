module

public import Foundation.FirstOrder.LK.Eq

/-!
# Theories of finite sequences

The theories $\mathsf{WSeq}$ and $\mathsf{Seq}^*$ of sequences of sequences, with the operation
appending an element and concatenation.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

namespace Sequence

inductive Func : ℕ → Type
  | empty : Func 0
  | snoc : Func 2
  | concat : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end Sequence

/--
Language of the theories of sequences: the empty sequence, the operation appending an element to a
sequence, and concatenation.
- [KM24, §2]
-/
@[reducible]
def sequence : Language where
  Func := Sequence.Func
  Rel := Sequence.Rel

@[inherit_doc]
notation "ℒₛₑ" => sequence

instance : (ℒₛₑ).Eq := ⟨Sequence.Rel.eq⟩

end Language

/--
The finite sequences of finite sequences: the empty one, and the one obtained by appending an
element.
- [KM24, §2]
-/
inductive FiniteSequence
  | empty : FiniteSequence
  | snoc : FiniteSequence → FiniteSequence → FiniteSequence

namespace FiniteSequence

/-- The concatenation of sequences. -/
def concat (s : FiniteSequence) : FiniteSequence → FiniteSequence
  | empty => s
  | snoc t x => snoc (s.concat t) x

/-- The initial segments of a sequence. -/
def initialSegments : FiniteSequence → List FiniteSequence
  | empty => [empty]
  | snoc s x => snoc s x :: s.initialSegments

open Language.Sequence

variable {ξ : Type*} {n : ℕ}

/--
The canonical term of a sequence.
- [KM24, §2]
-/
def sequeral : FiniteSequence → Semiterm ℒₛₑ ξ n
  | empty => Semiterm.func (L := ℒₛₑ) Func.empty ![]
  | snoc s x => Semiterm.func (L := ℒₛₑ) Func.snoc ![s.sequeral, x.sequeral]

end FiniteSequence

namespace Sequence

open Language.Sequence

/-- The empty sequence. -/
def emptyTerm {ξ : Type*} {n : ℕ} : Semiterm ℒₛₑ ξ n := Semiterm.func (L := ℒₛₑ) Func.empty ![]

/-- `x` with `y` appended. -/
def snocTerm : ClosedSemiterm ℒₛₑ 2 := Semiterm.func (L := ℒₛₑ) Func.snoc ![#0, #1]

/-- The concatenation of `x` and `y`. -/
def concatTerm : ClosedSemiterm ℒₛₑ 2 := Semiterm.func (L := ℒₛₑ) Func.concat ![#0, #1]

/--
`x` is an initial segment of `y`.
- [KM24, §2]
-/
def isInitialSegment : Semisentence ℒₛₑ 2 := “x y. ∃ z, !concatTerm x z = y”

/-- `x` is one of the sequences in the list. -/
def isOneOf (l : List FiniteSequence) : Semisentence ℒₛₑ 1 :=
  l.disj' fun t ↦ “x. x = !!t.sequeral”

/--
Axioms of the weak theory of sequences $\mathsf{WSeq}$.
- [KM24, §2, Figure 2]
-/
inductive IsWSeqAxiom : Sentence ℒₛₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₛₑ, IsWSeqAxiom φ
  | ne (s t : FiniteSequence) (h : s ≠ t) : IsWSeqAxiom “!!s.sequeral ≠ !!t.sequeral”
  | concat (s t : FiniteSequence) : IsWSeqAxiom
      “!concatTerm (!!s.sequeral) (!!t.sequeral) = !!(s.concat t).sequeral”
  | initialSegment (s : FiniteSequence) : IsWSeqAxiom
      “∀ x, !isInitialSegment x !!s.sequeral → !(isOneOf s.initialSegments) x”

/--
The weak theory of sequences $\mathsf{WSeq}$.
- [KM24, §2, Figure 2]
-/
abbrev WSeq : Theory ℒₛₑ := Set.ofPred IsWSeqAxiom

@[inherit_doc]
notation "𝗪𝗦𝗲𝗾" => WSeq

instance : 𝗘𝗤 ℒₛₑ ⪯ 𝗪𝗦𝗲𝗾 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWSeqAxiom.equal φ hφ

/--
Axioms of the theory of sequences $\mathsf{Seq}^*$ with the editor axiom.
- [KM24, §4.2, Figure 4]
-/
inductive IsSeqStarAxiom : Sentence ℒₛₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₛₑ, IsSeqStarAxiom φ
  | snocNeEmpty : IsSeqStarAxiom “∀ x y, !snocTerm x y ≠ !!emptyTerm”
  | snocInj : IsSeqStarAxiom
      “∀ x₁ x₂ y₁ y₂, !snocTerm x₁ x₂ = !snocTerm y₁ y₂ → x₁ = y₁ ∧ x₂ = y₂”
  | emptyUnit : IsSeqStarAxiom
      “∀ x, !concatTerm x (!!emptyTerm) = x ∧ !concatTerm (!!emptyTerm) x = x”
  | concatSnoc : IsSeqStarAxiom
      “∀ x y z, !concatTerm x (!snocTerm y z) = !snocTerm (!concatTerm x y) z”
  | editor : IsSeqStarAxiom
      “∀ x y z w, !concatTerm x y = !concatTerm z w ↔
        ∃ u, (z = !concatTerm x u ∧ !concatTerm u w = y) ∨
          (x = !concatTerm z u ∧ !concatTerm u y = w)”

/--
The theory of sequences $\mathsf{Seq}^*$ with the editor axiom.
- [KM24, §4.2, Figure 4]
-/
abbrev SeqStar : Theory ℒₛₑ := Set.ofPred IsSeqStarAxiom

@[inherit_doc]
notation "𝗦𝗲𝗾⋆" => SeqStar

instance : 𝗘𝗤 ℒₛₑ ⪯ 𝗦𝗲𝗾⋆ :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsSeqStarAxiom.equal φ hφ

end Sequence

end FFL.FirstOrder

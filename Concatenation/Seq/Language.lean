module

public import Concatenation.ToFoundation.Concat

/-!
# Language of the theory of sequences

The finite sequences whose entries are finite sequences, and their names in the language of the
theory of sequences.
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
Language of the theory of sequences: the empty sequence, written `⋆` in formulas, the operation
`⊢` that appends an element to a sequence, and concatenation.
- [KM24, §2]
-/
@[reducible]
def sequence : Language where
  Func := Sequence.Func
  Rel := Sequence.Rel

@[inherit_doc]
notation "ℒ⊢" => sequence

namespace Sequence

instance (k) : DecidableEq (Sequence.Func k) := fun a b ↦ by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> {exact instDecidableFalse}

instance (k) : DecidableEq (Sequence.Rel k) := fun a b ↦ by
  rcases a; rcases b; exact .isTrue rfl

instance (k) : Encodable (Sequence.Func k) where
  encode
    | .empty => 0
    | .snoc => 0
    | .concat => 1
  decode e :=
    match k, e with
    | 0, 0 => some .empty
    | 2, 0 => some .snoc
    | 2, 1 => some .concat
    | _, _ => none
  encodek x := by rcases x <;> simp

instance (k) : Encodable (Sequence.Rel k) where
  encode
    | .eq => 0
  decode e :=
    match k, e with
    | 2, 0 => some .eq
    | _, _ => none
  encodek x := by rcases x; simp

instance : (ℒ⊢).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⊢).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⊢).Star := ⟨Func.empty⟩

instance : (ℒ⊢).Concat := ⟨Func.concat⟩

instance : (ℒ⊢).Eq := ⟨Rel.eq⟩

end Sequence

end Language

/-- The operator that appends an element to a sequence, written `t ⊢ u` in formulas. -/
def Semiterm.Operator.snoc : Semiterm.Operator ℒ⊢ 2 :=
  ⟨Semiterm.func Language.Sequence.Func.snoc Semiterm.bvar⟩

syntax:50 first_order_term:50 " ⊢ " first_order_term:51 : first_order_term

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ ⊢ $e₂ ]) =>
    `(Semiterm.Operator.snoc.operator
      ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])

abbrev SequenceTheory := Theory ℒ⊢

abbrev SequenceSemisentence (n : ℕ) := Semisentence ℒ⊢ n

abbrev SequenceSentence := Sentence ℒ⊢

/--
The sequences: the empty sequence `nil`, and the sequence `snoc s t` that has `t` appended to `s`.
- [KM24, §2]
-/
inductive FiniteSequence
  | nil : FiniteSequence
  | protected snoc (s t : FiniteSequence) : FiniteSequence

namespace FiniteSequence

/-- The concatenation of sequences. -/
def append (s : FiniteSequence) : FiniteSequence → FiniteSequence
  | nil => s
  | .snoc t u => (s.append t).snoc u

instance : EmptyCollection FiniteSequence := ⟨nil⟩

instance : Append FiniteSequence := ⟨append⟩

@[simp]
lemma append_nil (s : FiniteSequence) : s ++ nil = s := rfl

@[simp]
lemma append_snoc (s t u : FiniteSequence) : s ++ t.snoc u = (s ++ t).snoc u := rfl

/--
The initial segments of a sequence.
- [KM24, §2]
-/
def prefixes : FiniteSequence → List FiniteSequence
  | nil => [nil]
  | .snoc s t => s.snoc t :: s.prefixes

/--
The canonical term of a sequence.
- [KM24, §2]
-/
def sequeral {ξ : Type*} {n : ℕ} : FiniteSequence → Semiterm ℒ⊢ ξ n
  | nil => ‘⋆’
  | .snoc s t => ‘!!s.sequeral ⊢ !!t.sequeral’

end FiniteSequence

end FFL.FirstOrder

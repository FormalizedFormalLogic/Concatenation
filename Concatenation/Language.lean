module

public import Concatenation.ToFoundation.Concat

/-!
# Language of the theory of concatenation
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

namespace Concatenation

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | concat : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2

end Concatenation

/--
Language of the theory of concatenation: two letters $0$, $1$, and concatenation.
- [GZ08, §1]
- [Mur22, §1]
-/
@[reducible]
def concatenation : Language where
  Func := Concatenation.Func
  Rel := Concatenation.Rel

@[inherit_doc]
notation "ℒ⌢" => concatenation

namespace Concatenation

instance (k) : DecidableEq (Concatenation.Func k) := fun a b ↦ by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> {exact instDecidableFalse}

instance (k) : DecidableEq (Concatenation.Rel k) := fun a b ↦ by
  rcases a; rcases b; exact .isTrue rfl

instance (k) : Encodable (Concatenation.Func k) where
  encode
    | .zero => 0
    | .one => 1
    | .concat => 0
  decode e :=
    match k, e with
    | 0, 0 => some .zero
    | 0, 1 => some .one
    | 2, 0 => some .concat
    | _, _ => none
  encodek x := by rcases x <;> simp

instance (k) : Encodable (Concatenation.Rel k) where
  encode
    | .eq => 0
  decode e :=
    match k, e with
    | 2, 0 => some .eq
    | _, _ => none
  encodek x := by rcases x; simp

instance : (ℒ⌢).DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⌢).Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : (ℒ⌢).Zero := ⟨Func.zero⟩

instance : (ℒ⌢).One := ⟨Func.one⟩

instance : (ℒ⌢).Concat := ⟨Func.concat⟩

instance : (ℒ⌢).Eq := ⟨Rel.eq⟩

end Concatenation

end Language

abbrev ConcatenationTheory := Theory ℒ⌢

abbrev ConcatenationSemiterm (ξ : Type*) (n : ℕ) := Semiterm ℒ⌢ ξ n

abbrev ConcatenationTerm (ξ : Type*) := Term ℒ⌢ ξ

abbrev ConcatenationSemiformula (ξ : Type*) (n : ℕ) := Semiformula ℒ⌢ ξ n

abbrev ConcatenationFormula (ξ : Type*) := Formula ℒ⌢ ξ

abbrev ConcatenationSemisentence (n : ℕ) := Semisentence ℒ⌢ n

abbrev ConcatenationSentence := Sentence ℒ⌢

abbrev ConcatenationSemiproposition (n : ℕ) := Semiproposition ℒ⌢ n

abbrev ConcatenationProposition := Proposition ℒ⌢

variable {ξ : Type*} {n : ℕ} [ToString ξ]

def Semiterm.toStringConcatenation : ConcatenationSemiterm ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  | func Language.One.one _ => "1"
  | func Language.Concat.concat v =>
    s!"({(v 0).toStringConcatenation} ⌢ {(v 1).toStringConcatenation})"

instance : Repr (ConcatenationSemiterm ξ n) := ⟨fun t _ ↦ t.toStringConcatenation⟩

instance : ToString (ConcatenationSemiterm ξ n) := ⟨fun t ↦ t.toStringConcatenation⟩

end FFL.FirstOrder

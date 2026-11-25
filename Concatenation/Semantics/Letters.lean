module

public import Concatenation.Semantics.Standard

/-!
# Semantics of the language of concatenation with arbitrary letters

Structures with a letter for every element of `α` and a concatenation, read as structures for
`ℒ⌢[α]`.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A type with a letter for every element of `α` and a concatenation `++`. -/
class LetterStructure (α : Type) (M : Type*) extends Append M where
  ofLetter : α → M

/-- The structure with two letters that the letters `a` and `b` give. -/
abbrev LetterStructure.concatenationStructure {α : Type} {M : Type*} [LetterStructure α M]
    (a b : α) : ConcatenationStructure M where
  zero := ofLetter a
  one := ofLetter b

namespace Concatenation

open Language LetterStructure

variable {α : Type}

/-- The constant denoting the letter `a`. -/
def letterTerm {ξ : Type*} {n : ℕ} (a : α) : Semiterm ℒ⌢[α] ξ n := .func (.letter a) ![]

section semantics

variable (M : Type*) [LetterStructure α M]

instance lettersModel : Tarski.Structure ℒ⌢[α] M where
  func := fun _ f ↦
    match f with
    | .letter a => fun _ ↦ ofLetter a
    | .concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | .eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢[α] M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Concat ℒ⌢[α] M := ⟨fun _ _ ↦ rfl⟩

variable {M}

@[simp]
lemma val_letterTerm {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M} (a : α) :
    (letterTerm a : Semiterm ℒ⌢[α] ξ n).val e ε = ofLetter a := rfl

end semantics

lemma completeLetters (T : Theory ℒ⌢[α]) [𝗘𝗤 ℒ⌢[α] ⪯ T] (φ : Sentence ℒ⌢[α])
    (H : ∀ (M : Type*) [Nonempty M] [LetterStructure α M] [M↓[ℒ⌢[α]] ⊧* T], M↓[ℒ⌢[α]] ⊧ φ) :
    T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    let c : LetterStructure α M :=
      { ofLetter a := s.func (.letter a) ![]
        append x y := s.func .concat ![x, y] }
    have e : s = lettersModel M :=
      Tarski.Structure.ext
        (funext₃ fun k f v ↦
          match k, f with
          | _, .letter a => congrArg _ <| Matrix.empty_eq v
          | _, .concat => congrArg _ <| Matrix.fun_eq_vec_two v)
        (funext₃ fun k r v ↦
          match k, r with
          | _, .eq => (Tarski.Structure.eq_lang (L := ℒ⌢[α]) (M := M) (v := v)).eq)
    rw [e] at hT ⊢
    exact H M

/-- The nonempty strings of the letters `α` under concatenation. -/
instance : LetterStructure α (FreeSemigroup α) where
  ofLetter := FreeSemigroup.of

end Concatenation

end FFL.FirstOrder

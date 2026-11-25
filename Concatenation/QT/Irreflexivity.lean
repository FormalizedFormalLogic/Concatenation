module

public import Concatenation.QT.Basic
public import Concatenation.Semantics.Standard
public import Foundation.FirstOrder.LK.Soundness
public import Mathlib.Data.Stream.Init

/-!
# Irreflexivity of initial segments in $\mathsf{QT}^+$

A model of $\mathsf{QT}^+$ with a string that is an initial segment of itself.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section semantics

variable {M : Type*} [ConcatenationStructure M] {x y : M}

open scoped Classical in
/--
The successor of a string.
- [Dam17, §1]
-/
noncomputable def succ (x : M) : M := if x = 0 then 1 else x ++ 1

noncomputable instance : Tarski.Structure (Language.ofFunc Language.SuccessorFunc) M :=
  Tarski.Structure.ofFunc Language.SuccessorFunc fun {_} f ↦
    match f with
    | .succ => fun v ↦ succ (v 0)

instance : Tarski.Structure.Eq ℒ⌢ₛ M := ⟨fun _ _ ↦ Iff.rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ₛ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ₛ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ₛ M := ⟨fun _ _ ↦ rfl⟩

@[simp]
lemma val_successor {e : Fin 1 → M} {ε : Empty → M} : successor.val e ε = succ (e 0) := rfl

/--
`x` is an initial segment of `y`: `x` is $0$ and `y` is not, or `y` extends `x`.
- [Dam17, §1]
-/
def IsInitialSegment (x y : M) : Prop := (x = 0 ∧ y ≠ 0) ∨ ∃ z, x ++ z = y

@[simp]
lemma eval_isInitialSegment : M ⊧/![x, y] isInitialSegment ↔ IsInitialSegment x y := by
  simp [isInitialSegment, IsInitialSegment]

end semantics

/--
The nonempty words over two letters, and the pairs of an $\omega$-word and an $\omega^*$-word, the
latter read from its last letter.
-/
inductive EndedWord
  | word (x : FreeSemigroup Bool)
  | ends (u v : Stream' Bool)

namespace EndedWord

/--
The concatenation; that of two pairs keeps the $\omega$-word of the first and the $\omega^*$-word of
the second.
-/
def append : EndedWord → EndedWord → EndedWord
  | word x, word y => word (x * y)
  | word x, ends u v => ends (x.toList ++ₛ u) v
  | ends u v, word x => ends u (x.toList.reverse ++ₛ v)
  | ends u _, ends _ v => ends u v

instance : ConcatenationStructure EndedWord where
  zero := word (.of false)
  one := word (.of true)
  append := append

variable {x y : EndedWord}

/-- The letter `b`. -/
abbrev letter (b : Bool) : EndedWord := word (.of b)

lemma zero_eq : (0 : EndedWord) = letter false := rfl

lemma one_eq : (1 : EndedWord) = letter true := rfl

lemma append_def : x ++ y = x.append y := rfl

protected lemma append_assoc (x y z : EndedWord) : x ++ y ++ z = x ++ (y ++ z) := by
  cases x <;> cases y <;> cases z <;>
    simp [append_def, append, mul_assoc, Stream'.append_append_stream]

@[simp]
lemma append_ne_letter (x y : EndedWord) (b : Bool) : x ++ y ≠ letter b := by
  cases x <;> cases y <;> simp [append_def, append, (FreeSemigroup.of_ne_mul _ _ _).symm]

@[simp]
lemma letter_append_inj {b c : Bool} : letter b ++ x = letter c ++ y ↔ b = c ∧ x = y := by
  cases x <;> cases y <;>
    simp [append_def, append, ← FreeSemigroup.toList_inj, Stream'.cons_injective2.eq_iff, and_assoc]

@[simp]
lemma append_letter_inj {b c : Bool} : x ++ letter b = y ++ letter c ↔ x = y ∧ b = c := by
  cases x <;> cases y <;>
    simp [append_def, append, ← FreeSemigroup.toList_inj, Stream'.cons_injective2.eq_iff,
      and_left_comm, and_comm]

lemma exists_letter_append (x : EndedWord) :
    (∃ b, x = letter b) ∨ ∃ y b, letter b ++ y = x := by
  rcases x with ⟨b, _ | ⟨c, l⟩⟩ | ⟨u, v⟩
  · left; use b; rfl
  · right; use word ⟨c, l⟩, b; rfl
  · right; use ends u.tail v, u.head; simp [append_def, append]

lemma exists_append_letter (x : EndedWord) :
    (∃ b, x = letter b) ∨ ∃ y b, y ++ letter b = x := by
  rcases x with x | ⟨u, v⟩
  · rcases List.eq_nil_or_concat x.toList with h | ⟨l, b, h⟩
    · simp [FreeSemigroup.toList] at h
    · rcases FreeSemigroup.eq_nil_or_exists_toList l with rfl | ⟨y, rfl⟩
      · left; use b; simpa [← FreeSemigroup.toList_inj] using h
      · right; use word y, b
        simp [append_def, append, ← FreeSemigroup.toList_inj, h]
  · right; use ends u v.tail, v.head; simp [append_def, append]

lemma letter_or_letter_append_and_append_letter (x : EndedWord) :
    x = letter false ∨ x = letter true ∨
      ((∃ y, letter false ++ y = x ∨ letter true ++ y = x) ∧
      ∃ z, z ++ letter false = x ∨ z ++ letter true = x) := by
  have h₁ := exists_letter_append x
  have h₂ := exists_append_letter x
  simp only [Bool.exists_bool] at h₁ h₂
  grind

instance : EndedWord↓[ℒ⌢ₛ] ⊧* 𝗤𝗧⁺ := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : EndedWord↓[ℒ⌢ₛ] ⊧* 𝗘𝗤 ℒ⌢ₛ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simpa [models_iff] using EndedWord.append_assoc
  case concatNeLetter => simp [models_iff, zero_eq, one_eq]
  case letterCancel => simp [models_iff, zero_eq, one_eq]
  case letterNe => simp [models_iff, zero_eq, one_eq]
  case cases =>
    simpa [models_iff, zero_eq, one_eq] using letter_or_letter_append_and_append_letter
  case successor =>
    simp [models_iff, Semiterm.val_substs, succ]
    grind⟩

end EndedWord

/--
$\mathsf{QT}^+$ does not prove that no string is an initial segment of itself.
- [Dam17, §2]
- [Dam17a, §2]
-/
theorem unprovable_isInitialSegment_irrefl : 𝗤𝗧⁺ ⊬ “∀ x, ¬!isInitialSegment x x” := by
  apply unprovable_of_countermodel 𝗤𝗧⁺ (M := EndedWord)
  suffices ∃ x : EndedWord, IsInitialSegment x x by simpa [Semantics.NotModels, models_iff]
  use .ends (.const true) (.const true)
  right
  use EndedWord.letter true
  simpa [EndedWord.append_def, EndedWord.append] using
    (Stream'.const_eq true).symm

end FFL.FirstOrder.Concatenation

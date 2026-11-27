module

public import Concatenation.Semantics.Basic
public import Foundation.FirstOrder.LK.Soundness
public import Mathlib.Data.Stream.Init

/-!
# Damnjanovic's theory of concatenation $\mathsf{QT}^+$

The theory $\mathsf{QT}^+$, and a model of it with a string that is an initial segment of itself.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/-- The successor of a string. -/
def successor : Semiterm ℒ⌢ₛ Empty 1 := Semiterm.func (Sum.inr Language.SuccessorFunc.succ) ![#0]

/--
Axioms of the theory of concatenation $\mathsf{QT}^+$ of nonempty strings over two letters.
- [Dam17, §1]
- [Dam17a, §1]
-/
inductive IsQTPlusAxiom : Sentence ℒ⌢ₛ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₛ, IsQTPlusAxiom φ
  | concatAssoc : IsQTPlusAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | concatNeLetter : IsQTPlusAxiom
      “∀ x y, x ⌢ y ≠ !!(op(0).const) ∧ x ⌢ y ≠ !!(op(1).const)”
  | letterCancel : IsQTPlusAxiom
      “∀ x y,
        (x ⌢ !!(op(0).const) = y ⌢ !!(op(0).const) → x = y) ∧
        (x ⌢ !!(op(1).const) = y ⌢ !!(op(1).const) → x = y) ∧
        (!!(op(0).const) ⌢ x = !!(op(0).const) ⌢ y → x = y) ∧
        (!!(op(1).const) ⌢ x = !!(op(1).const) ⌢ y → x = y)”
  | letterNe : IsQTPlusAxiom
      “∀ x y, !!(op(0).const) ⌢ x ≠ !!(op(1).const) ⌢ y ∧
        x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | cases : IsQTPlusAxiom
      “∀ x, x = !!(op(0).const) ∨ x = !!(op(1).const) ∨
        ((∃ y, !!(op(0).const) ⌢ y = x ∨ !!(op(1).const) ⌢ y = x) ∧
        ∃ z, z ⌢ !!(op(0).const) = x ∨ z ⌢ !!(op(1).const) = x)”
  | successor : IsQTPlusAxiom
      “∀ x y, !successor x = y ↔
        ((x = !!(op(0).const) ∧ y = !!(op(1).const)) ∨
        (x ≠ !!(op(0).const) ∧ x ⌢ !!(op(1).const) = y))”

/--
The theory of concatenation $\mathsf{QT}^+$.
- [Dam17, §1]
- [Dam17a, §1]
-/
abbrev QTPlus : Theory ℒ⌢ₛ := Set.ofPred IsQTPlusAxiom

@[inherit_doc]
notation "𝗤𝗧⁺" => QTPlus

instance : 𝗘𝗤 ℒ⌢ₛ ⪯ 𝗤𝗧⁺ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsQTPlusAxiom.equal φ hφ

/--
`x` is an initial segment of `y`: `x` is $0$ and `y` is not, or `y` extends `x`.
- [Dam17, §1]
- [Dam17a, §1]
-/
def isInitialSegment : Semisentence ℒ⌢ₛ 2 :=
  “x y. (x = !!(op(0).const) ∧ y ≠ !!(op(0).const)) ∨ ∃ z, x ⌢ z = y”

section semantics

variable {V : Type*} [ConcatenationStructure V] {x y : V}

open scoped Classical in
/--
The successor of a string.
- [Dam17, §1]
-/
noncomputable def succ (x : V) : V := if x = 0 then 1 else x ++ 1

noncomputable instance : Tarski.Structure (Language.ofFunc Language.SuccessorFunc) V :=
  Tarski.Structure.ofFunc Language.SuccessorFunc fun {_} f ↦
    match f with
    | .succ => fun v ↦ succ (v 0)

instance : Tarski.Structure.Eq ℒ⌢ₛ V := ⟨fun _ _ ↦ Iff.rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ₛ V := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ₛ V := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ₛ V := ⟨fun _ _ ↦ rfl⟩

@[simp]
lemma val_successor {e : Fin 1 → V} {ε : Empty → V} : successor.val e ε = succ (e 0) := rfl

instance isInitialSegment_defined : ℒ⌢ₛ-relation[V] IsInitialSegment via isInitialSegment :=
  ⟨fun v ↦ by simp [isInitialSegment, IsInitialSegment, eq_comm (b := v 1)]⟩

instance isInitialSegment_definable : ℒ⌢ₛ-relation[V] IsInitialSegment :=
  isInitialSegment_defined.to_definable

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

private lemma exists_letter_append (x : EndedWord) :
    (∃ b, x = letter b) ∨ ∃ y b, letter b ++ y = x := by
  rcases x with ⟨b, _ | ⟨c, l⟩⟩ | ⟨u, v⟩
  · left; use b; rfl
  · right; use word ⟨c, l⟩, b; rfl
  · right; use ends u.tail v, u.head; simp [append_def, append]

private lemma exists_append_letter (x : EndedWord) :
    (∃ b, x = letter b) ∨ ∃ y b, y ++ letter b = x := by
  rcases x with x | ⟨u, v⟩
  · rcases List.eq_nil_or_concat x.toList with h | ⟨l, b, h⟩
    · simp [FreeSemigroup.toList] at h
    · rcases FreeSemigroup.eq_nil_or_exists_toList l with rfl | ⟨y, rfl⟩
      · left; use b; simpa [← FreeSemigroup.toList_inj] using h
      · right; use word y, b
        simp [append_def, append, ← FreeSemigroup.toList_inj, h]
  · right; use ends u v.tail, v.head; simp [append_def, append]

private lemma letter_or_letter_append_and_append_letter (x : EndedWord) :
    x = letter false ∨ x = letter true ∨
      ((∃ y, letter false ++ y = x ∨ letter true ++ y = x) ∧
      ∃ z, z ++ letter false = x ∨ z ++ letter true = x) := by
  have h₁ := exists_letter_append x
  have h₂ := exists_append_letter x
  simp only [Bool.exists_bool] at h₁ h₂
  grind

instance : EndedWord↓[ℒ⌢ₛ] ⊧* 𝗤𝗧⁺ := by
  constructor
  intro σ h
  cases h
  case equal hφ =>
    have : EndedWord↓[ℒ⌢ₛ] ⊧* 𝗘𝗤 ℒ⌢ₛ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simpa [models_iff] using EndedWord.append_assoc
  case cases =>
    simpa [models_iff, zero_eq, one_eq] using letter_or_letter_append_and_append_letter
  case successor =>
    simp [models_iff, Semiterm.val_substs, succ]
    grind
  all_goals simp [models_iff, zero_eq, one_eq]

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
  simpa [EndedWord.append_def, EndedWord.append] using Stream'.const_eq true

end FFL.FirstOrder.Concatenation

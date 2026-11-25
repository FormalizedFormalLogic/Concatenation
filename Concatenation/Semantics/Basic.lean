module

public import Concatenation.Biteral
public import Concatenation.TC.Basic
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-!
# Semantics of the language of concatenation

Structures with two letters and a concatenation, read as structures for `ℒ⌢`, and the atoms,
substrings, prefixes, suffixes and tallies in them.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A type with two letters `0`, `1` and a concatenation `++`. -/
class ConcatenationStructure (α : Type*) extends Zero α, One α, Append α

instance {α : Type*} [Zero α] [One α] [Append α] : ConcatenationStructure α where

namespace ConcatenationStructure

variable {α : Type*} [ConcatenationStructure α]

/-- The value of a nonempty binary string, associated to the left. -/
def ofFreeSemigroup (x : FreeSemigroup Bool) : α :=
  x.tail.foldl (fun m b ↦ m ++ if b then 1 else 0) (if x.head then 1 else 0)

end ConcatenationStructure

namespace Concatenation

open Language

section semantics

variable (M : Type*) [ConcatenationStructure M]

instance standardModel : Tarski.Structure ℒ⌢ M where
  func := fun _ f ↦
    match f with
    | Concatenation.Func.zero => fun _ ↦ 0
    | Concatenation.Func.one => fun _ ↦ 1
    | Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ M := ⟨fun _ _ ↦ rfl⟩

lemma standardModel_unique (s : Tarski.Structure ℒ⌢ M) [Tarski.Structure.Zero ℒ⌢ M]
    [Tarski.Structure.One ℒ⌢ M] [Tarski.Structure.Concat ℒ⌢ M] [Tarski.Structure.Eq ℒ⌢ M] :
    s = standardModel M :=
  Tarski.Structure.ext
    (funext₃ fun k f _ ↦
      match k, f with
      | _, Language.Zero.zero => by simp [Matrix.empty_eq]
      | _, Language.One.one => by simp [Matrix.empty_eq]
      | _, Language.Concat.concat => by simp)
    (funext₃ fun k r _ ↦
      match k, r with
      | _, Language.Eq.eq => by simp)

end semantics

lemma complete (T : ConcatenationTheory) [𝗘𝗤 ℒ⌢ ⪯ T] (φ : ConcatenationSentence)
    (H : ∀ (M : Type*) [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* T], M↓[ℒ⌢] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    let c : ConcatenationStructure M :=
      { zero := s.func Language.Zero.zero ![]
        one := s.func Language.One.one ![]
        append a b := s.func Language.Concat.concat ![a, b] }
    have : Tarski.Structure.Zero ℒ⌢ M := ⟨by
      simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq, Matrix.empty_eq]; rfl⟩
    have : Tarski.Structure.One ℒ⌢ M := ⟨by
      simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq, Matrix.empty_eq]; rfl⟩
    have : Tarski.Structure.Concat ℒ⌢ M := ⟨fun a b ↦ rfl⟩
    have e := standardModel_unique M s
    rw [e] at hT ⊢
    exact H M

lemma provable_iff_of_models_iff {T : ConcatenationTheory} [𝗘𝗤 ℒ⌢ ⪯ T] {n}
    {φ ψ : ConcatenationSemisentence n}
    (h : ∀ (V : Type*) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] (e : Fin n → V),
      V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply complete T _
  intro V _ _
  simpa [models_iff] using h V

lemma models_iff_of_provable_iff {T : ConcatenationTheory} [𝗘𝗤 ℒ⌢ ⪯ T] {n}
    {φ ψ : ConcatenationSemisentence n} (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*)
    [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have h' := consequence_iff.mp (Theory.Proof.sound h) V inferInstance
  simp only [models_iff, Semiformula.eval_allClosure] at h'
  simpa using h' e

lemma weakerThan_of_models (T S : ConcatenationTheory) [𝗘𝗤 ℒ⌢ ⪯ S]
    (H : ∀ (M : Type*) [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* S], M↓[ℒ⌢] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ complete _ _ fun M _ _ ↦ Theory.Proof.sound h (H M)

section eval

variable {M : Type*} [ConcatenationStructure M] {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M}

@[simp]
lemma val_letter (b : Bool) : (letter b : Semiterm ℒ⌢ ξ n).val e ε = if b then 1 else 0 := by
  cases b <;> simp [letter]

@[simp]
lemma val_biteral (x : FreeSemigroup Bool) :
    (biteral x : Semiterm ℒ⌢ ξ n).val e ε = ConcatenationStructure.ofFreeSemigroup x := by
  suffices ∀ (l : List Bool) (t : Semiterm ℒ⌢ ξ n),
      (l.foldl (fun t b ↦ ‘!!t ⌢ !!(letter b)’) t).val e ε =
        l.foldl (fun m b ↦ m ++ if b then 1 else 0) (t.val e ε) by
    simp [biteral, ConcatenationStructure.ofFreeSemigroup, this]
  intro l
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

@[simp]
lemma eval_isOneOf {l : List (FreeSemigroup Bool)} {x : M} :
    M ⊧/![x] (isOneOf l : ConcatenationSemisentence 1) ↔
      ∃ γ ∈ l, x = ConcatenationStructure.ofFreeSemigroup γ := by
  simp [isOneOf]

end eval

section substring

variable {M : Type*} [ConcatenationStructure M]

/-- `x` is one of the letters `0` and `1`. -/
def IsAtom (x : M) : Prop := x = 0 ∨ x = 1

/--
`x` is a substring of `y`. Both associations of `u ++ x ++ v` are listed, so that the relation is
the one `isSubstring` defines in any concatenation structure.
- [Gan09, §1, Definition 1]
-/
def IsSubstring (x y : M) : Prop :=
  x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨ (∃ u v, y = (u ++ x) ++ v) ∨
    ∃ u v, y = u ++ (x ++ v)

/--
`x` is a prefix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsPrefix (x y : M) : Prop := x = y ∨ ∃ v, y = x ++ v

/--
`x` is a suffix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsSuffix (x y : M) : Prop := x = y ∨ ∃ u, y = u ++ x

/--
`x` is a `c`-tally: every atom that is a substring of `x` is `c`.
- [Gan09, §1, Definition 1]
-/
def IsTally (c x : M) : Prop := ∀ y, IsAtom y → IsSubstring y x → y = c

/-- `x` is one of the letters `0` and `1`. -/
def isAtom : Semisentence ℒ⌢ 1 := “x. x = !!(op(0).const) ∨ x = !!(op(1).const)”

/-- `x` is a prefix of `y`. -/
def isPrefix : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ v, y = x ⌢ v”

/-- `x` is a suffix of `y`. -/
def isSuffix : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

/-- `x` is a `c`-tally. -/
def isTally : Semisentence ℒ⌢ 2 := “c x. ∀ y, !isAtom y → !isSubstring y x → y = c”

variable {c x y : M}

@[simp]
lemma isAtom_zero : IsAtom (0 : M) := Or.inl rfl

@[simp]
lemma isAtom_one : IsAtom (1 : M) := Or.inr rfl

@[refl, simp]
lemma IsSubstring.refl (x : M) : IsSubstring x x := Or.inl rfl

@[simp]
lemma isSubstring_append_left (x y : M) : IsSubstring x (x ++ y) := by
  right; right; left; use y

@[simp]
lemma isSubstring_append_right (x y : M) : IsSubstring y (x ++ y) := by
  right; left; use x

@[simp]
lemma isSubstring_append_append (u x v : M) : IsSubstring x (u ++ x ++ v) := by
  right; right; right; left; use u, v

@[refl, simp]
lemma IsPrefix.refl (x : M) : IsPrefix x x := Or.inl rfl

@[simp]
lemma isPrefix_append (x y : M) : IsPrefix x (x ++ y) := by
  right; use y

@[refl, simp]
lemma IsSuffix.refl (x : M) : IsSuffix x x := Or.inl rfl

@[simp]
lemma isSuffix_append (x y : M) : IsSuffix y (x ++ y) := by
  right; use x

lemma IsPrefix.isSubstring (h : IsPrefix x y) : IsSubstring x y := by
  rcases h with rfl | ⟨v, rfl⟩ <;> simp

lemma IsSuffix.isSubstring (h : IsSuffix x y) : IsSubstring x y := by
  rcases h with rfl | ⟨u, rfl⟩ <;> simp

@[simp]
lemma eval_isAtom : M ⊧/![x] isAtom ↔ IsAtom x := by simp [isAtom, IsAtom]

@[simp]
lemma eval_isSubstring : M ⊧/![x, y] (isSubstring : Semisentence ℒ⌢ 2) ↔ IsSubstring x y := by
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := y)]

@[simp]
lemma eval_isPrefix : M ⊧/![x, y] isPrefix ↔ IsPrefix x y := by
  simp [isPrefix, IsPrefix]

@[simp]
lemma eval_isSuffix : M ⊧/![x, y] isSuffix ↔ IsSuffix x y := by
  simp [isSuffix, IsSuffix]

@[simp]
lemma eval_isTally : M ⊧/![c, x] isTally ↔ IsTally c x := by
  simp [isTally, IsTally]

end substring

section TC

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖]

protected lemma append_assoc (a b c : M) : a ++ b ++ c = a ++ (b ++ c) := by
  have := by simpa [models_iff] using Theory.models M _ IsTCAxiom.concatAssoc
  exact (this a b c).symm

lemma editor {a b c d : M} (h : a ++ b = c ++ d) :
    (a = c ∧ b = d) ∨ ∃ u, (a ++ u = c ∧ b = u ++ d) ∨ (a = c ++ u ∧ u ++ b = d) := by
  have := by simpa [models_iff] using Theory.models M _ IsTCAxiom.editor
  exact this a b c d h

@[simp]
lemma zero_ne_append (a b : M) : 0 ≠ a ++ b := by
  have := by simpa [models_iff] using Theory.models M _ IsTCAxiom.zeroNeConcat
  exact this a b

@[simp]
lemma one_ne_append (a b : M) : 1 ≠ a ++ b := by
  have := by simpa [models_iff] using Theory.models M _ IsTCAxiom.oneNeConcat
  exact this a b

@[simp]
protected lemma zero_ne_one : (0 : M) ≠ 1 := by
  simpa [models_iff] using Theory.models M _ IsTCAxiom.zeroNeOne

end TC

end Concatenation

end FFL.FirstOrder

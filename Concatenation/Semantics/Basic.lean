module

public import Concatenation.Biteral
public import Concatenation.TC.Basic
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-!
# Semantics of the language of concatenation

Structures with two letters and a concatenation, read as structures for `ℒ⌢`.
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

@[simp]
lemma eval_isSubstring {x y : M} :
    M ⊧/![x, y] (isSubstring : ConcatenationSemisentence 2) ↔
      x = y ∨ ∃ k l, k ++ x = y ∨ x ++ l = y ∨ (k ++ x) ++ l = y ∨ k ++ (x ++ l) = y := by
  simp [isSubstring]

end eval

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

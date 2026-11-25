module

public import Concatenation.Semantics.Basic
public import Concatenation.TC.Empty

/-!
# Semantics of the language of concatenation with the empty string

Structures with two letters, a concatenation and the empty string, read as structures for `ℒ⌢ₑ`.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A type with two letters `0`, `1`, a concatenation `++`, and the empty string `∅`. -/
class ConcatenationEmptyStructure (α : Type*) extends ConcatenationStructure α, EmptyCollection α

namespace ConcatenationEmptyStructure

variable {α : Type*} [ConcatenationEmptyStructure α]

/-- The value of a possibly empty binary string, associated to the left. -/
def ofList : List Bool → α
  | [] => ∅
  | b :: l => ConcatenationStructure.ofFreeSemigroup ⟨b, l⟩

end ConcatenationEmptyStructure

namespace Concatenation

open Language

section semantics

variable (M : Type*) [ConcatenationEmptyStructure M]

instance standardModelEmpty : Tarski.Structure ℒ⌢ₑ M where
  func := fun _ f ↦
    match f with
    | Sum.inl Concatenation.Func.zero => fun _ ↦ 0
    | Sum.inl Concatenation.Func.one => fun _ ↦ 1
    | Sum.inl Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
    | Sum.inr (Constant.Func.const _) => fun _ ↦ ∅
  rel := fun _ r ↦
    match r with
    | Sum.inl Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ₑ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ₑ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ₑ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ₑ M := ⟨fun _ _ ↦ rfl⟩

variable {M}

@[simp]
lemma val_star : (Semiterm.Operator.Star.star : Semiterm.Operator ℒ⌢ₑ 0).val ![] = (∅ : M) := rfl

end semantics

section eval

open ConcatenationStructure ConcatenationEmptyStructure

variable {M : Type*} [ConcatenationEmptyStructure M] {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M}
  {x y : M}

lemma val_biteral_empty (u : FreeSemigroup Bool) :
    (biteral u : Semiterm ℒ⌢ₑ ξ n).val e ε = ofFreeSemigroup u := by
  have hb (b : Bool) : (letter b : Semiterm ℒ⌢ₑ ξ n).val e ε = if b then 1 else 0 := by
    cases b <;> simp [letter]
  suffices ∀ (l : List Bool) (t : Semiterm ℒ⌢ₑ ξ n),
      (l.foldl (fun t b ↦ ‘!!t ⌢ !!(letter b)’) t).val e ε =
        l.foldl (fun m b ↦ m ++ if b then 1 else 0) (t.val e ε) by
    simp [biteral, ofFreeSemigroup, this, hb]
  intro l
  induction l with
  | nil => simp
  | cons b l ih => simp [ih, hb]

@[simp]
lemma val_biteralEmpty (l : List Bool) :
    (biteralEmpty l : Semiterm ℒ⌢ₑ ξ n).val e ε = ofList l := by
  cases l
  · simp [biteralEmpty, ofList]
  · simp [biteralEmpty, ofList, val_biteral_empty]

@[simp]
lemma eval_isSubstring_empty :
    M ⊧/![x, y] (isSubstring : Semisentence ℒ⌢ₑ 2) ↔ IsSubstring x y := by
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := y)]

end eval

lemma completeEmpty (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (φ : Sentence ℒ⌢ₑ)
    (H : ∀ (M : Type*) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T], M↓[ℒ⌢ₑ] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    let c : ConcatenationEmptyStructure M :=
      { zero := s.func (Sum.inl Concatenation.Func.zero) ![]
        one := s.func (Sum.inl Concatenation.Func.one) ![]
        append a b := s.func (Sum.inl Concatenation.Func.concat) ![a, b]
        emptyCollection := s.func (Sum.inr <| Constant.Func.const ⟨⟩) ![] }
    have e : s = standardModelEmpty M :=
      Tarski.Structure.ext
        (funext₃ fun k f v ↦
          match k, f with
          | _, Sum.inl Concatenation.Func.zero => congrArg _ <| Matrix.empty_eq v
          | _, Sum.inl Concatenation.Func.one => congrArg _ <| Matrix.empty_eq v
          | _, Sum.inl Concatenation.Func.concat => congrArg _ <| Matrix.fun_eq_vec_two v
          | _, Sum.inr (Constant.Func.const _) => congrArg _ <| Matrix.empty_eq v)
        (funext₃ fun k r v ↦
          match k, r with
          | _, Sum.inl Concatenation.Rel.eq =>
            (Tarski.Structure.eq_lang (L := ℒ⌢ₑ) (M := M) (v := v)).eq)
    rw [e] at hT ⊢
    exact H M

lemma weakerThan_of_models_empty (T S : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ S]
    (H : ∀ (M : Type*) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* S], M↓[ℒ⌢ₑ] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ completeEmpty _ _ fun M _ _ ↦ Theory.Proof.sound h (H M)

section TCEmpty

variable {M : Type*} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {x y z w : M}

namespace TCEmpty

@[simp]
lemma empty_append (x : M) : ∅ ++ x = x := by
  have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.emptyConcat
  exact this x

@[simp]
lemma append_empty (x : M) : x ++ ∅ = x := by
  have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.concatEmpty
  exact this x

protected lemma append_assoc (x y z : M) : x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.concatAssoc
  exact this x y z

lemma editor (h : x ++ y = z ++ w) :
    ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.editor
  exact this x y z w h

@[simp]
lemma zero_ne_empty : (0 : M) ≠ ∅ := by
  simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.zeroNeEmpty

@[simp]
lemma one_ne_empty : (1 : M) ≠ ∅ := by
  simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.oneNeEmpty

@[simp]
protected lemma zero_ne_one : (0 : M) ≠ 1 := by
  simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.zeroNeOne

lemma isAtom_ne_empty (h : IsAtom x) : x ≠ ∅ := by
  rcases h with rfl | rfl <;> simp

lemma eq_empty_of_append_isAtom (h : IsAtom (x ++ y)) : x = ∅ ∨ y = ∅ := by
  rcases h with h | h
  · have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.zeroAtom
    exact this x y h
  · have := by simpa [models_iff] using Theory.models M _ IsTCEmptyAxiom.oneAtom
    exact this x y h

lemma eq_empty_of_append_eq_empty (h : x ++ y = ∅) : x = ∅ ∧ y = ∅ := by
  suffices x = ∅ from ⟨this, by simpa [this] using h⟩
  have h₁ : 1 ++ x = ∅ ∨ y = ∅ :=
    eq_empty_of_append_isAtom <| by simp [TCEmpty.append_assoc, h]
  rcases h₁ with h₁ | rfl
  · have h₂ : (1 : M) = ∅ ∨ x ++ 0 = ∅ := eq_empty_of_append_isAtom <| by
      simp [← TCEmpty.append_assoc, h₁]
    have h₃ : (1 : M) ++ (x ++ 0) = 0 := by simp [← TCEmpty.append_assoc, h₁]
    simp [h₂.resolve_left one_ne_empty, TCEmpty.zero_ne_one.symm] at h₃
  · simpa using h

end TCEmpty

end TCEmpty

end Concatenation

end FFL.FirstOrder

module

public import Concatenation.Semantics.Basic

/-!
# Tarski's theory of concatenation $\mathsf{F}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of Tarski's theory of concatenation, with the empty string.
- [Hor11, §2, Definition 2.11]
- [Gan09, §3]
- [Vis09, Appendix D]
-/
inductive IsFAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsFAxiom φ
  | emptyConcat : IsFAxiom “∀ x, ⋆ ⌢ x = x”
  | concatEmpty : IsFAxiom “∀ x, x ⌢ ⋆ = x”
  | concatAssoc : IsFAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | cancelRight : IsFAxiom “∀ x y z, x ⌢ z = y ⌢ z → x = y”
  | cancelLeft : IsFAxiom “∀ x y z, z ⌢ x = z ⌢ y → x = y”
  | concatZeroNeConcatOne : IsFAxiom “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”
  | emptyOrConcatLetter : IsFAxiom “∀ x, x ≠ ⋆ →
      ∃ u, x = u ⌢ !!(op(0).const) ∨ x = u ⌢ !!(op(1).const)”

/--
Tarski's theory of concatenation, with the empty string.
- [Hor11, §2, Definition 2.11]
- [Gan09, §3]
- [Vis09, Appendix D]
-/
abbrev F : Theory ℒ⌢ₑ := Set.ofPred IsFAxiom

@[inherit_doc]
notation "𝗙" => F

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗙 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsFAxiom.equal φ hφ

namespace F

variable {M : Type*} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗙] {x y z : M}

@[simp]
lemma empty_append (x : M) : ∅ ++ x = x := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.emptyConcat
  exact this x

@[simp]
lemma append_empty (x : M) : x ++ ∅ = x := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.concatEmpty
  exact this x

protected lemma append_assoc (x y z : M) : x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.concatAssoc
  exact this x y z

protected lemma append_right_cancel (h : x ++ z = y ++ z) : x = y := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.cancelRight
  exact this x y z h

protected lemma append_left_cancel (h : z ++ x = z ++ y) : x = y := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.cancelLeft
  exact this x y z h

lemma append_zero_ne_append_one (x y : M) : x ++ 0 ≠ y ++ 1 := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.concatZeroNeConcatOne
  exact this x y

lemma eq_empty_or_exists_eq_append (x : M) : x = ∅ ∨ ∃ u c, IsAtom c ∧ x = u ++ c := by
  have := by simpa [models_iff] using Theory.models M _ IsFAxiom.emptyOrConcatLetter
  rcases Classical.em (x = ∅) with h | h
  · exact Or.inl h
  · obtain ⟨u, h | h⟩ := this x h
    · exact Or.inr ⟨u, 0, isAtom_zero, h⟩
    · exact Or.inr ⟨u, 1, isAtom_one, h⟩

/-- Two strings ending with letters are equal only if they end with the same letter. -/
lemma eq_of_append_eq_append {c d : M} (hc : IsAtom c) (hd : IsAtom d) (h : x ++ c = y ++ d) :
    x = y ∧ c = d := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact ⟨F.append_right_cancel h, rfl⟩
  · exact (append_zero_ne_append_one _ _ h).elim
  · exact (append_zero_ne_append_one _ _ h.symm).elim
  · exact ⟨F.append_right_cancel h, rfl⟩

@[simp]
protected lemma zero_ne_one : (0 : M) ≠ 1 := fun h ↦
  append_zero_ne_append_one (∅ : M) ∅ <| by simpa using h

lemma append_isAtom_ne_empty {c : M} (hc : IsAtom c) (x : M) : x ++ c ≠ ∅ := by
  intro h
  have h₁ (d : M) (hd : IsAtom d) : d = c :=
    (eq_of_append_eq_append hd hc (x := ∅) (y := d ++ x) <| by simp [F.append_assoc, h]).2
  exact F.zero_ne_one ((h₁ 0 isAtom_zero).trans (h₁ 1 isAtom_one).symm)

lemma isAtom_ne_empty (h : IsAtom x) : x ≠ ∅ := by
  simpa using append_isAtom_ne_empty h ∅

lemma eq_empty_of_append_eq_empty (h : x ++ y = ∅) : y = ∅ := by
  rcases eq_empty_or_exists_eq_append y with h' | ⟨u, c, hc, rfl⟩
  · exact h'
  · exact (append_isAtom_ne_empty hc (x ++ u) <| by rw [F.append_assoc, h]).elim

lemma eq_empty_of_append_isAtom (h : IsAtom (x ++ y)) : x = ∅ ∨ y = ∅ := by
  rcases eq_empty_or_exists_eq_append y with h' | ⟨u, c, hc, rfl⟩
  · exact Or.inr h'
  · have h₁ : x ++ u = ∅ := (eq_of_append_eq_append hc h <| by simp [F.append_assoc]).1
    left
    simpa [eq_empty_of_append_eq_empty h₁] using h₁

end F

end FFL.FirstOrder.Concatenation

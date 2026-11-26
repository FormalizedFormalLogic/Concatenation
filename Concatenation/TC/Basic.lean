module

public import AlphaCentauri.ToFoundation.FirstOrder.Axiomatizability
public import Concatenation.Semantics.Basic

/-!
# The theory of concatenation $\mathsf{TC}$

The axioms of $\mathsf{TC}$, without and with the empty string, and their first consequences.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of Grzegorczyk's theory of concatenation of nonempty strings over two letters.
- [GZ08, §1]
- [Vis09, §2]
-/
inductive IsTCAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsTCAxiom φ
  | concatAssoc : IsTCAxiom “∀ x y z, x ⌢ (y ⌢ z) = (x ⌢ y) ⌢ z”
  | editor : IsTCAxiom “∀ x y z w, x ⌢ y = z ⌢ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ⌢ u = z ∧ y = u ⌢ w) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”
  | zeroNeConcat : IsTCAxiom “∀ x y, !!(op(0).const) ≠ x ⌢ y”
  | oneNeConcat : IsTCAxiom “∀ x y, !!(op(1).const) ≠ x ⌢ y”
  | zeroNeOne : IsTCAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
Grzegorczyk's theory of concatenation.
- [GZ08, §1]
-/
abbrev TC : Theory ℒ⌢ := Set.ofPred IsTCAxiom

@[inherit_doc]
notation "𝗧𝗖" => TC

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗧𝗖 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsTCAxiom.equal φ hφ

lemma TC.finite : (𝗧𝗖 : ConcatenationTheory).Finite := by
  apply ((Theory.Eq.finite (L := ℒ⌢)).union (Set.toFinite {_, _, _, _, _})).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | concatAssoc => exact .inr <| .inl rfl
    | editor => exact .inr <| .inr <| .inl rfl
    | zeroNeConcat => exact .inr <| .inr <| .inr <| .inl rfl
    | oneNeConcat => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | zeroNeOne => exact .inr <| .inr <| .inr <| .inr <| .inr rfl

lemma TC.finiteAxiomatizable : FiniteAxiomatizable 𝗧𝗖 := .of_finite TC.finite

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

@[simp]
protected lemma append_ne_zero (a b : M) : a ++ b ≠ 0 := (zero_ne_append a b).symm

@[simp]
protected lemma append_ne_one (a b : M) : a ++ b ≠ 1 := (one_ne_append a b).symm

@[simp]
protected lemma one_ne_zero : (1 : M) ≠ 0 := Concatenation.zero_ne_one.symm

end TC

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simp [models_iff, mul_assoc]
  case editor => simpa [models_iff] using fun x y z w ↦ FreeSemigroup.mul_eq_mul_iff.mp
  case zeroNeConcat => simpa [models_iff, zero_eq_of_false] using FreeSemigroup.of_ne_mul false
  case oneNeConcat => simpa [models_iff, one_eq_of_true] using FreeSemigroup.of_ne_mul true
  case zeroNeOne => simp [models_iff, zero_eq_of_false, one_eq_of_true, FreeSemigroup.of]⟩

instance : Entailment.Consistent 𝗧𝗖 :=
  let : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

/--
Axioms of the theory of concatenation with the empty string.
- [HH14, Definition 1]
- [Vis09, §2]
-/
inductive IsTCEmptyAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsTCEmptyAxiom φ
  | emptyConcat : IsTCEmptyAxiom “∀ x, ⋆ ⌢ x = x”
  | concatEmpty : IsTCEmptyAxiom “∀ x, x ⌢ ⋆ = x”
  | concatAssoc : IsTCEmptyAxiom “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor : IsTCEmptyAxiom “∀ x y s t, x ⌢ y = s ⌢ t →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | zeroNeEmpty : IsTCEmptyAxiom “!!(op(0).const) ≠ ⋆”
  | zeroAtom : IsTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(0).const) → x = ⋆ ∨ y = ⋆”
  | oneNeEmpty : IsTCEmptyAxiom “!!(op(1).const) ≠ ⋆”
  | oneAtom : IsTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(1).const) → x = ⋆ ∨ y = ⋆”
  | zeroNeOne : IsTCEmptyAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The theory of concatenation with the empty string.
- [HH14, Definition 1]
- [Vis09, §2]
-/
abbrev TCEmpty : Theory ℒ⌢ₑ := Set.ofPred IsTCEmptyAxiom

@[inherit_doc]
notation "𝗧𝗖ₑ" => TCEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗧𝗖ₑ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsTCEmptyAxiom.equal φ hφ

namespace TCEmpty

variable {M : Type*} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {x y z w : M}

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

@[simp]
lemma empty_ne_zero : (∅ : M) ≠ 0 := zero_ne_empty.symm

@[simp]
lemma empty_ne_one : (∅ : M) ≠ 1 := one_ne_empty.symm

@[simp]
protected lemma one_ne_zero : (1 : M) ≠ 0 := TCEmpty.zero_ne_one.symm

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
    simp [h₂.resolve_left one_ne_empty] at h₃
  · simpa using h

end TCEmpty

end FFL.FirstOrder.Concatenation

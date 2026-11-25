module

public import Concatenation.Minimality.Basic
public import Concatenation.Semantics.Basic

/-!
# $\mathsf{BT}$ without associativity

A model of $\mathsf{BT}$ without associativity that is definable in $(\mathbb{N}, +)$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open ConcatenationStructure

/--
The natural numbers with the letters $0$ and $1$, where $x0 = 3x + 3$, $x1 = 3x + 4$ and $xy = 2$
when $y$ is not a letter.
-/
@[ext]
structure TernaryCode where
  /-- The underlying natural number. -/
  val : ℕ

namespace TernaryCode

instance : Zero TernaryCode := ⟨⟨0⟩⟩

instance : One TernaryCode := ⟨⟨1⟩⟩

instance : Append TernaryCode :=
  ⟨fun x y ↦ ⟨if y.val = 0 then 3 * x.val + 3 else if y.val = 1 then 3 * x.val + 4 else 2⟩⟩

variable {x y u : TernaryCode} {α : FreeSemigroup Bool}

@[simp]
lemma val_zero : (0 : TernaryCode).val = 0 := rfl

@[simp]
lemma val_one : (1 : TernaryCode).val = 1 := rfl

lemma val_append (x y : TernaryCode) :
    (x ++ y).val = if y.val = 0 then 3 * x.val + 3 else if y.val = 1 then 3 * x.val + 4 else 2 :=
  rfl

lemma two_le_val_append (x y : TernaryCode) : 2 ≤ (x ++ y).val := by
  rw [val_append]
  split_ifs <;> omega

lemma val_letter (b : Bool) : (if b then 1 else 0 : TernaryCode).val = if b then 1 else 0 := by
  cases b <;> rfl

lemma append_eq_ofFreeSemigroup (h : u ++ y = ofFreeSemigroup α) :
    ∃ β b, α = β * FreeSemigroup.of b ∧ u = ofFreeSemigroup β ∧ y = if b then 1 else 0 := by
  have h2 := two_le_val_append u y
  rcases α.eq_of_or_eq_mul_of with ⟨b, rfl⟩ | ⟨β, b, rfl⟩
  · rw [h, ofFreeSemigroup_of, val_letter] at h2
    cases b <;> simp at h2
  · use β, b
    have h' := congrArg val h
    rw [ofFreeSemigroup_mul_of, val_append, val_append, val_letter] at h'
    and_intros
    · rfl
    · ext
      cases b <;> simp at h' <;> split_ifs at h' <;> omega
    · ext
      rw [val_letter]
      cases b <;> simp at h' <;> split_ifs at h' <;> simp <;> omega

lemma isSubstring_ofFreeSemigroup (h : IsSubstring x (ofFreeSemigroup α : TernaryCode)) :
    ∃ γ ∈ α.substrings, x = ofFreeSemigroup γ := by
  simp only [FreeSemigroup.mem_substrings_iff]
  rcases h with rfl | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · use α
    and_intros
    · exact .inl rfl
    · rfl
  · obtain ⟨β, b, rfl, -, rfl⟩ := append_eq_ofFreeSemigroup h.symm
    use FreeSemigroup.of b
    and_intros
    · exact .inr <| .inl ⟨β, rfl⟩
    · rfl
  · obtain ⟨β, b, rfl, rfl, -⟩ := append_eq_ofFreeSemigroup h.symm
    use β
    and_intros
    · exact .inr <| .inr <| .inl ⟨_, rfl⟩
    · rfl
  · obtain ⟨β, b, rfl, h', -⟩ := append_eq_ofFreeSemigroup h.symm
    obtain ⟨β', c, rfl, -, rfl⟩ := append_eq_ofFreeSemigroup h'
    use FreeSemigroup.of c
    and_intros
    · exact .inr <| .inr <| .inr ⟨β', _, rfl⟩
    · rfl
  · obtain ⟨β, b, rfl, -, h'⟩ := append_eq_ofFreeSemigroup h.symm
    have h2 := two_le_val_append x v
    rw [h', val_letter] at h2
    cases b <;> simp at h2

/-- `TernaryCode` is a model of $\mathsf{BT}$ without associativity. -/
instance models_BT_diff_concatAssoc :
    TernaryCode↓[ℒ⌢] ⊧* (𝗕𝗧 \ {concatAssoc} : Theory ℒ⌢) := ⟨by
  rintro σ ⟨h, hσ⟩
  cases h
  case equal hφ =>
    have : TernaryCode↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => exact absurd rfl hσ
  case concatRightCancel =>
    suffices ∀ x y : TernaryCode, x ≠ y → x ++ 0 ≠ y ++ 0 ∧ x ++ 1 ≠ y ++ 1 by
      simpa [models_iff] using this
    intro x y h
    simp only [ne_eq, TernaryCode.ext_iff, val_append] at h ⊢
    simp
    omega
  case concatZeroNeConcatOne =>
    suffices ∀ x y : TernaryCode, x ++ 0 ≠ y ++ 1 by simpa [models_iff] using this
    intro x y
    simp only [ne_eq, TernaryCode.ext_iff, val_append]
    simp
    omega
  case substring α =>
    simp only [models_iff]
    simpa using fun x ↦ isSubstring_ofFreeSemigroup⟩

end TernaryCode

/--
$\mathsf{BT}$ without associativity is not essentially undecidable, if the theory of `TernaryCode`
is decidable.
- [Mur22, Open Problem 3]
-/
theorem not_essentiallyUndecidable_BT_diff_concatAssoc_of_decidable
    (h : Entailment.Decidable (Tarski.Structure.theory ℒ⌢ TernaryCode)) :
    ¬(𝗕𝗧 \ {concatAssoc} : Theory ℒ⌢).EssentiallyUndecidable :=
  Theory.not_essentiallyUndecidable_of_models _ TernaryCode h

end FFL.FirstOrder.Concatenation

module

public import Concatenation.TC.Empty
public import Concatenation.ToFoundation.PrenexDefinable

/-!
# Notation induction

Substrings and tallies in $\mathsf{TC}$ with the empty string, and induction and collection on
the tallies in the models of $\Sigma_n\text{-}\mathsf{TCI}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Bounding

section TCEmpty

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {c d k l u v w x y z : V}

namespace TCEmpty

lemma isSubstring_iff : IsSubstring x y ↔ ∃ u v, y = u ++ x ++ v := by
  constructor
  · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩)
    · exact ⟨∅, ∅, by simp⟩
    · exact ⟨u, ∅, by simp⟩
    · exact ⟨∅, v, by simp⟩
    · exact ⟨u, v, rfl⟩
    · exact ⟨u, v, by simp [TCEmpty.append_assoc]⟩
  · rintro ⟨u, v, rfl⟩
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨u, v, rfl⟩

lemma isSubstring_append_append_of (h : IsSubstring x y) (u v : V) :
    IsSubstring x (u ++ y ++ v) := by
  obtain ⟨k, l, rfl⟩ := isSubstring_iff.mp h
  exact isSubstring_iff.mpr ⟨u ++ k, l ++ v, by simp [TCEmpty.append_assoc]⟩

lemma isSubstring_append_left_of (h : IsSubstring x y) (u : V) : IsSubstring x (u ++ y) := by
  simpa using isSubstring_append_append_of h u ∅

lemma isSubstring_append_right_of (h : IsSubstring x y) (v : V) : IsSubstring x (y ++ v) := by
  simpa using isSubstring_append_append_of h ∅ v

lemma isSubstring_trans (hxy : IsSubstring x y) (hyz : IsSubstring y z) : IsSubstring x z := by
  obtain ⟨k, l, rfl⟩ := isSubstring_iff.mp hyz
  exact isSubstring_append_append_of hxy k l

@[simp]
lemma empty_isSubstring (x : V) : IsSubstring ∅ x := isSubstring_iff.mpr ⟨∅, x, by simp⟩

@[simp]
lemma isSubstring_empty_iff : IsSubstring x ∅ ↔ x = ∅ := by
  constructor
  · intro h
    obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
    exact (eq_empty_of_append_eq_empty (eq_empty_of_append_eq_empty h.symm).1).2
  · rintro rfl
    simp

lemma eq_of_isSubstring_isAtom (hc : IsAtom c) (h : IsSubstring x c) : x = ∅ ∨ x = c := by
  obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
  rcases eq_empty_of_append_isAtom (h ▸ hc) with h' | rfl
  · obtain ⟨rfl, rfl⟩ := eq_empty_of_append_eq_empty h'
    simp
  · simp only [append_empty] at h
    rcases eq_empty_of_append_isAtom (h ▸ hc) with rfl | rfl
    · simp only [empty_append] at h
      exact Or.inr h.symm
    · simp

lemma eq_and_eq_of_append_isAtom (hc : IsAtom c) (hd : IsAtom d) (h : x ++ c = y ++ d) :
    x = y ∧ c = d := by
  obtain ⟨w, ⟨rfl, h'⟩ | ⟨rfl, h'⟩⟩ := editor h
  · rcases eq_empty_of_append_isAtom (h' ▸ hc) with rfl | h''
    · simp_all
    · exact absurd h'' (isAtom_ne_empty hd)
  · rcases eq_empty_of_append_isAtom (h' ▸ hd) with rfl | h''
    · simp_all
    · exact absurd h'' (isAtom_ne_empty hc)

lemma isSubstring_or_isSubstring_of_isAtom (hc : IsAtom c) (h : IsSubstring c (x ++ y)) :
    IsSubstring c x ∨ IsSubstring c y := by
  obtain ⟨k, l, h⟩ := isSubstring_iff.mp h
  obtain ⟨w, ⟨h₁, rfl⟩ | ⟨rfl, -⟩⟩ := editor h
  · obtain ⟨u, ⟨-, rfl⟩ | ⟨rfl, hu⟩⟩ := editor h₁
    · exact Or.inr <| isSubstring_iff.mpr ⟨u, l, rfl⟩
    · rcases eq_empty_of_append_isAtom (hu ▸ hc) with rfl | rfl
      · exact Or.inr <| isSubstring_iff.mpr ⟨∅, l, by simp_all⟩
      · exact Or.inl <| isSubstring_iff.mpr ⟨k, ∅, by simp_all⟩
  · exact Or.inl <| isSubstring_iff.mpr ⟨k, w, rfl⟩

@[simp]
lemma isTally_empty : IsTally c (∅ : V) := fun _ hy h ↦
  absurd (isSubstring_empty_iff.mp h) (isAtom_ne_empty hy)

lemma isTally_one : IsTally (1 : V) 1 := fun y hy h ↦ by
  rcases eq_of_isSubstring_isAtom isAtom_one h with rfl | rfl
  · exact absurd rfl (isAtom_ne_empty hy)
  · rfl

lemma isTally_of_isSubstring (hx : IsTally c x) (h : IsSubstring y x) : IsTally c y :=
  fun z hz hzy ↦ hx z hz (isSubstring_trans hzy h)

lemma isTally_append (hx : IsTally c x) (hy : IsTally c y) : IsTally c (x ++ y) := fun z hz h ↦
  (isSubstring_or_isSubstring_of_isAtom hz h).elim (hx z hz) (hy z hz)

lemma isTally_append_iff : IsTally c (x ++ y) ↔ IsTally c x ∧ IsTally c y :=
  ⟨fun h ↦ ⟨isTally_of_isSubstring h (isSubstring_append_left x y),
    isTally_of_isSubstring h (isSubstring_append_right x y)⟩, fun h ↦ isTally_append h.1 h.2⟩

lemma not_isTally_one_append_zero (x : V) : ¬IsTally 1 (x ++ 0) := fun h ↦
  TCEmpty.zero_ne_one <| h 0 isAtom_zero (isSubstring_append_right x 0)

lemma isTally_one_iff : IsTally 1 x ↔ ∀ y, IsSubstring y x → y ≠ 0 := by
  constructor
  · rintro h y hy rfl
    exact TCEmpty.zero_ne_one <| h 0 isAtom_zero hy
  · rintro h _ (rfl | rfl) hy
    · exact absurd rfl (h 0 hy)
    · rfl

end TCEmpty

end TCEmpty

section notationInduction

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V] {s : ℕ}

lemma TCISigma.models_TCEmpty (s : ℕ) [V↓[ℒ⌢ₑ] ⊧* TCISigma s] : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ :=
  models_of_ss (U := TCISigma s) inferInstance IsTCISigmaAxiom.tcEmpty

instance [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := TCISigma.models_TCEmpty 1

/-- The models of $\Sigma_{s'}\text{-}\mathsf{TCI}$ are models of $\Sigma_s\text{-}\mathsf{TCI}$
for `s ≤ s'`. -/
lemma TCISigma.models_of_le {s' : ℕ} [V↓[ℒ⌢ₑ] ⊧* TCISigma s'] (hs : s ≤ s') :
    V↓[ℒ⌢ₑ] ⊧* TCISigma s := by
  have : V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := TCISigma.models_TCEmpty s'
  have : Nonempty V := ⟨∅⟩
  apply models_theory_iff.mpr
  intro σ hσ
  rcases hσ with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact models_theory_iff.mp inferInstance _ hφ
  · obtain ⟨ψ, hψ, H⟩ := hφ.exists_eval_iff_of_le hs
    have h := Theory.models (T := TCISigma s') V (IsTCISigmaAxiom.notationInduction ψ hψ)
    simp [models_iff, notationInduction, Semiformula.eval_substs] at h ⊢
    intro f h₀ h₁ x
    have H' (y : V) := H V ![y] f
    exact (H' x).mpr <| h f ((H' ∅).mp h₀) (fun y hy ↦ by
      simpa only [H'] using h₁ y ((H' y).mpr hy)) x

/--
Notation induction for a predicate defined by a prenex $\Sigma_s$ formula with parameters.
- [HH14, Question 3]
-/
lemma TCISigma.notation_induction [V↓[ℒ⌢ₑ] ⊧* TCISigma s] {P : V → Prop}
    (hP : PrenexDefinable ℬₛ 𝚺 s fun v : Fin 1 → V ↦ P (v 0)) (empty : P ∅)
    (append : ∀ x, P x → P (x ++ 0) ∧ P (x ++ 1)) (x : V) : P x := by
  have : Nonempty V := ⟨∅⟩
  obtain ⟨e, φ, hφ, H⟩ := hP.exists_eval_iff
  have h := Theory.models (T := TCISigma s) V (IsTCISigmaAxiom.notationInduction φ hφ)
  simp [models_iff, notationInduction, Semiformula.eval_substs] at h
  have H' (y : V) : P y ↔ φ.Eval ![y] e := by simpa using H ![y]
  simp only [H'] at empty append ⊢
  exact h e empty append x

end notationInduction

end FFL.FirstOrder.Concatenation

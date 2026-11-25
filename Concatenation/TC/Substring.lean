module

public import Concatenation.Semantics.Basic

/-!
# Atoms, substrings and tallies in models of $\mathsf{TC}$

The facts about atoms, substrings and tallies that hold in every model of $\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖] {c c' d t u v x y y' z : M}

lemma isSubstring_iff : IsSubstring x y ↔ x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨
    ∃ u v, y = u ++ x ++ v := by
  simp [IsSubstring, Concatenation.append_assoc]

lemma IsSubstring.append_left (h : IsSubstring x y) : IsSubstring x (u ++ y) := by
  rcases isSubstring_iff.mp h with rfl | ⟨u', rfl⟩ | ⟨v, rfl⟩ | ⟨u', v, rfl⟩
  · simp
  · simpa [Concatenation.append_assoc] using isSubstring_append_right (u ++ u') x
  · simpa [Concatenation.append_assoc] using isSubstring_append_append u x v
  · simpa [Concatenation.append_assoc] using isSubstring_append_append (u ++ u') x v

lemma IsSubstring.append_right (h : IsSubstring x y) : IsSubstring x (y ++ v) := by
  rcases isSubstring_iff.mp h with rfl | ⟨u, rfl⟩ | ⟨v', rfl⟩ | ⟨u, v', rfl⟩
  · simp
  · simp
  · simp [Concatenation.append_assoc]
  · simpa [Concatenation.append_assoc] using isSubstring_append_append u x (v' ++ v)

@[trans]
lemma IsSubstring.trans (hxy : IsSubstring x y) (hyz : IsSubstring y z) : IsSubstring x z := by
  rcases isSubstring_iff.mp hyz with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩
  · exact hxy
  · exact hxy.append_left
  · exact hxy.append_right
  · exact hxy.append_left.append_right

lemma IsAtom.ne_append (hc : IsAtom c) : c ≠ x ++ y := by
  rcases hc with rfl | rfl <;> simp

lemma IsAtom.eq_of_append_eq_append (hc : IsAtom c) (hc' : IsAtom c') (h : y ++ c = y' ++ c') :
    c = c' ∧ y = y' := by
  rcases editor h with ⟨rfl, rfl⟩ | ⟨u, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · simp
  · exact absurd rfl hc.ne_append
  · exact absurd rfl hc'.ne_append

lemma IsAtom.eq_of_append_eq_append_left (hc : IsAtom c) (hc' : IsAtom c') (h : c ++ y = c' ++ y') :
    c = c' ∧ y = y' := by
  rcases editor h with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
  · simp
  · exact absurd rfl hc'.ne_append
  · exact absurd rfl hc.ne_append

lemma IsAtom.append_right_cancel (hc : IsAtom c) (h : x ++ c = y ++ c) : x = y :=
  (hc.eq_of_append_eq_append hc h).2

lemma IsAtom.append_left_cancel (hc : IsAtom c) (h : c ++ x = c ++ y) : x = y :=
  (hc.eq_of_append_eq_append_left hc h).2

/--
A substring of `x ++ y` is a substring of `x` or of `y`, or splits into a suffix of `x`
followed by a prefix of `y`.
- [Gan09, §3, Lemma 5]
-/
lemma IsSubstring.append_cases (h : IsSubstring z (x ++ y)) :
    IsSubstring z x ∨ IsSubstring z y ∨
      ∃ z₁ z₂, z = z₁ ++ z₂ ∧ x ⊒ z₁ ∧ z₂ ⊑ₚ y := by
  rcases isSubstring_iff.mp h with rfl | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩
  · right; right; use x, y
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · simp
    · right; right; use w, y; simp
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · right; right; use x, w; simp
    · simp
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨hw, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · rcases editor hw with ⟨rfl, rfl⟩ | ⟨w', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · simp
      · simp
      · right; right; use w', w; simp
    · simp

lemma IsAtom.eq_of_isSubstring (hc : IsAtom c) (h : IsSubstring x c) : x = c := by
  rcases isSubstring_iff.mp h with h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩
  · exact h
  · exact absurd h hc.ne_append
  · exact absurd h hc.ne_append
  · exact absurd h hc.ne_append

lemma isTally_self (hc : IsAtom c) : IsTally c c := fun _ _ h ↦ hc.eq_of_isSubstring h

lemma not_isTally_one_zero : ¬IsTally (1 : M) 0 := fun h ↦
  Concatenation.zero_ne_one <| h 0 isAtom_zero (IsSubstring.refl _)

lemma not_isTally_zero_one : ¬IsTally (0 : M) 1 := fun h ↦
  Concatenation.zero_ne_one (h 1 isAtom_one (IsSubstring.refl _)).symm

lemma isTally_one_one : IsTally (1 : M) 1 := isTally_self isAtom_one

lemma IsTally.of_isSubstring (hx : IsTally c x) (h : IsSubstring y x) : IsTally c y :=
  fun z hz hzy ↦ hx z hz (hzy.trans h)

lemma IsTally.append (hx : IsTally c x) (hy : IsTally c y) : IsTally c (x ++ y) := by
  intro z hz h
  rcases h.append_cases with h | h | ⟨z₁, z₂, h, -, -⟩
  · exact hx z hz h
  · exact hy z hz h
  · exact absurd h hz.ne_append

lemma IsTally.not_isSubstring_zero (hx : IsTally 1 x) : ¬IsSubstring 0 x := fun h ↦
  Concatenation.zero_ne_one <| hx 0 isAtom_zero h

lemma IsTally.not_isSubstring_one (hx : IsTally 0 x) : ¬IsSubstring 1 x := fun h ↦
  Concatenation.zero_ne_one (hx 1 isAtom_one h).symm

lemma IsTally.append_one (hx : IsTally 1 x) : IsTally 1 (x ++ 1) := hx.append isTally_one_one

lemma IsTally.ne_zero (hx : IsTally 1 x) : x ≠ 0 := by
  rintro rfl
  exact not_isTally_one_zero hx

lemma IsTally.ne_zero_append_zero (hx : IsTally 1 x) : x ≠ 0 ++ 0 := by
  rintro rfl
  exact hx.not_isSubstring_zero <| isSubstring_append_left 0 0

lemma append_one_ne_zero_append_zero (x : M) : x ++ 1 ≠ 0 ++ 0 := fun h ↦
  Concatenation.zero_ne_one (isAtom_one.eq_of_append_eq_append isAtom_zero h).1.symm

lemma IsSuffix.append_left (h : y ⊒ x) : u ++ y ⊒ x := by
  rcases h with rfl | ⟨u', rfl⟩
  · simp
  · right; use u ++ u'; simp [Concatenation.append_assoc]

lemma IsPrefix.append_right (h : x ⊑ₚ y) : x ⊑ₚ y ++ v := by
  rcases h with rfl | ⟨v', rfl⟩
  · simp
  · right; use v' ++ v; simp [Concatenation.append_assoc]

lemma IsSuffix.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : x ⊒ c)
    (h' : x ⊒ c') : c = c' := by
  rcases h with rfl | ⟨u, rfl⟩ <;> rcases h' with h' | ⟨u', h'⟩
  · exact h'.symm
  · exact absurd h' hc.ne_append
  · exact absurd h' hc'.ne_append
  · exact (hc.eq_of_append_eq_append hc' h').1

lemma IsPrefix.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : c ⊑ₚ x)
    (h' : c' ⊑ₚ x) : c = c' := by
  rcases h with rfl | ⟨v, rfl⟩ <;> rcases h' with h' | ⟨v', h'⟩
  · exact h'.symm
  · exact absurd h' hc.ne_append
  · exact absurd h' hc'.ne_append
  · exact (hc.eq_of_append_eq_append_left hc' h').1

@[trans]
lemma IsPrefix.trans (hxy : x ⊑ₚ y) (hyz : y ⊑ₚ z) : x ⊑ₚ z := by
  rcases hyz with rfl | ⟨v, rfl⟩
  · exact hxy
  · exact hxy.append_right

@[trans]
lemma IsSuffix.trans (hxy : y ⊒ x) (hyz : z ⊒ y) : z ⊒ x := by
  rcases hyz with rfl | ⟨u, rfl⟩
  · exact hxy
  · exact hxy.append_left

lemma IsPrefix.total (hx : x ⊑ₚ z) (hy : y ⊑ₚ z) : x ⊑ₚ y ∨ y ⊑ₚ x := by
  rcases hx with rfl | ⟨v, rfl⟩ <;> rcases hy with h | ⟨v', h⟩
  · simp [h]
  · right; right; use v'
  · left; right; use v
  · rcases editor h with ⟨rfl, -⟩ | ⟨u, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> simp

lemma IsSuffix.total (hx : z ⊒ x) (hy : z ⊒ y) : y ⊒ x ∨ x ⊒ y := by
  rcases hx with rfl | ⟨u, rfl⟩ <;> rcases hy with h | ⟨u', h⟩
  · simp [h]
  · right; right; use u'
  · left; right; use u
  · rcases editor h with ⟨-, rfl⟩ | ⟨w, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ <;> simp

lemma eq_and_eq_of_append_eq_append_isAtom (hc : IsAtom c) (hd : IsAtom d) (h : x ++ y = c ++ d) :
    x = c ∧ y = d := by
  rcases editor h with h | ⟨u, ⟨h, -⟩ | ⟨-, h⟩⟩
  · exact h
  · exact absurd h.symm hc.ne_append
  · exact absurd h.symm hd.ne_append

lemma eq_zero_or_eq_zero_zero_of_isSubstring (h : IsSubstring t (0 ++ 0 : M)) :
    t = 0 ∨ t = 0 ++ 0 := by
  rcases h.append_cases with h | h | ⟨t₁, t₂, rfl, h₁, h₂⟩
  · exact Or.inl <| isAtom_zero.eq_of_isSubstring h
  · exact Or.inl <| isAtom_zero.eq_of_isSubstring h
  · rw [isAtom_zero.eq_of_isSubstring h₁.isSubstring, isAtom_zero.eq_of_isSubstring h₂.isSubstring]
    exact Or.inr rfl

lemma eq_of_isSuffix_isAtom_zero_zero (hc : IsAtom c) (h : c ++ 0 ++ 0 ⊒ t) :
    t = 0 ∨ t = 0 ++ 0 ∨ t = c ++ 0 ++ 0 := by
  rcases h with rfl | ⟨k, h⟩
  · simp
  · rcases editor h with ⟨-, rfl⟩ | ⟨u, ⟨-, h₁⟩ | ⟨h₁, rfl⟩⟩
    · simp
    · exact absurd h₁ isAtom_zero.ne_append
    · rcases editor h₁ with ⟨-, rfl⟩ | ⟨u', ⟨-, h'⟩ | ⟨h', -⟩⟩
      · simp
      · exact absurd h' isAtom_zero.ne_append
      · exact absurd h' hc.ne_append

lemma isTally_zero_zero : IsTally (0 : M) (0 ++ 0) :=
  (isTally_self isAtom_zero).append (isTally_self isAtom_zero)

lemma zero_zero_append_ne_zero_zero : (0 ++ 0 ++ x : M) ≠ 0 ++ 0 := by
  intro h
  rcases editor h with ⟨h, -⟩ | ⟨u, ⟨h, -⟩ | ⟨-, h⟩⟩
  · exact zero_ne_append _ _ h.symm
  · exact zero_ne_append _ _ h.symm
  · exact zero_ne_append _ _ h.symm

lemma IsSuffix.append_congr (h : y ⊒ x) : y ++ z ⊒ x ++ z := by
  rcases h with rfl | ⟨u, rfl⟩
  · simp
  · right; use u; simp [Concatenation.append_assoc]

lemma IsPrefix.of_append_left_isAtom (hc : IsAtom c) (h : c ++ x ⊑ₚ c ++ y) : x ⊑ₚ y := by
  rcases h with h | ⟨t, h⟩
  · rw [hc.append_left_cancel h]
  · right; use t; exact hc.append_left_cancel <| by simpa [Concatenation.append_assoc] using h

end FFL.FirstOrder.Concatenation

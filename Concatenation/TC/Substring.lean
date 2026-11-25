module

public import Concatenation.Semantics.Substring

/-!
# Atoms, substrings and tallies in models of $\mathsf{TC}$

The facts about atoms, substrings and tallies that hold in every model of $\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖] {c c' u v x y y' z : M}

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
A substring of `x ++ y` is a substring of `x` or of `y`, or splits into an end segment of `x`
followed by an initial segment of `y`.
- [Gan09, §3, Lemma 5]
-/
theorem IsSubstring.append_cases (h : IsSubstring z (x ++ y)) :
    IsSubstring z x ∨ IsSubstring z y ∨
      ∃ z₁ z₂, z = z₁ ++ z₂ ∧ IsEndSegment z₁ x ∧ IsInitialSegment z₂ y := by
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
  Concatenation.zero_ne_one <| h 0 (Or.inl rfl) (IsSubstring.refl _)

lemma not_isTally_zero_one : ¬IsTally (0 : M) 1 := fun h ↦
  Concatenation.zero_ne_one (h 1 (Or.inr rfl) (IsSubstring.refl _)).symm

lemma IsTally.of_isSubstring (hx : IsTally c x) (h : IsSubstring y x) : IsTally c y :=
  fun z hz hzy ↦ hx z hz (hzy.trans h)

lemma IsTally.append (hx : IsTally c x) (hy : IsTally c y) : IsTally c (x ++ y) := by
  intro z hz h
  rcases h.append_cases with h | h | ⟨z₁, z₂, h, -, -⟩
  · exact hx z hz h
  · exact hy z hz h
  · exact absurd h hz.ne_append

lemma IsTally.not_isSubstring_zero (hx : IsTally 1 x) : ¬IsSubstring 0 x := fun h ↦
  Concatenation.zero_ne_one <| hx 0 (Or.inl rfl) h

lemma IsTally.not_isSubstring_one (hx : IsTally 0 x) : ¬IsSubstring 1 x := fun h ↦
  Concatenation.zero_ne_one (hx 1 (Or.inr rfl) h).symm

end FFL.FirstOrder.Concatenation

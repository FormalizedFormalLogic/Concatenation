module

public import Concatenation.Semantics.Sequence
public import Concatenation.TC.Thin

/-!
# Separation of tallies in $\mathsf{TC}^+$

The first and last atoms of a string in $\mathsf{TC}^+$, and the separation of tallies by a
string ending with the other letter.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M] {c c' d s s' t u v u' v' x x' y y' z z' : M}

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma IsEndSegment.append_left (h : IsEndSegment x y) : IsEndSegment x (u ++ y) := by
  rcases h with rfl | ⟨u', rfl⟩
  · simp
  · right; use u ++ u'; simp [Concatenation.append_assoc]

lemma IsInitialSegment.append_right (h : IsInitialSegment x y) : IsInitialSegment x (y ++ v) := by
  rcases h with rfl | ⟨v', rfl⟩
  · simp
  · right; use v' ++ v; simp [Concatenation.append_assoc]

lemma IsEndSegment.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : IsEndSegment c x)
    (h' : IsEndSegment c' x) : c = c' := by
  rcases h with rfl | ⟨u, rfl⟩ <;> rcases h' with h' | ⟨u', h'⟩
  · exact h'.symm
  · exact absurd h' hc.ne_append
  · exact absurd h' hc'.ne_append
  · exact (hc.eq_of_append_eq_append hc' h').1

lemma IsInitialSegment.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : IsInitialSegment c x)
    (h' : IsInitialSegment c' x) : c = c' := by
  rcases h with rfl | ⟨v, rfl⟩ <;> rcases h' with h' | ⟨v', h'⟩
  · exact h'.symm
  · exact absurd h' hc.ne_append
  · exact absurd h' hc'.ne_append
  · exact (hc.eq_of_append_eq_append_left hc' h').1

@[trans]
lemma IsInitialSegment.trans (hxy : IsInitialSegment x y) (hyz : IsInitialSegment y z) :
    IsInitialSegment x z := by
  rcases hyz with rfl | ⟨v, rfl⟩
  · exact hxy
  · exact hxy.append_right

@[trans]
lemma IsEndSegment.trans (hxy : IsEndSegment x y) (hyz : IsEndSegment y z) : IsEndSegment x z := by
  rcases hyz with rfl | ⟨u, rfl⟩
  · exact hxy
  · exact hxy.append_left

lemma IsInitialSegment.total (hx : IsInitialSegment x z) (hy : IsInitialSegment y z) :
    IsInitialSegment x y ∨ IsInitialSegment y x := by
  rcases hx with rfl | ⟨v, rfl⟩ <;> rcases hy with h | ⟨v', h⟩
  · simp [h]
  · right; right; use v'
  · left; right; use v
  · rcases editor h with ⟨rfl, -⟩ | ⟨u, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> simp

lemma IsEndSegment.total (hx : IsEndSegment x z) (hy : IsEndSegment y z) :
    IsEndSegment x y ∨ IsEndSegment y x := by
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
  have h0 : IsAtom (0 : M) := Or.inl rfl
  rcases h.append_cases with h | h | ⟨t₁, t₂, rfl, h₁, h₂⟩
  · exact Or.inl <| h0.eq_of_isSubstring h
  · exact Or.inl <| h0.eq_of_isSubstring h
  · rw [h0.eq_of_isSubstring h₁.isSubstring, h0.eq_of_isSubstring h₂.isSubstring]
    exact Or.inr rfl

lemma eq_of_isEndSegment_isAtom_zero_zero (hc : IsAtom c) (h : IsEndSegment t (c ++ 0 ++ 0)) :
    t = 0 ∨ t = 0 ++ 0 ∨ t = c ++ 0 ++ 0 := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  rcases h with rfl | ⟨k, h⟩
  · simp
  · rcases editor h with ⟨-, rfl⟩ | ⟨u, ⟨-, h₁⟩ | ⟨h₁, rfl⟩⟩
    · simp
    · exact absurd h₁ h0.ne_append
    · rcases editor h₁ with ⟨-, rfl⟩ | ⟨u', ⟨-, h'⟩ | ⟨h', -⟩⟩
      · simp
      · exact absurd h' h0.ne_append
      · exact absurd h' hc.ne_append

lemma isTally_zero_zero : IsTally (0 : M) (0 ++ 0) :=
  (isTally_self <| Or.inl rfl).append (isTally_self <| Or.inl rfl)

lemma zero_zero_append_ne_zero_zero : (0 ++ 0 ++ x : M) ≠ 0 ++ 0 := by
  intro h
  rcases editor h with ⟨h, -⟩ | ⟨u, ⟨h, -⟩ | ⟨-, h⟩⟩
  · exact zero_ne_append _ _ h.symm
  · exact zero_ne_append _ _ h.symm
  · exact zero_ne_append _ _ h.symm

lemma IsEndSegment.append_congr (h : IsEndSegment x y) : IsEndSegment (x ++ z) (y ++ z) := by
  rcases h with rfl | ⟨u, rfl⟩
  · simp
  · right; use u; simp [Concatenation.append_assoc]

lemma IsInitialSegment.of_append_left_isAtom (hc : IsAtom c)
    (h : IsInitialSegment (c ++ x) (c ++ y)) : IsInitialSegment x y := by
  rcases h with h | ⟨t, h⟩
  · rw [hc.append_left_cancel h]
  · right; use t; exact hc.append_left_cancel <| by simpa [Concatenation.append_assoc] using h

end TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

lemma exists_isEndSegment_isAtom (x : M) : ∃ c, IsAtom c ∧ IsEndSegment c x := by
  rcases TCPlus.isBounded x with hx | ⟨-, c, z, hc, rfl⟩
  · use x
  · use c
    and_intros
    · exact hc
    · simp

lemma exists_isInitialSegment_isAtom (x : M) : ∃ c, IsAtom c ∧ IsInitialSegment c x := by
  rcases TCPlus.isBounded x with hx | ⟨⟨c, z, hc, rfl⟩, -⟩
  · use x
  · use c
    and_intros
    · exact hc
    · simp

lemma IsTally.isEndSegment (hx : IsTally c x) : IsEndSegment c x := by
  obtain ⟨d, hd, h⟩ := exists_isEndSegment_isAtom x
  rwa [← hx d hd h.isSubstring]

lemma IsTally.isInitialSegment (hx : IsTally c x) : IsInitialSegment c x := by
  obtain ⟨d, hd, h⟩ := exists_isInitialSegment_isAtom x
  rwa [← hx d hd h.isSubstring]

lemma IsTally.eq_or_exists_append (hx : IsTally c x) :
    x = c ∨ ∃ x', IsTally c x' ∧ x = x' ++ c := by
  rcases hx.isEndSegment with rfl | ⟨x', rfl⟩
  · simp
  · right
    use x'
    and_intros
    · exact hx.of_isSubstring <| isSubstring_append_left x' c
    · rfl

lemma IsInitialSegment.isInitialSegment_of_isAtom (ht : IsInitialSegment t z) (hc : IsAtom c)
    (hz : IsInitialSegment c z) : IsInitialSegment c t := by
  obtain ⟨e, he, het⟩ := exists_isInitialSegment_isAtom t
  rwa [← (het.trans ht).eq_of_isAtom he hc hz]

lemma IsEndSegment.isEndSegment_of_isAtom (ht : IsEndSegment t z) (hc : IsAtom c)
    (hz : IsEndSegment c z) : IsEndSegment c t := by
  obtain ⟨e, he, het⟩ := exists_isEndSegment_isAtom t
  rwa [← (het.trans ht).eq_of_isAtom he hc hz]

lemma IsTally.eq_of_isTally (hc : IsTally c x) (hd : IsTally d x) : c = d := by
  obtain ⟨e, he, h⟩ := exists_isEndSegment_isAtom x
  rw [← hc e he h.isSubstring, ← hd e he h.isSubstring]

lemma IsTally.not_isSubstring_of_isTally_one (ht : IsTally 0 t) (hx : IsTally 1 x) :
    ¬IsSubstring t x := fun h ↦ Concatenation.zero_ne_one <| ht.eq_of_isTally <| hx.of_isSubstring h

lemma IsTally.isSubstring_or_isSubstring (ht : IsTally 0 t) (h : IsSubstring t (x ++ y))
    (hxy : IsEndSegment 1 x ∨ IsInitialSegment 1 y) : IsSubstring t x ∨ IsSubstring t y := by
  rcases h.append_cases with h | h | ⟨t₁, t₂, rfl, h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr h
  · apply absurd _ ht.not_isSubstring_one
    rcases hxy with hx | hy
    · exact (h₁.isEndSegment_of_isAtom (Or.inr rfl) hx).isSubstring.append_right
    · exact (h₂.isInitialSegment_of_isAtom (Or.inr rfl) hy).isSubstring.append_left

/--
A `c`-tally is not separated from the preceding string ending with an atom `d ≠ c`: if `x` and `y`
are `c`-tallies and `z`, `z'` end with `d`, then `z ++ x = z' ++ y` implies `z = z'` and `x = y`.
- [Gan09, §3, Lemma 7]
-/
theorem tally_separation_of_ne (hd : IsAtom d) (hdc : d ≠ c) (hx : IsTally c x) (hy : IsTally c y)
    (hz : IsEndSegment d z) (hz' : IsEndSegment d z') (h : z ++ x = z' ++ y) : z = z' ∧ x = y := by
  have H : ∀ {z z' x y : M}, IsTally c x → IsEndSegment d z' → ∀ w, z ++ w = z' → x ≠ w ++ y := by
    intro z z' x y hx hz' w hw hxw
    obtain ⟨e, he, hew⟩ := exists_isEndSegment_isAtom w
    have h₁ : IsEndSegment e z' := hw ▸ hew.append_left
    obtain rfl := h₁.eq_of_isAtom he hd hz'
    exact hdc <| hx e he <| hxw ▸ hew.isSubstring.append_right
  rcases editor h with h | ⟨w, ⟨hw, hxw⟩ | ⟨hw, hyw⟩⟩
  · exact h
  · exact absurd hxw <| H hx hz' w hw
  · exact absurd hyw.symm <| H hy hz w hw.symm

/--
If `x` and `y` are `1`-tallies and `z`, `z'` end with `0`, then `z ++ x = z' ++ y` implies `z = z'`
and `x = y`.
- [Gan09, §3, Lemma 7]
-/
theorem tally_separation (hx : IsTally 1 x) (hy : IsTally 1 y) (hz : IsEndSegment 0 z)
    (hz' : IsEndSegment 0 z') (h : z ++ x = z' ++ y) : z = z' ∧ x = y :=
  tally_separation_of_ne (Or.inl rfl) Concatenation.zero_ne_one hx hy hz hz' h

/--
If `x` and `y` are `0`-tallies and `z`, `z'` end with `1`, then `z ++ x = z' ++ y` implies `z = z'`
and `x = y`.
- [Gan09, §3, Lemma 7]
-/
theorem tally_separation' (hx : IsTally 0 x) (hy : IsTally 0 y) (hz : IsEndSegment 1 z)
    (hz' : IsEndSegment 1 z') (h : z ++ x = z' ++ y) : z = z' ∧ x = y :=
  tally_separation_of_ne (Or.inr rfl) Concatenation.zero_ne_one.symm hx hy hz hz' h

/--
The pairing of `1`-tallies is injective.
- [Gan09, §3]
-/
lemma pairOf_inj (hy : IsTally 1 y) (hy' : IsTally 1 y') :
    pairOf x y = pairOf x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    obtain ⟨h₁, rfl⟩ :=
      tally_separation hy hy' (isEndSegment_append x 0) (isEndSegment_append x' 0) h
    exact ⟨IsAtom.append_right_cancel (Or.inl rfl) h₁, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `s 0 0 u 0 v 0 0` determines `s`, `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq (hu : IsTally 1 u) (hv : IsTally 1 v) (hu' : IsTally 1 u')
    (hv' : IsTally 1 v')
    (h : s ++ (0 ++ 0 ++ pairOf u v ++ 0 ++ 0) = s' ++ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0)) :
    s = s' ∧ u = u' ∧ v = v' := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  simp only [pairOf, ← Concatenation.append_assoc] at h
  obtain ⟨h₁, rfl⟩ := tally_separation hv hv' (isEndSegment_append _ _) (isEndSegment_append _ _)
    (h0.append_right_cancel <| h0.append_right_cancel h)
  obtain ⟨h₂, rfl⟩ := tally_separation hu hu' (isEndSegment_append _ _) (isEndSegment_append _ _)
    (h0.append_right_cancel h₁)
  exact ⟨h0.append_right_cancel <| h0.append_right_cancel h₂, rfl, rfl⟩

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `0 0 u 0 v 0 0` determines `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq_of_no_prefix (hu : IsTally 1 u) (hv : IsTally 1 v) (hu' : IsTally 1 u')
    (hv' : IsTally 1 v')
    (h : 0 ++ 0 ++ pairOf u v ++ 0 ++ 0 = 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) : u = u' ∧ v = v' :=
  (configuration_eq (s := 1) (s' := 1) hu hv hu' hv' <| congrArg (1 ++ ·) h).2

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `0 0 u 0 v 0 0` is not of the form
`s' 0 0 u' 0 v' 0 0`.
- [Gan09, §3]
-/
lemma configuration_ne (hu : IsTally 1 u) (hv : IsTally 1 v) (hu' : IsTally 1 u')
    (hv' : IsTally 1 v') :
    0 ++ 0 ++ pairOf u v ++ 0 ++ 0 ≠ s' ++ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) := by
  intro h
  have h₁ := congrArg (1 ++ ·) h
  simp only [← Concatenation.append_assoc (1 : M) s'] at h₁
  exact one_ne_append _ _ (configuration_eq hu hv hu' hv' h₁).1

/--
For `1`-tallies `u`, `v`, `u'`, `v'` and strings `s`, `s'` ending with `0`, the string
`s u 0 v 0 0` determines `s`, `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq_of_isEndSegment (hu : IsTally 1 u) (hv : IsTally 1 v) (hu' : IsTally 1 u')
    (hv' : IsTally 1 v') (hs : IsEndSegment 0 s) (hs' : IsEndSegment 0 s')
    (h : s ++ (pairOf u v ++ 0 ++ 0) = s' ++ (pairOf u' v' ++ 0 ++ 0)) :
    s = s' ∧ u = u' ∧ v = v' := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  simp only [pairOf, ← Concatenation.append_assoc] at h
  obtain ⟨h₁, rfl⟩ := tally_separation hv hv' (isEndSegment_append _ _) (isEndSegment_append _ _)
    (h0.append_right_cancel <| h0.append_right_cancel h)
  obtain ⟨h₂, rfl⟩ := tally_separation hu hu' hs hs' (h0.append_right_cancel h₁)
  exact ⟨h₂, rfl, rfl⟩

end FFL.FirstOrder.Concatenation

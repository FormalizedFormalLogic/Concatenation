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

variable {M : Type*} [ConcatenationStructure M] {c d s s' t u v u' v' x x' y y' z z' : M}
  [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

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
    · exact (h₁.isEndSegment_of_isAtom isAtom_one hx).isSubstring.append_right
    · exact (h₂.isInitialSegment_of_isAtom isAtom_one hy).isSubstring.append_left

/--
A `c`-tally is separated from a preceding string ending with an atom `d ≠ c`: if `x` and `y`
are `c`-tallies and `z`, `z'` end with `d`, then `z ++ x = z' ++ y` implies `z = z'` and `x = y`.
- [Gan09, §3, Lemma 7]
-/
lemma tally_separation_of_ne (hd : IsAtom d) (hdc : d ≠ c) (hx : IsTally c x) (hy : IsTally c y)
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
  tally_separation_of_ne isAtom_zero Concatenation.zero_ne_one hx hy hz hz' h

/--
If `x` and `y` are `0`-tallies and `z`, `z'` end with `1`, then `z ++ x = z' ++ y` implies `z = z'`
and `x = y`.
- [Gan09, §3, Lemma 7]
-/
lemma tally_separation' (hx : IsTally 0 x) (hy : IsTally 0 y) (hz : IsEndSegment 1 z)
    (hz' : IsEndSegment 1 z') (h : z ++ x = z' ++ y) : z = z' ∧ x = y :=
  tally_separation_of_ne isAtom_one Concatenation.zero_ne_one.symm hx hy hz hz' h

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
    exact ⟨isAtom_zero.append_right_cancel h₁, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

section configuration

variable (hu : IsTally 1 u) (hv : IsTally 1 v) (hu' : IsTally 1 u') (hv' : IsTally 1 v')
include hu hv hu' hv'

/--
For `1`-tallies `u`, `v`, `u'`, `v'` and strings `s`, `s'` ending with `0`, the string
`s u 0 v 0 0` determines `s`, `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq_of_isEndSegment (hs : IsEndSegment 0 s) (hs' : IsEndSegment 0 s')
    (h : s ++ (pairOf u v ++ 0 ++ 0) = s' ++ (pairOf u' v' ++ 0 ++ 0)) :
    s = s' ∧ u = u' ∧ v = v' := by
  simp only [pairOf, ← Concatenation.append_assoc] at h
  obtain ⟨h₁, rfl⟩ := tally_separation hv hv' (isEndSegment_append _ _) (isEndSegment_append _ _)
    (isAtom_zero.append_right_cancel <| isAtom_zero.append_right_cancel h)
  obtain ⟨h₂, rfl⟩ := tally_separation hu hu' hs hs' (isAtom_zero.append_right_cancel h₁)
  exact ⟨h₂, rfl, rfl⟩

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `s 0 0 u 0 v 0 0` determines `s`, `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq
    (h : s ++ (0 ++ 0 ++ pairOf u v ++ 0 ++ 0) = s' ++ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0)) :
    s = s' ∧ u = u' ∧ v = v' := by
  obtain ⟨h₁, h₂⟩ := configuration_eq_of_isEndSegment hu hv hu' hv'
    (isEndSegment_append (s ++ 0) 0) (isEndSegment_append (s' ++ 0) 0) <| by
      simpa only [Concatenation.append_assoc] using h
  exact ⟨isAtom_zero.append_right_cancel <| isAtom_zero.append_right_cancel h₁, h₂⟩

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `0 0 u 0 v 0 0` determines `u` and `v`.
- [Gan09, §3]
-/
lemma configuration_eq_of_no_prefix
    (h : 0 ++ 0 ++ pairOf u v ++ 0 ++ 0 = 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) : u = u' ∧ v = v' :=
  (configuration_eq (s := 1) (s' := 1) hu hv hu' hv' <| congrArg (1 ++ ·) h).2

/--
For `1`-tallies `u`, `v`, `u'`, `v'`, the string `0 0 u 0 v 0 0` is not of the form
`s' 0 0 u' 0 v' 0 0`.
- [Gan09, §3]
-/
lemma configuration_ne :
    0 ++ 0 ++ pairOf u v ++ 0 ++ 0 ≠ s' ++ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) := by
  intro h
  have h₁ := congrArg (1 ++ ·) h
  simp only [← Concatenation.append_assoc (1 : M) s'] at h₁
  exact one_ne_append _ _ (configuration_eq hu hv hu' hv' h₁).1

end configuration

end FFL.FirstOrder.Concatenation

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

variable {M : Type*} [ConcatenationStructure M] {c c' d s s' u v u' v' x x' y y' z z' : M}

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

end FFL.FirstOrder.Concatenation

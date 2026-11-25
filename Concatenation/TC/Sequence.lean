module

public import Concatenation.TC.Substring

/-!
# Pairs, sequences and multiplication sequences

Ganea's coding of finite sequences of pairs of tallies by strings, and the extension and the
restriction of multiplication sequences in $\mathsf{TC}^+$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section definitions

variable {M : Type*} [ConcatenationStructure M] {x y z u : M}

/--
The ordered pair of `x` and `y`, the string `x 0 y`.
- [Gan09, §1, Definition 1(c)]
-/
def pairOf (x y : M) : M := x ++ 0 ++ y

/--
`z` is an ordered pair of `1`-tallies.
- [Gan09, §1, Definition 1(c)]
-/
def IsPair (z : M) : Prop := ∃ x y, IsTally 1 x ∧ IsTally 1 y ∧ z = pairOf x y

/-- `z` is an ordered pair of `1`-tallies. -/
def isPair : Semisentence ℒ⌢ 1 :=
  “z. ∃ x y, !isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧
    z = x ⌢ !!(op(0).const) ⌢ y”

@[simp]
lemma eval_isPair : M ⊧/![z] isPair ↔ IsPair z := by simp [isPair, IsPair, pairOf]

/--
`z` is a sequence: it begins with `001`, ends with `100`, and its only `0`-tally substrings are
`0` and `00`.
- [Gan09, §1, Definition 1(d)]
-/
@[mk_iff]
structure IsSeq (z : M) : Prop where
  isPrefix : 0 ++ 0 ++ 1 ◨ z
  isSuffix : z ◧ 1 ++ 0 ++ 0
  eq_of_isTally : ∀ y, IsTally 0 y → IsSubstring y z → y = 0 ∨ y = 0 ++ 0

/-- `z` is a sequence. -/
def isSeq : Semisentence ℒ⌢ 1 :=
  “z. !isPrefix (!!(op(0).const) ⌢ !!(op(0).const) ⌢ !!(op(1).const)) z ∧
    !isSuffix (!!(op(1).const) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z ∧
    ∀ y, !isTally !!(op(0).const) y → !isSubstring y z →
      y = !!(op(0).const) ∨ y = !!(op(0).const) ⌢ !!(op(0).const)”

@[simp]
lemma eval_isSeq : M ⊧/![z] isSeq ↔ IsSeq z := by simp [isSeq, isSeq_iff]

/--
`y` is a member of the sequence `z`.
- [Gan09, §1, Definition 1(e)]
-/
def Mem (y z : M) : Prop :=
  IsSeq z ∧ ¬IsSubstring (0 ++ 0) y ∧ IsSubstring (0 ++ 0 ++ y ++ 0 ++ 0) z

/-- `y` is a member of the sequence `z`. -/
def mem : Semisentence ℒ⌢ 2 :=
  “y z. !isSeq z ∧ ¬!isSubstring (!!(op(0).const) ⌢ !!(op(0).const)) y ∧
    !isSubstring
      (!!(op(0).const) ⌢ !!(op(0).const) ⌢ y ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

@[simp]
lemma eval_mem : M ⊧/![y, z] mem ↔ Mem y z := by simp [mem, Mem]

/--
`z` is a sequence of ordered pairs.
- [Gan09, §1, Definition 1(e)]
-/
def IsPairSeq (z : M) : Prop := IsSeq z ∧ ∀ y, Mem y z → IsPair y

/-- `z` is a sequence of ordered pairs. -/
def isPairSeq : Semisentence ℒ⌢ 1 := “z. !isSeq z ∧ ∀ y, !mem y z → !isPair y”

@[simp]
lemma eval_isPairSeq : M ⊧/![z] isPairSeq ↔ IsPairSeq z := by simp [isPairSeq, IsPairSeq]

/--
`u` is the first member of `z`.
- [Gan09, §1, Definition 1(f)]
-/
def IsFirst (u z : M) : Prop := 0 ++ 0 ++ u ++ 0 ++ 0 ◨ z

/-- `u` is the first member of `z`. -/
def isFirst : Semisentence ℒ⌢ 2 :=
  “u z. !isPrefix
    (!!(op(0).const) ⌢ !!(op(0).const) ⌢ u ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

@[simp]
lemma eval_isFirst : M ⊧/![u, z] isFirst ↔ IsFirst u z := by simp [isFirst, IsFirst]

/--
`u` is the last member of `z`.
- [Gan09, §1, Definition 1(f)]
-/
def IsLast (u z : M) : Prop := z ◧ 0 ++ 0 ++ u ++ 0 ++ 0

/-- `u` is the last member of `z`. -/
def isLast : Semisentence ℒ⌢ 2 :=
  “u z. !isSuffix
    (!!(op(0).const) ⌢ !!(op(0).const) ⌢ u ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

@[simp]
lemma eval_isLast : M ⊧/![u, z] isLast ↔ IsLast u z := by simp [isLast, IsLast]

/--
`z` is a multiplication sequence for the `1`-tallies `x` and `y`: a sequence of pairs from
`(x, 1)` to `(w, y)` for some `1`-tally `w`, in which each pair but the first is `(u x, v 1)` for
the pair `(u, v)` immediately before it. Each pair `(u, v)` in it records $x \cdot v = u$.
The last clause is the one of Švejdar.
- [Gan09, §1, Definition 1(g)]
- [Sve09, §3]
-/
@[mk_iff]
structure IsMulSeq (x y z : M) : Prop where
  isTally_left : IsTally 1 x
  isTally_right : IsTally 1 y
  isPairSeq : IsPairSeq z
  isFirst : IsFirst (pairOf x 1) z
  exists_isLast : ∃ w, IsTally 1 w ∧ IsLast (pairOf w y) z
  exists_pred : ∀ s u' v', IsTally 1 u' → IsTally 1 v' →
    s ++ 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0 ◨ z →
    ∃ u v, IsTally 1 u ∧ IsTally 1 v ∧ u' = u ++ x ∧ v' = v ++ 1 ∧ s ◧ 0 ++ 0 ++ pairOf u v

/-- `z` is a multiplication sequence for the `1`-tallies `x` and `y`. -/
def isMulSeq : Semisentence ℒ⌢ 3 :=
  “x y z. !isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧ !isPairSeq z ∧
    !isFirst (x ⌢ !!(op(0).const) ⌢ !!(op(1).const)) z ∧
    (∃ w, !isTally !!(op(1).const) w ∧ !isLast (w ⌢ !!(op(0).const) ⌢ y) z) ∧
    ∀ s u' v', !isTally !!(op(1).const) u' → !isTally !!(op(1).const) v' →
      !isPrefix (s ⌢ !!(op(0).const) ⌢ !!(op(0).const) ⌢ (u' ⌢ !!(op(0).const) ⌢ v') ⌢
        !!(op(0).const) ⌢ !!(op(0).const)) z →
      ∃ u v, !isTally !!(op(1).const) u ∧ !isTally !!(op(1).const) v ∧
        u' = u ⌢ x ∧ v' = v ⌢ !!(op(1).const) ∧
        !isSuffix (!!(op(0).const) ⌢ !!(op(0).const) ⌢ (u ⌢ !!(op(0).const) ⌢ v)) s”

@[simp]
lemma eval_isMulSeq : M ⊧/![x, y, z] isMulSeq ↔ IsMulSeq x y z := by
  simp [isMulSeq, isMulSeq_iff, pairOf]

lemma IsPairSeq.isSeq (h : IsPairSeq z) : IsSeq z := h.1

end definitions

section separation

variable {M : Type*} [ConcatenationStructure M] {c d s s' t u v u' v' x x' y y' z z' : M}
  [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

lemma exists_isSuffix_isAtom (x : M) : ∃ c, IsAtom c ∧ x ◧ c := by
  rcases TCPlus.isBounded x with hx | ⟨-, c, z, hc, rfl⟩
  · use x
  · use c
    simp [hc]

lemma exists_isPrefix_isAtom (x : M) : ∃ c, IsAtom c ∧ c ◨ x := by
  rcases TCPlus.isBounded x with hx | ⟨⟨c, z, hc, rfl⟩, -⟩
  · use x
  · use c
    simp [hc]

lemma IsTally.isSuffix (hx : IsTally c x) : x ◧ c := by
  obtain ⟨d, hd, h⟩ := exists_isSuffix_isAtom x
  rwa [← hx d hd h.isSubstring]

lemma IsTally.isPrefix (hx : IsTally c x) : c ◨ x := by
  obtain ⟨d, hd, h⟩ := exists_isPrefix_isAtom x
  rwa [← hx d hd h.isSubstring]

lemma IsTally.eq_or_exists_append (hx : IsTally c x) :
    x = c ∨ ∃ x', IsTally c x' ∧ x = x' ++ c := by
  rcases hx.isSuffix with rfl | ⟨x', rfl⟩
  · simp
  · right
    use x', hx.of_isSubstring <| isSubstring_append_left x' c

lemma IsPrefix.isPrefix_of_isAtom (ht : t ◨ z) (hc : IsAtom c) (hz : c ◨ z) : c ◨ t := by
  obtain ⟨e, he, het⟩ := exists_isPrefix_isAtom t
  rwa [← (het.trans ht).eq_of_isAtom he hc hz]

lemma IsSuffix.isSuffix_of_isAtom (ht : z ◧ t) (hc : IsAtom c) (hz : z ◧ c) : t ◧ c := by
  obtain ⟨e, he, het⟩ := exists_isSuffix_isAtom t
  rwa [← (het.trans ht).eq_of_isAtom he hc hz]

lemma IsTally.eq_of_isTally (hc : IsTally c x) (hd : IsTally d x) : c = d := by
  obtain ⟨e, he, h⟩ := exists_isSuffix_isAtom x
  rw [← hc e he h.isSubstring, ← hd e he h.isSubstring]

lemma IsTally.not_isSubstring_of_isTally_one (ht : IsTally 0 t) (hx : IsTally 1 x) :
    ¬IsSubstring t x := fun h ↦ Concatenation.zero_ne_one <| ht.eq_of_isTally <| hx.of_isSubstring h

lemma IsTally.isSubstring_or_isSubstring (ht : IsTally 0 t) (h : IsSubstring t (x ++ y))
    (hxy : x ◧ 1 ∨ 1 ◨ y) : IsSubstring t x ∨ IsSubstring t y := by
  rcases h.append_cases with h | h | ⟨t₁, t₂, rfl, h₁, h₂⟩
  · exact Or.inl h
  · exact Or.inr h
  · apply absurd _ ht.not_isSubstring_one
    rcases hxy with hx | hy
    · exact (h₁.isSuffix_of_isAtom isAtom_one hx).isSubstring.append_right
    · exact (h₂.isPrefix_of_isAtom isAtom_one hy).isSubstring.append_left

/--
A `c`-tally is separated from a preceding string ending with an atom `d ≠ c`: if `x` and `y`
are `c`-tallies and `z`, `z'` end with `d`, then `z ++ x = z' ++ y` implies `z = z'` and `x = y`.
- [Gan09, §3, Lemma 7]
-/
lemma tally_separation_of_ne (hd : IsAtom d) (hdc : d ≠ c) (hx : IsTally c x) (hy : IsTally c y)
    (hz : z ◧ d) (hz' : z' ◧ d) (h : z ++ x = z' ++ y) : z = z' ∧ x = y := by
  have H : ∀ {z z' x y : M}, IsTally c x → z' ◧ d → ∀ w, z ++ w = z' → x ≠ w ++ y := by
    intro z z' x y hx hz' w hw hxw
    obtain ⟨e, he, hew⟩ := exists_isSuffix_isAtom w
    have h₁ : z' ◧ e := hw ▸ hew.append_left
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
lemma tally_separation (hx : IsTally 1 x) (hy : IsTally 1 y) (hz : z ◧ 0)
    (hz' : z' ◧ 0) (h : z ++ x = z' ++ y) : z = z' ∧ x = y :=
  tally_separation_of_ne isAtom_zero Concatenation.zero_ne_one hx hy hz hz' h

/--
If `x` and `y` are `0`-tallies and `z`, `z'` end with `1`, then `z ++ x = z' ++ y` implies `z = z'`
and `x = y`.
- [Gan09, §3, Lemma 7]
-/
lemma tally_separation' (hx : IsTally 0 x) (hy : IsTally 0 y) (hz : z ◧ 1)
    (hz' : z' ◧ 1) (h : z ++ x = z' ++ y) : z = z' ∧ x = y :=
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
      tally_separation hy hy' (isSuffix_append x 0) (isSuffix_append x' 0) h
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
lemma configuration_eq_of_isSuffix (hs : s ◧ 0) (hs' : s' ◧ 0)
    (h : s ++ (pairOf u v ++ 0 ++ 0) = s' ++ (pairOf u' v' ++ 0 ++ 0)) :
    s = s' ∧ u = u' ∧ v = v' := by
  simp only [pairOf, ← Concatenation.append_assoc] at h
  obtain ⟨h₁, rfl⟩ := tally_separation hv hv' (isSuffix_append _ _) (isSuffix_append _ _)
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
  obtain ⟨h₁, h₂⟩ := configuration_eq_of_isSuffix hu hv hu' hv'
    (isSuffix_append (s ++ 0) 0) (isSuffix_append (s' ++ 0) 0) <| by
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

end separation

section mulSeq

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]
  {a b k p q r s t u v w w' x y z : M}

section pairOf

lemma IsTally.isPrefix_pairOf_append (hp : IsTally 1 p) : 1 ◨ pairOf p q ++ 0 ++ 0 :=
  hp.isPrefix.append_right.append_right.append_right.append_right

variable (hp : IsTally 1 p) (hq : IsTally 1 q)
include hp hq

lemma eq_zero_or_eq_zero_zero_of_isSubstring_pairOf (ht : IsTally 0 t)
    (h : IsSubstring t (pairOf p q ++ 0 ++ 0)) : t = 0 ∨ t = 0 ++ 0 := by
  simp only [pairOf, Concatenation.append_assoc] at h
  rcases ht.isSubstring_or_isSubstring h (Or.inl hp.isSuffix) with h | h
  · exact absurd h (ht.not_isSubstring_of_isTally_one hp)
  rcases ht.isSubstring_or_isSubstring h (Or.inr hq.isPrefix.append_right) with h | h
  · exact Or.inl <| isAtom_zero.eq_of_isSubstring h
  rcases ht.isSubstring_or_isSubstring h (Or.inl hq.isSuffix) with h | h
  · exact absurd h (ht.not_isSubstring_of_isTally_one hq)
  · exact eq_zero_or_eq_zero_zero_of_isSubstring h

lemma not_isSubstring_zero_zero_append_pairOf :
    ¬IsSubstring (0 ++ 0 ++ z) (pairOf p q ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := isAtom_zero
  have H : ∀ {r t₁ t₂ : M}, IsTally 1 r → r ◧ t₁ → 0 ++ (0 ++ z) = t₁ ++ t₂ → False := by
    intro r t₁ t₂ hr h₁ he
    have h₂ : 0 ◨ t₁ := (isPrefix_append t₁ t₂).isPrefix_of_isAtom h0
      (he ▸ isPrefix_append 0 (0 ++ z))
    exact (hr.of_isSubstring h₁.isSubstring).not_isSubstring_zero h₂.isSubstring
  intro h
  simp only [pairOf, Concatenation.append_assoc] at h
  rcases h.append_cases with h | h | ⟨t₁, t₂, he, h₁, -⟩
  · exact hp.not_isSubstring_zero <| (isSubstring_append_left 0 _).trans h
  · rcases h.append_cases with h | h | ⟨t₁, t₂, he, h₁, h₂⟩
    · exact zero_ne_append _ _ (h0.eq_of_isSubstring h).symm
    · rcases h.append_cases with h | h | ⟨t₁, t₂, he, h₁, -⟩
      · exact hq.not_isSubstring_zero <| (isSubstring_append_left 0 _).trans h
      · rcases eq_zero_or_eq_zero_zero_of_isSubstring h with h | h
        · exact zero_ne_append _ _ h.symm
        · exact zero_ne_append _ _ (h0.append_left_cancel h).symm
      · exact H hq h₁ he
    · obtain rfl := h0.eq_of_isSubstring h₁.isSubstring
      obtain rfl := h0.append_left_cancel he
      exact Concatenation.zero_ne_one <| ((isPrefix_append 0 z).trans h₂).eq_of_isAtom h0
        isAtom_one hq.isPrefix.append_right
  · exact H hp h₁ he

lemma eq_of_isPrefix_pairOf (h : k ++ 0 ++ 0 ◨ pairOf p q ++ 0 ++ 0) : k = pairOf p q := by
  rcases h with h | ⟨t, h⟩
  · exact isAtom_zero.append_right_cancel <| isAtom_zero.append_right_cancel h
  · apply absurd _ (not_isSubstring_zero_zero_append_pairOf (z := t) hp hq)
    rw [h]
    simp [Concatenation.append_assoc]

lemma eq_of_isSuffix_of_isPrefix_pairOf (h : z ++ 0 ++ 0 ◧ k)
    (h' : k ◨ pairOf p q ++ 0 ++ 0) : k = pairOf p q ++ 0 ++ 0 := by
  have h1 : 1 ◨ k :=
    h'.isPrefix_of_isAtom isAtom_one hp.isPrefix_pairOf_append
  have hn : ¬IsSubstring k (0 ++ 0) := fun h ↦
    (isTally_zero_zero.of_isSubstring h).not_isSubstring_one h1.isSubstring
  have h00 : z ++ 0 ++ 0 ◧ 0 ++ 0 := by
    right; use z; simp [Concatenation.append_assoc]
  rcases h.total h00 with h | h | ⟨j, rfl⟩
  · exact absurd h.isSubstring hn
  · exact absurd (h ▸ IsSubstring.refl _) hn
  · rw [← Concatenation.append_assoc, eq_of_isPrefix_pairOf (k := j) hp hq]
    simpa only [Concatenation.append_assoc] using h'

lemma isPrefix_append_pairOf_cases (h : z ++ 0 ++ 0 ◨ x ++ (pairOf p q ++ 0 ++ 0)) :
    z ++ 0 ++ 0 ◨ x ∨ z ++ 0 ++ 0 = x ++ (pairOf p q ++ 0 ++ 0) := by
  rcases h with h | ⟨t, h⟩
  · exact Or.inr h
  rcases editor h with ⟨rfl, -⟩ | ⟨m, ⟨hm, hm'⟩ | ⟨rfl, -⟩⟩
  · simp
  · right
    rw [← hm, ← eq_of_isSuffix_of_isPrefix_pairOf hp hq
      (hm ▸ isSuffix_append x m) (hm' ▸ isPrefix_append m t)]
  · simp

lemma isSubstring_append_pairOf_cases
    (h : IsSubstring (0 ++ 0 ++ z ++ 0 ++ 0) (x ++ (pairOf p q ++ 0 ++ 0))) :
    IsSubstring (0 ++ 0 ++ z ++ 0 ++ 0) x ∨
      ∃ z₁, x ◧ z₁ ∧ 0 ++ 0 ++ z ++ 0 ++ 0 = z₁ ++ (pairOf p q ++ 0 ++ 0) := by
  rcases h.append_cases with h | h | ⟨z₁, z₂, he, h₁, h₂⟩
  · exact Or.inl h
  · apply absurd _ (not_isSubstring_zero_zero_append_pairOf (z := z ++ 0 ++ 0) hp hq)
    simpa only [Concatenation.append_assoc] using h
  · right
    use z₁, h₁
    rwa [← eq_of_isSuffix_of_isPrefix_pairOf hp hq
      (he ▸ isSuffix_append z₁ z₂) h₂]

end pairOf

lemma isSubstring_zero_zero_of_isSuffix (hx : x ◧ 1 ++ 0 ++ 0)
    (hu : x ◧ 0 ++ 0 ++ u) : IsSubstring (0 ++ 0) u := by
  have h0 : IsAtom (0 : M) := isAtom_zero
  have h100 : IsSubstring (0 ++ 0 : M) (1 ++ 0 ++ 0) := by
    simp [Concatenation.append_assoc]
  rcases hu.total hx with h | h
  · exfalso
    rcases eq_of_isSuffix_isAtom_zero_zero isAtom_one h with h | h | h
    · exact zero_ne_append _ _ h.symm
    · exact zero_zero_append_ne_zero_zero h
    · have h₁ : (0 : M) ◨ 0 ++ 0 ++ u := by simp [Concatenation.append_assoc]
      have h₂ : (1 : M) ◨ 1 ++ 0 ++ 0 := by simp [Concatenation.append_assoc]
      exact Concatenation.zero_ne_one <| h₁.eq_of_isAtom h0 isAtom_one (h ▸ h₂)
  · rcases h.total (isSuffix_append (0 ++ 0) u) with h' | h'
    · exact h100.trans h'.isSubstring
    · rcases eq_of_isSuffix_isAtom_zero_zero isAtom_one h' with rfl | rfl | rfl
      · exfalso
        rcases eq_of_isSuffix_isAtom_zero_zero h0 h with h | h | h
        · exact zero_ne_append _ _ h.symm
        · exact zero_ne_append _ _ (h0.append_right_cancel h).symm
        · exact Concatenation.zero_ne_one (h0.append_right_cancel <| h0.append_right_cancel h).symm
      · simp
      · exact h100

lemma IsLast.pairOf_inj (hu : IsTally 1 u) (hv : IsTally 1 v) (hp : IsTally 1 p) (hq : IsTally 1 q)
    (h : IsLast (pairOf u v) z) (h' : IsLast (pairOf p q) z) : u = p ∧ v = q := by
  rcases h with rfl | ⟨k, rfl⟩ <;> rcases h' with h' | ⟨k', h'⟩
  · exact configuration_eq_of_no_prefix hu hv hp hq h'.symm
  · exact absurd h' (configuration_ne hu hv hp hq)
  · exact absurd h' (configuration_ne hp hq hu hv)
  · exact (configuration_eq hu hv hp hq h').2

lemma IsSeq.isSuffix_zero_zero (h : IsSeq z) : z ◧ 0 ++ 0 := by
  have h₁ : 1 ++ 0 ++ 0 ◧ (0 ++ 0 : M) := by
    right; use 1; simp [Concatenation.append_assoc]
  exact h₁.trans h.isSuffix

lemma isLast_append (h : z ◧ 0 ++ 0) : IsLast u (z ++ u ++ 0 ++ 0) := by
  grind [IsLast, IsSuffix, Concatenation.append_assoc]

lemma IsFirst.of_append_pairOf (hp : IsTally 1 p) (hq : IsTally 1 q)
    (h : IsFirst (pairOf p q) (k ++ 0 ++ 0 ++ pairOf u v ++ 0 ++ 0)) :
    IsFirst (pairOf p q) (k ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := isAtom_zero
  have h1 : IsAtom (1 : M) := isAtom_one
  obtain ⟨w, hw, hs⟩ : ∃ w, pairOf p q ++ 0 ++ 0 ◨ w ∧
      (0 ++ 0) ++ w = k ++ ((0 ++ 0) ++ (pairOf u v ++ 0 ++ 0)) := by
    rcases h with h | ⟨t, h⟩
    · use pairOf p q ++ 0 ++ 0
      simpa [Concatenation.append_assoc] using h
    · use pairOf p q ++ 0 ++ 0 ++ t
      exact ⟨by simp, by simpa only [Concatenation.append_assoc] using h.symm⟩
  have hw1 : 1 ◨ w := hp.isPrefix_pairOf_append.trans hw
  have H : ¬0 ◨ w := fun h ↦ Concatenation.zero_ne_one <| h.eq_of_isAtom h0 h1 hw1
  rcases editor hs with ⟨rfl, rfl⟩ | ⟨m, ⟨rfl, hm⟩ | ⟨hm, hm'⟩⟩
  · exact absurd (by simp [Concatenation.append_assoc]) H
  · have h₁ : m ++ 0 ++ 0 ◨ w := by
      rw [hm]; right; use pairOf u v ++ 0 ++ 0; simp [Concatenation.append_assoc]
    have h₂ : pairOf p q ++ 0 ++ 0 ◨ m ++ 0 ++ 0 := by
      rcases hw.total h₁ with h₃ | h₃
      · exact h₃
      · rw [eq_of_isPrefix_pairOf hp hq h₃]
    rcases h₂ with h₂ | ⟨t, h₂⟩
    · left; simp only [Concatenation.append_assoc] at h₂ ⊢; rw [h₂]
    · right; use t; simp only [Concatenation.append_assoc] at h₂ ⊢; rw [h₂]
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_append_eq_append_isAtom h0 h0 hm.symm
    have h₂ : w = 0 ++ (pairOf u v ++ 0 ++ 0) :=
      h0.append_left_cancel <| hm'.trans <| Concatenation.append_assoc 0 0 _
    exact absurd (by rw [h₂]; simp) H

lemma IsTally.isPrefix_zero_zero_one (hx : IsTally 1 x) :
    0 ++ 0 ++ 1 ◨ 0 ++ 0 ++ pairOf x y ++ 0 ++ 0 := by
  rcases hx.isPrefix with rfl | ⟨x', rfl⟩
  · right; use 0 ++ y ++ 0 ++ 0; simp [pairOf, Concatenation.append_assoc]
  · right; use x' ++ 0 ++ y ++ 0 ++ 0; simp [pairOf, Concatenation.append_assoc]

section append

variable (ha : IsTally 1 a) (hb : IsTally 1 b)
include ha hb

lemma isSeq_append_pairOf (hr : IsSeq r) : IsSeq (r ++ pairOf a b ++ 0 ++ 0) := by
  constructor
  · exact hr.isPrefix.append_right.append_right.append_right
  · rcases hb.isSuffix with rfl | ⟨b', rfl⟩
    · right; use r ++ a ++ 0; simp [pairOf, Concatenation.append_assoc]
    · right; use r ++ a ++ 0 ++ b'; simp [pairOf, Concatenation.append_assoc]
  · intro t ht h
    simp only [Concatenation.append_assoc r] at h
    rcases ht.isSubstring_or_isSubstring h (Or.inr ha.isPrefix_pairOf_append) with h | h
    · exact hr.eq_of_isTally t ht h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring_pairOf ha hb ht h

lemma isSeq_zero_zero_append_pairOf : IsSeq (0 ++ 0 ++ pairOf a b ++ 0 ++ 0) := by
  constructor
  · exact ha.isPrefix_zero_zero_one
  · simpa only [pairOf, Concatenation.append_assoc] using
      (hb.isSuffix.append_left (u := 0 ++ 0 ++ a ++ 0)).append_congr (z := 0 ++ 0)
  · intro t ht h
    simp only [Concatenation.append_assoc (0 ++ 0 : M)] at h
    rcases ht.isSubstring_or_isSubstring h (Or.inr ha.isPrefix_pairOf_append) with h | h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring_pairOf ha hb ht h

lemma isPairSeq_zero_zero_append_pairOf : IsPairSeq (0 ++ 0 ++ pairOf a b ++ 0 ++ 0) := by
  apply And.intro <| isSeq_zero_zero_append_pairOf ha hb
  rintro v ⟨-, -, h⟩
  rw [show 0 ++ 0 ++ pairOf a b ++ 0 ++ 0 = 0 ++ 0 ++ (pairOf a b ++ 0 ++ 0) by
    simp [Concatenation.append_assoc]] at h
  rcases isSubstring_append_pairOf_cases ha hb h with h | ⟨z, hz, h⟩
  · rcases eq_zero_or_eq_zero_zero_of_isSubstring h with h | h
    · simp at h
    · apply absurd h
      simpa only [Concatenation.append_assoc] using
        zero_zero_append_ne_zero_zero (x := v ++ (0 ++ 0))
  · use a, b, ha, hb
    rcases eq_zero_or_eq_zero_zero_of_isSubstring hz.isSubstring with rfl | rfl
    · simp only [Concatenation.append_assoc] at h
      have h₁ : 0 ◨ pairOf a b ++ 0 ++ 0 := by
        simp only [Concatenation.append_assoc, ← isAtom_zero.append_left_cancel h]
        simp
      exact absurd (h₁.eq_of_isAtom isAtom_zero isAtom_one ha.isPrefix_pairOf_append)
        Concatenation.zero_ne_one
    · apply isAtom_zero.append_left_cancel
      apply isAtom_zero.append_left_cancel
      apply isAtom_zero.append_right_cancel
      apply isAtom_zero.append_right_cancel
      simpa only [Concatenation.append_assoc] using h

lemma isPairSeq_append_pairOf (hr : IsPairSeq r) : IsPairSeq (r ++ pairOf a b ++ 0 ++ 0) := by
  apply And.intro <| isSeq_append_pairOf ha hb hr.isSeq
  rintro v ⟨-, hv, h⟩
  simp only [Concatenation.append_assoc r] at h
  rcases isSubstring_append_pairOf_cases ha hb h with h | ⟨z₁, hz₁, h⟩
  · exact hr.2 v ⟨hr.isSeq, hv, h⟩
  have h' : z₁ ++ pairOf a b = 0 ++ 0 ++ v := by
    apply isAtom_zero.append_right_cancel
    apply isAtom_zero.append_right_cancel
    rw [h]
    simp [Concatenation.append_assoc]
  rcases editor h' with ⟨rfl, rfl⟩ | ⟨m, ⟨hm, hm'⟩ | ⟨rfl, rfl⟩⟩
  · use a, b
  · have h₁ : IsTally 0 m := isTally_zero_zero.of_isSubstring (hm ▸ isSubstring_append_right z₁ m)
    have h₂ : 1 ◨ m := (hm' ▸ isPrefix_append m v :
      m ◨ pairOf a b).isPrefix_of_isAtom isAtom_one
        ha.isPrefix.append_right.append_right
    exact absurd h₂.isSubstring h₁.not_isSubstring_one
  · exact absurd ((isSubstring_zero_zero_of_isSuffix hr.isSeq.isSuffix hz₁).trans
      (isSubstring_append_left m _)) hv

end append

lemma IsFirst.pairOf_inj (hq : IsTally 1 q) (ha : IsTally 1 a) (hb : IsTally 1 b)
    (h : IsFirst (pairOf p q) (0 ++ 0 ++ pairOf a b ++ 0 ++ 0)) : p = a ∧ q = b := by
  have h₁ : pairOf p q ++ 0 ++ 0 ◨ pairOf a b ++ 0 ++ 0 := by
    apply IsPrefix.of_append_left_isAtom isAtom_zero
    apply IsPrefix.of_append_left_isAtom isAtom_zero
    simpa only [IsFirst, Concatenation.append_assoc] using h
  exact (FFL.FirstOrder.Concatenation.pairOf_inj hq hb).mp <|
    eq_of_isPrefix_pairOf ha hb h₁

/--
A multiplication sequence for `x` and `y 1` is `k 0 0 a 0 (y 1) 0 0` for some `k` and some `1`-tally
`a`.
- [Gan09, §3, Theorem 4]
-/
lemma IsMulSeq.exists_eq_append_pairOf (hs : IsMulSeq x (y ++ 1) s) :
    ∃ k a, IsTally 1 a ∧ s = k ++ 0 ++ 0 ++ pairOf a (y ++ 1) ++ 0 ++ 0 := by
  obtain ⟨hx, hy1, -, hfirst, ⟨a, ha, h | ⟨k, rfl⟩⟩, -⟩ := hs
  · rw [← h] at hfirst
    exact absurd (hfirst.pairOf_inj isTally_one_one ha hy1).2 (one_ne_append y 1)
  · use k, a, ha
    simp [Concatenation.append_assoc]

lemma IsPairSeq.of_append_pairOf (hs : IsPairSeq (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0))
    (hp : IsTally 1 p) (hfirst : IsFirst (pairOf p q) (k ++ 0 ++ 0)) : IsPairSeq (k ++ 0 ++ 0) := by
  have hsub : IsSubstring (k ++ 0 ++ 0) (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0) :=
    ((isSubstring_append_left _ _).append_right).append_right
  have hseq : IsSeq (k ++ 0 ++ 0) := by
    constructor
    · exact hp.isPrefix_zero_zero_one.trans hfirst
    · obtain ⟨c, hc, hk⟩ := exists_isSuffix_isAtom k
      rcases hc with rfl | rfl
      · exfalso
        have h₁ : IsSubstring (0 ++ 0 ++ 0) (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0) :=
          hk.append_congr.append_congr.isSubstring.trans hsub
        rcases hs.isSeq.eq_of_isTally _ (isTally_zero_zero.append (isTally_self isAtom_zero)) h₁
          with h | h
        · exact zero_ne_append _ _ h.symm
        · exact zero_ne_append _ _ (isAtom_zero.append_right_cancel h).symm
      · exact hk.append_congr.append_congr
    · exact fun t ht h ↦ hs.isSeq.eq_of_isTally t ht (h.trans hsub)
  exact ⟨hseq, fun v ⟨_, hv, h⟩ ↦ hs.2 v ⟨hs.isSeq, hv, h.trans hsub⟩⟩

lemma IsLast.exists_eq_append (h : IsLast u z) : ∃ k, k ◧ 0 ++ 0 ++ u ∧ z = k ++ 0 ++ 0 := by
  rcases h with rfl | ⟨k, rfl⟩
  · use 0 ++ 0 ++ u
  · use k ++ (0 ++ 0 ++ u)
    simp [Concatenation.append_assoc]

/--
If `r` is a multiplication sequence for `x` and `y` with last member `(w, y)`, then
`r (w x) 0 (y 1) 0 0` is a multiplication sequence for `x` and `y 1`.
- [Gan09, §3, Theorem 4]
- [Sve09, §3]
-/
lemma IsMulSeq.extend (hr : IsMulSeq x y r) (hw : IsTally 1 w) (hlast : IsLast (pairOf w y) r) :
    IsMulSeq x (y ++ 1) (r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0) := by
  obtain ⟨hx, hy, hps, hfirst, -, hrec⟩ := hr
  have ha := hw.append hx
  have hb := hy.append_one
  refine ⟨hx, hb, isPairSeq_append_pairOf ha hb hps, hfirst.append_right.append_right.append_right,
    ⟨w ++ x, ha, isLast_append hps.isSeq.isSuffix_zero_zero⟩, ?_⟩
  intro s u' v' hu' hv' h
  simp only [Concatenation.append_assoc r] at h
  rcases isPrefix_append_pairOf_cases ha hb h with h | h
  · exact hrec s u' v' hu' hv' h
  · obtain ⟨k, hk, rfl⟩ := hlast.exists_eq_append
    obtain ⟨rfl, rfl, rfl⟩ := configuration_eq hu' hv' ha hb <| by
      simpa only [Concatenation.append_assoc] using h
    use w, y

lemma IsMulSeq.isLast_extend (hr : IsMulSeq x y r) :
    IsLast (pairOf (w ++ x) (y ++ 1)) (r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0) :=
  isLast_append hr.isPairSeq.isSeq.isSuffix_zero_zero

lemma IsMulSeq.isLast_unique (hr : IsMulSeq x y r) (hw : IsTally 1 w) (hw' : IsTally 1 w')
    (h : IsLast (pairOf w y) r) (h' : IsLast (pairOf w' y) r) : w = w' :=
  (h.pairOf_inj hw hr.isTally_right hw' hr.isTally_right h').1

/--
Every multiplication sequence for `x` and `y 1` is `r (w x) 0 (y 1) 0 0` for some multiplication
sequence `r` for `x` and `y` with last member `(w, y)`.
- [Gan09, §3, Theorem 4]
- [Sve09, §3, Lemma 5]
-/
lemma IsMulSeq.restrict (hs : IsMulSeq x (y ++ 1) s) : ∃ r w, IsTally 1 w ∧ IsMulSeq x y r ∧
    IsLast (pairOf w y) r ∧ s = r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0 := by
  obtain ⟨k, a, ha, rfl⟩ := hs.exists_eq_append_pairOf
  obtain ⟨hx, hy1, hps, hfirst, -, hrec⟩ := hs
  obtain ⟨u, v, hu, hv, rfl, h, hk⟩ := hrec k a (y ++ 1) ha hy1 (IsPrefix.refl _)
  obtain rfl := isAtom_one.append_right_cancel h
  have hfirst' := hfirst.of_append_pairOf hx isTally_one_one
  have hlast : IsLast (pairOf u y) (k ++ 0 ++ 0) := hk.append_congr.append_congr
  use k ++ 0 ++ 0, u
  exact ⟨hu, ⟨hx, hv, hps.of_append_pairOf hx hfirst', hfirst', ⟨u, hu, hlast⟩,
    fun s u' v' hu' hv' h ↦ hrec s u' v' hu' hv' h.append_right.append_right.append_right⟩,
    hlast, rfl⟩

/--
For a `1`-tally `x`, the only multiplication sequence for `x` and `1` is `0 0 x 0 1 0 0`.
- [Gan09, §1]
- [Sve09, §3]
-/
lemma isMulSeq_one_iff (hx : IsTally 1 x) :
    IsMulSeq x 1 r ↔ r = 0 ++ 0 ++ pairOf x 1 ++ 0 ++ 0 := by
  have h1 : IsTally (1 : M) 1 := isTally_one_one
  constructor
  · rintro ⟨-, -, -, hfirst, ⟨w, hw, rfl | ⟨k, rfl⟩⟩, hrec⟩
    · rw [(hfirst.pairOf_inj h1 hw h1).1]
    · obtain ⟨u, v, -, -, -, h, -⟩ := hrec k w 1 hw h1 <| by
        left; simp only [Concatenation.append_assoc]
      exact absurd h (one_ne_append v 1)
  · rintro rfl
    refine ⟨hx, h1, isPairSeq_zero_zero_append_pairOf hx h1, IsPrefix.refl _,
      ⟨x, hx, IsSuffix.refl _⟩, ?_⟩
    intro s u' v' hu' hv' h
    exfalso
    simp only [Concatenation.append_assoc (0 ++ 0 : M)] at h
    rcases isPrefix_append_pairOf_cases hx h1 h with h | h
    · have h₁ : IsSubstring (pairOf u' v') (0 ++ 0 : M) :=
        (isSubstring_append_append _ _ _).trans <| (isSubstring_append_left _ 0).trans h.isSubstring
      have h₂ : IsSubstring u' (pairOf u' v') := (isSubstring_append_left u' 0).append_right
      exact (isTally_zero_zero.of_isSubstring <| h₂.trans h₁).not_isSubstring_of_isTally_one hu'
        (IsSubstring.refl _)
    · apply configuration_ne hx h1 hu' hv' (s' := s)
      simpa only [Concatenation.append_assoc] using h.symm

lemma existsUnique_isMulSeq_one (hx : IsTally 1 x) : ∃! r, IsMulSeq x 1 r := by
  simp [isMulSeq_one_iff hx]

/--
For a `1`-tally `x`, there is exactly one multiplication sequence for `x` and `y 1` if and only if
there is exactly one for `x` and `y`.
- [Gan09, §3, Theorem 4]
- [Sve09, §3, Lemma 5]
-/
theorem existsUnique_isMulSeq_succ_iff (hx : IsTally 1 x) : (∃! r, IsMulSeq x (y ++ 1) r) ↔
    ∃! r, IsMulSeq x y r := by
  constructor
  · rintro ⟨s, hs, huniq⟩
    obtain ⟨r, w, hw, hr, hl, rfl⟩ := hs.restrict
    apply ExistsUnique.intro r hr
    intro r' hr'
    obtain ⟨w', hw', hl'⟩ := hr'.exists_isLast
    have H {r} (hr : IsMulSeq x y r) : r ◧ 0 :=
      (isSuffix_append (0 : M) 0).trans hr.isPairSeq.isSeq.isSuffix_zero_zero
    exact (configuration_eq_of_isSuffix (hw'.append hx) hs.isTally_right (hw.append hx)
      hs.isTally_right (H hr') (H hr) <| by
        simpa only [Concatenation.append_assoc] using huniq _ (hr'.extend hw' hl')).1
  · rintro ⟨r, hr, huniq⟩
    obtain ⟨w, hw, hl⟩ := hr.exists_isLast
    apply ExistsUnique.intro _ <| hr.extend hw hl
    intro s hs
    obtain ⟨r', w', hw', hr', hl', rfl⟩ := hs.restrict
    obtain rfl := huniq _ hr'
    rw [hr.isLast_unique hw' hw hl' hl]

/--
If there is exactly one multiplication sequence for `x` and `y`, with last member `(w, y)`, then the
last member of a multiplication sequence for `x` and `y 1` is `(w x, y 1)`.
- [Gan09, §3, Theorem 4]
-/
lemma IsMulSeq.isLast_of_existsUnique (h : ∃! r, IsMulSeq x y r) (hr : IsMulSeq x y r)
    (hw : IsTally 1 w) (hlast : IsLast (pairOf w y) r) (hs : IsMulSeq x (y ++ 1) s) :
    IsLast (pairOf (w ++ x) (y ++ 1)) s := by
  obtain rfl := ((existsUnique_isMulSeq_succ_iff hr.isTally_left).mpr h).unique hs
    (hr.extend hw hlast)
  exact hr.isLast_extend

end mulSeq

end FFL.FirstOrder.Concatenation

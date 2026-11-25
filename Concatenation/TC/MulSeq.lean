module

public import Concatenation.TC.Separation

/-!
# Extension and restriction of multiplication sequences

How a multiplication sequence for $x, y$ and one for $x, y a$ determine each other in
$\mathsf{TC}^+$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]
  {a b k p q r s t u v w w' x y z : M}

section pairOf

lemma IsTally.isInitialSegment_pairOf_append (hp : IsTally 1 p) :
    IsInitialSegment 1 (pairOf p q ++ 0 ++ 0) :=
  hp.isInitialSegment.append_right.append_right.append_right.append_right

variable (hp : IsTally 1 p) (hq : IsTally 1 q)
include hp hq

lemma eq_zero_or_eq_zero_zero_of_isSubstring_pairOf (ht : IsTally 0 t)
    (h : IsSubstring t (pairOf p q ++ 0 ++ 0)) : t = 0 ∨ t = 0 ++ 0 := by
  simp only [pairOf, Concatenation.append_assoc] at h
  rcases ht.isSubstring_or_isSubstring h (Or.inl hp.isEndSegment) with h | h
  · exact absurd h (ht.not_isSubstring_of_isTally_one hp)
  rcases ht.isSubstring_or_isSubstring h (Or.inr hq.isInitialSegment.append_right) with h | h
  · exact Or.inl <| IsAtom.eq_of_isSubstring (Or.inl rfl) h
  rcases ht.isSubstring_or_isSubstring h (Or.inl hq.isEndSegment) with h | h
  · exact absurd h (ht.not_isSubstring_of_isTally_one hq)
  · exact eq_zero_or_eq_zero_zero_of_isSubstring h

lemma not_isSubstring_zero_zero_append_pairOf :
    ¬IsSubstring (0 ++ 0 ++ z) (pairOf p q ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  have H : ∀ {r t₁ t₂ : M}, IsTally 1 r → IsEndSegment t₁ r → 0 ++ (0 ++ z) = t₁ ++ t₂ → False := by
    intro r t₁ t₂ hr h₁ he
    have h₂ : IsInitialSegment 0 t₁ := (isInitialSegment_append t₁ t₂).isInitialSegment_of_isAtom h0
      (he ▸ isInitialSegment_append 0 (0 ++ z))
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
      exact Concatenation.zero_ne_one <| ((isInitialSegment_append 0 z).trans h₂).eq_of_isAtom h0
        (Or.inr rfl) hq.isInitialSegment.append_right
  · exact H hp h₁ he

lemma eq_of_isInitialSegment_pairOf (h : IsInitialSegment (k ++ 0 ++ 0) (pairOf p q ++ 0 ++ 0)) :
    k = pairOf p q := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  rcases h with h | ⟨t, h⟩
  · exact h0.append_right_cancel <| h0.append_right_cancel h
  · refine absurd ?_ (not_isSubstring_zero_zero_append_pairOf (z := t) hp hq)
    rw [h]
    simp [Concatenation.append_assoc]

lemma eq_of_isEndSegment_of_isInitialSegment_pairOf (h : IsEndSegment k (z ++ 0 ++ 0))
    (h' : IsInitialSegment k (pairOf p q ++ 0 ++ 0)) : k = pairOf p q ++ 0 ++ 0 := by
  have h1 : IsInitialSegment 1 k :=
    h'.isInitialSegment_of_isAtom (Or.inr rfl) hp.isInitialSegment_pairOf_append
  have hn : ¬IsSubstring k (0 ++ 0) := fun h ↦
    (isTally_zero_zero.of_isSubstring h).not_isSubstring_one h1.isSubstring
  have h00 : IsEndSegment (0 ++ 0) (z ++ 0 ++ 0) := by
    right; use z; simp [Concatenation.append_assoc]
  rcases h.total h00 with h | h | ⟨j, rfl⟩
  · exact absurd h.isSubstring hn
  · exact absurd (h ▸ IsSubstring.refl _) hn
  · rw [← Concatenation.append_assoc, eq_of_isInitialSegment_pairOf (k := j) hp hq]
    simpa only [Concatenation.append_assoc] using h'

lemma isInitialSegment_append_pairOf_cases
    (h : IsInitialSegment (z ++ 0 ++ 0) (x ++ (pairOf p q ++ 0 ++ 0))) :
    IsInitialSegment (z ++ 0 ++ 0) x ∨ z ++ 0 ++ 0 = x ++ (pairOf p q ++ 0 ++ 0) := by
  rcases h with h | ⟨t, h⟩
  · exact Or.inr h
  rcases editor h with ⟨rfl, -⟩ | ⟨m, ⟨hm, hm'⟩ | ⟨rfl, -⟩⟩
  · simp
  · right
    rw [← hm, ← eq_of_isEndSegment_of_isInitialSegment_pairOf hp hq
      (hm ▸ isEndSegment_append x m) (hm' ▸ isInitialSegment_append m t)]
  · simp

lemma isSubstring_append_pairOf_cases
    (h : IsSubstring (0 ++ 0 ++ z ++ 0 ++ 0) (x ++ (pairOf p q ++ 0 ++ 0))) :
    IsSubstring (0 ++ 0 ++ z ++ 0 ++ 0) x ∨
      ∃ z₁, IsEndSegment z₁ x ∧ 0 ++ 0 ++ z ++ 0 ++ 0 = z₁ ++ (pairOf p q ++ 0 ++ 0) := by
  rcases h.append_cases with h | h | ⟨z₁, z₂, he, h₁, h₂⟩
  · exact Or.inl h
  · refine absurd ?_ (not_isSubstring_zero_zero_append_pairOf (z := z ++ 0 ++ 0) hp hq)
    simpa only [Concatenation.append_assoc] using h
  · right
    use z₁
    and_intros
    · exact h₁
    rwa [← eq_of_isEndSegment_of_isInitialSegment_pairOf hp hq
      (he ▸ isEndSegment_append z₁ z₂) h₂]

end pairOf

lemma isSubstring_zero_zero_of_isEndSegment (hx : IsEndSegment (1 ++ 0 ++ 0) x)
    (hu : IsEndSegment (0 ++ 0 ++ u) x) : IsSubstring (0 ++ 0) u := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  have h100 : IsSubstring (0 ++ 0 : M) (1 ++ 0 ++ 0) := by
    simp [Concatenation.append_assoc]
  rcases hu.total hx with h | h
  · exfalso
    rcases eq_of_isEndSegment_isAtom_zero_zero (Or.inr rfl) h with h | h | h
    · exact zero_ne_append _ _ h.symm
    · exact zero_zero_append_ne_zero_zero h
    · have h₁ : IsInitialSegment (0 : M) (0 ++ 0 ++ u) := by simp [Concatenation.append_assoc]
      have h₂ : IsInitialSegment (1 : M) (1 ++ 0 ++ 0) := by simp [Concatenation.append_assoc]
      exact Concatenation.zero_ne_one <| h₁.eq_of_isAtom h0 (Or.inr rfl) (h ▸ h₂)
  · rcases h.total (isEndSegment_append (0 ++ 0) u) with h' | h'
    · exact h100.trans h'.isSubstring
    · rcases eq_of_isEndSegment_isAtom_zero_zero (Or.inr rfl) h' with rfl | rfl | rfl
      · exfalso
        rcases eq_of_isEndSegment_isAtom_zero_zero h0 h with h | h | h
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

lemma IsSeq.isEndSegment_zero_zero (h : IsSeq z) : IsEndSegment (0 ++ 0) z := by
  have h₁ : IsEndSegment (0 ++ 0 : M) (1 ++ 0 ++ 0) := by
    right; use 1; simp [Concatenation.append_assoc]
  exact h₁.trans h.2.1

lemma isLast_append_pairOf (h : IsEndSegment (0 ++ 0) z) : IsLast u (z ++ u ++ 0 ++ 0) := by
  rcases h with rfl | ⟨k, rfl⟩
  · exact IsEndSegment.refl _
  · right; use k; simp [Concatenation.append_assoc]

lemma IsFirst.of_append_pairOf (hp : IsTally 1 p) (hq : IsTally 1 q)
    (h : IsFirst (pairOf p q) (k ++ 0 ++ 0 ++ pairOf u v ++ 0 ++ 0)) :
    IsFirst (pairOf p q) (k ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  have h1 : IsAtom (1 : M) := Or.inr rfl
  obtain ⟨w, hw, hs⟩ : ∃ w, IsInitialSegment (pairOf p q ++ 0 ++ 0) w ∧
      (0 ++ 0) ++ w = k ++ ((0 ++ 0) ++ (pairOf u v ++ 0 ++ 0)) := by
    rcases h with h | ⟨t, h⟩
    · use pairOf p q ++ 0 ++ 0
      and_intros
      · rfl
      · simp only [Concatenation.append_assoc] at h ⊢; exact h
    · use pairOf p q ++ 0 ++ 0 ++ t
      and_intros
      · simp
      · simp only [Concatenation.append_assoc] at h ⊢; exact h.symm
  have hw1 : IsInitialSegment 1 w := hp.isInitialSegment_pairOf_append.trans hw
  have H : ¬IsInitialSegment 0 w := fun h ↦ Concatenation.zero_ne_one <| h.eq_of_isAtom h0 h1 hw1
  rcases editor hs with ⟨rfl, rfl⟩ | ⟨m, ⟨rfl, hm⟩ | ⟨hm, hm'⟩⟩
  · exact absurd (by simp [Concatenation.append_assoc]) H
  · have h₁ : IsInitialSegment (m ++ 0 ++ 0) w := by
      rw [hm]; right; use pairOf u v ++ 0 ++ 0; simp [Concatenation.append_assoc]
    have h₂ : IsInitialSegment (pairOf p q ++ 0 ++ 0) (m ++ 0 ++ 0) := by
      rcases hw.total h₁ with h₃ | h₃
      · exact h₃
      · rw [eq_of_isInitialSegment_pairOf hp hq h₃]
    rcases h₂ with h₂ | ⟨t, h₂⟩
    · left; simp only [Concatenation.append_assoc] at h₂ ⊢; rw [h₂]
    · right; use t; simp only [Concatenation.append_assoc] at h₂ ⊢; rw [h₂]
  · obtain ⟨rfl, rfl⟩ := eq_and_eq_of_append_eq_append_isAtom h0 h0 hm.symm
    have h₂ : w = 0 ++ (pairOf u v ++ 0 ++ 0) :=
      h0.append_left_cancel <| hm'.trans <| Concatenation.append_assoc 0 0 _
    exact absurd (by rw [h₂]; simp) H

lemma IsTally.isInitialSegment_zero_zero_one (hx : IsTally 1 x) :
    IsInitialSegment (0 ++ 0 ++ 1) (0 ++ 0 ++ pairOf x y ++ 0 ++ 0) := by
  rcases hx.isInitialSegment with rfl | ⟨x', rfl⟩
  · right; use 0 ++ y ++ 0 ++ 0; simp [pairOf, Concatenation.append_assoc]
  · right; use x' ++ 0 ++ y ++ 0 ++ 0; simp [pairOf, Concatenation.append_assoc]

lemma isSeq_append_pairOf (ha : IsTally 1 a) (hb : IsTally 1 b) (hr : IsSeq r) :
    IsSeq (r ++ pairOf a b ++ 0 ++ 0) := by
  and_intros
  · exact hr.1.append_right.append_right.append_right
  · rcases hb.isEndSegment with rfl | ⟨b', rfl⟩
    · right; use r ++ a ++ 0; simp [pairOf, Concatenation.append_assoc]
    · right; use r ++ a ++ 0 ++ b'; simp [pairOf, Concatenation.append_assoc]
  · intro t ht h
    rw [show r ++ pairOf a b ++ 0 ++ 0 = r ++ (pairOf a b ++ 0 ++ 0) by
      simp [Concatenation.append_assoc]] at h
    rcases ht.isSubstring_or_isSubstring h (Or.inr ha.isInitialSegment_pairOf_append) with h | h
    · exact hr.2.2 t ht h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring_pairOf ha hb ht h

lemma isSeq_zero_zero_append_pairOf (ha : IsTally 1 a) (hb : IsTally 1 b) :
    IsSeq (0 ++ 0 ++ pairOf a b ++ 0 ++ 0) := by
  and_intros
  · exact ha.isInitialSegment_zero_zero_one
  · simpa only [pairOf, Concatenation.append_assoc] using
      (hb.isEndSegment.append_left (u := 0 ++ 0 ++ a ++ 0)).append_congr (z := 0 ++ 0)
  · intro t ht h
    rw [show 0 ++ 0 ++ pairOf a b ++ 0 ++ 0 = 0 ++ 0 ++ (pairOf a b ++ 0 ++ 0) by
      simp [Concatenation.append_assoc]] at h
    rcases ht.isSubstring_or_isSubstring h (Or.inr ha.isInitialSegment_pairOf_append) with h | h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring h
    · exact eq_zero_or_eq_zero_zero_of_isSubstring_pairOf ha hb ht h

lemma isPairSeq_zero_zero_append_pairOf (ha : IsTally 1 a) (hb : IsTally 1 b) :
    IsPairSeq (0 ++ 0 ++ pairOf a b ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  apply And.intro <| isSeq_zero_zero_append_pairOf ha hb
  rintro v ⟨-, -, h⟩
  rw [show 0 ++ 0 ++ pairOf a b ++ 0 ++ 0 = 0 ++ 0 ++ (pairOf a b ++ 0 ++ 0) by
    simp [Concatenation.append_assoc]] at h
  rcases isSubstring_append_pairOf_cases ha hb h with h | ⟨z, hz, h⟩
  · rcases eq_zero_or_eq_zero_zero_of_isSubstring h with h | h
    · exact absurd h.symm (zero_ne_append _ _)
    · refine absurd h ?_
      simpa only [Concatenation.append_assoc] using
        zero_zero_append_ne_zero_zero (x := v ++ (0 ++ 0))
  · use a, b
    apply And.intro ha
    apply And.intro hb
    rcases eq_zero_or_eq_zero_zero_of_isSubstring hz.isSubstring with rfl | rfl
    · simp only [Concatenation.append_assoc] at h
      have h₁ : IsInitialSegment 0 (pairOf a b ++ 0 ++ 0) := by
        simp only [Concatenation.append_assoc, ← h0.append_left_cancel h]
        simp
      exact absurd (h₁.eq_of_isAtom h0 (Or.inr rfl) ha.isInitialSegment_pairOf_append)
        Concatenation.zero_ne_one
    · apply h0.append_left_cancel
      apply h0.append_left_cancel
      apply h0.append_right_cancel
      apply h0.append_right_cancel
      simpa only [Concatenation.append_assoc] using h

lemma isPairSeq_append_pairOf (ha : IsTally 1 a) (hb : IsTally 1 b) (hr : IsPairSeq r) :
    IsPairSeq (r ++ pairOf a b ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  apply And.intro <| isSeq_append_pairOf ha hb hr.isSeq
  rintro v ⟨-, hv, h⟩
  rw [show r ++ pairOf a b ++ 0 ++ 0 = r ++ (pairOf a b ++ 0 ++ 0) by
    simp [Concatenation.append_assoc]] at h
  rcases isSubstring_append_pairOf_cases ha hb h with h | ⟨z₁, hz₁, h⟩
  · exact hr.2 v ⟨hr.isSeq, hv, h⟩
  have h' : z₁ ++ pairOf a b = 0 ++ 0 ++ v := by
    apply h0.append_right_cancel
    apply h0.append_right_cancel
    rw [h]
    simp [Concatenation.append_assoc]
  rcases editor h' with ⟨rfl, rfl⟩ | ⟨m, ⟨hm, hm'⟩ | ⟨rfl, rfl⟩⟩
  · use a, b
  · have h₁ : IsTally 0 m := isTally_zero_zero.of_isSubstring (hm ▸ isSubstring_append_right z₁ m)
    have h₂ : IsInitialSegment 1 m := (hm' ▸ isInitialSegment_append m v :
      IsInitialSegment m (pairOf a b)).isInitialSegment_of_isAtom (Or.inr rfl)
        ha.isInitialSegment.append_right.append_right
    exact absurd h₂.isSubstring h₁.not_isSubstring_one
  · exact absurd ((isSubstring_zero_zero_of_isEndSegment hr.isSeq.2.1 hz₁).trans
      (isSubstring_append_left m _)) hv

lemma IsFirst.pairOf_inj (hq : IsTally 1 q) (ha : IsTally 1 a) (hb : IsTally 1 b)
    (h : IsFirst (pairOf p q) (0 ++ 0 ++ pairOf a b ++ 0 ++ 0)) : p = a ∧ q = b := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  have h₁ : IsInitialSegment (pairOf p q ++ 0 ++ 0) (pairOf a b ++ 0 ++ 0) := by
    apply IsInitialSegment.of_append_left_isAtom h0
    apply IsInitialSegment.of_append_left_isAtom h0
    simpa only [IsFirst, Concatenation.append_assoc] using h
  exact (FFL.FirstOrder.Concatenation.pairOf_inj hq hb).mp <|
    eq_of_isInitialSegment_pairOf ha hb h₁

/--
A multiplication sequence for `x` and `y 1` is `k 0 0 a 0 (y 1) 0 0` for some `k` and some `1`-tally
`a`.
- [Gan09, §3, Theorem 4]
-/
lemma IsMulSeq.exists_eq_append_pairOf (hs : IsMulSeq x (y ++ 1) s) :
    ∃ k a, IsTally 1 a ∧ s = k ++ 0 ++ 0 ++ pairOf a (y ++ 1) ++ 0 ++ 0 := by
  obtain ⟨hx, hy1, -, hfirst, ⟨a, ha, h | ⟨k, rfl⟩⟩, -⟩ := hs
  · rw [← h] at hfirst
    exact absurd (hfirst.pairOf_inj (isTally_self (Or.inr rfl)) ha hy1).2 (one_ne_append y 1)
  · use k, a
    and_intros
    · exact ha
    · simp [Concatenation.append_assoc]

lemma IsPairSeq.of_append_pairOf (hs : IsPairSeq (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0))
    (hp : IsTally 1 p) (hfirst : IsFirst (pairOf p q) (k ++ 0 ++ 0)) : IsPairSeq (k ++ 0 ++ 0) := by
  have h0 : IsAtom (0 : M) := Or.inl rfl
  have hsub : IsSubstring (k ++ 0 ++ 0) (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0) :=
    ((isSubstring_append_left _ _).append_right).append_right
  have hseq : IsSeq (k ++ 0 ++ 0) := by
    and_intros
    · exact hp.isInitialSegment_zero_zero_one.trans hfirst
    · obtain ⟨c, hc, hk⟩ := exists_isEndSegment_isAtom k
      rcases hc with rfl | rfl
      · exfalso
        have h₁ : IsSubstring (0 ++ 0 ++ 0) (k ++ 0 ++ 0 ++ pairOf a b ++ 0 ++ 0) :=
          hk.append_congr.append_congr.isSubstring.trans hsub
        rcases hs.isSeq.2.2 _ (isTally_zero_zero.append (isTally_self h0)) h₁ with h | h
        · exact zero_ne_append _ _ h.symm
        · exact zero_ne_append _ _ (h0.append_right_cancel h).symm
      · exact hk.append_congr.append_congr
    · exact fun t ht h ↦ hs.isSeq.2.2 t ht (h.trans hsub)
  exact ⟨hseq, fun v ⟨_, hv, h⟩ ↦ hs.2 v ⟨hs.isSeq, hv, h.trans hsub⟩⟩

lemma IsLast.exists_eq_append (h : IsLast u z) :
    ∃ k, IsEndSegment (0 ++ 0 ++ u) k ∧ z = k ++ 0 ++ 0 := by
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
theorem IsMulSeq.extend (hr : IsMulSeq x y r) (hw : IsTally 1 w) (hlast : IsLast (pairOf w y) r) :
    IsMulSeq x (y ++ 1) (r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0) := by
  obtain ⟨hx, hy, hps, hfirst, -, hrec⟩ := hr
  have ha := hw.append hx
  have hb := hy.append <| isTally_self <| Or.inr rfl
  refine ⟨hx, hb, isPairSeq_append_pairOf ha hb hps, hfirst.append_right.append_right.append_right,
    ⟨w ++ x, ha, isLast_append_pairOf hps.isSeq.isEndSegment_zero_zero⟩, ?_⟩
  intro s u' v' hu' hv' h
  rw [show r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0 = r ++ (pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0) by
    simp [Concatenation.append_assoc]] at h
  rcases isInitialSegment_append_pairOf_cases ha hb h with h | h
  · exact hrec s u' v' hu' hv' h
  · obtain ⟨k, hk, rfl⟩ := hlast.exists_eq_append
    obtain ⟨rfl, rfl, rfl⟩ := configuration_eq hu' hv' ha hb <| by
      simpa only [Concatenation.append_assoc] using h
    use w, y

lemma IsMulSeq.isLast_extend (hr : IsMulSeq x y r) :
    IsLast (pairOf (w ++ x) (y ++ 1)) (r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0) :=
  isLast_append_pairOf hr.isPairSeq.isSeq.isEndSegment_zero_zero

lemma IsMulSeq.isLast_unique (hr : IsMulSeq x y r) (hw : IsTally 1 w) (hw' : IsTally 1 w')
    (h : IsLast (pairOf w y) r) (h' : IsLast (pairOf w' y) r) : w = w' :=
  (h.pairOf_inj hw hr.isTally_right hw' hr.isTally_right h').1

/--
Every multiplication sequence for `x` and `y 1` is `r (w x) 0 (y 1) 0 0` for some multiplication
sequence `r` for `x` and `y` with last member `(w, y)`.
- [Gan09, §3, Theorem 4]
- [Sve09, §3, Lemma 5]
-/
theorem IsMulSeq.restrict (hs : IsMulSeq x (y ++ 1) s) (hy : IsTally 1 y) :
    ∃ r w, IsTally 1 w ∧ IsMulSeq x y r ∧ IsLast (pairOf w y) r ∧
      s = r ++ pairOf (w ++ x) (y ++ 1) ++ 0 ++ 0 := by
  obtain ⟨k, a, ha, rfl⟩ := hs.exists_eq_append_pairOf
  obtain ⟨hx, hy1, hps, hfirst, -, hrec⟩ := hs
  obtain ⟨u, v, hu, hv, rfl, h, hk⟩ := hrec k a (y ++ 1) ha hy1 (IsInitialSegment.refl _)
  obtain rfl := IsAtom.append_right_cancel (Or.inr rfl) h
  have hfirst' := hfirst.of_append_pairOf hx (isTally_self (Or.inr rfl))
  have hlast : IsLast (pairOf u y) (k ++ 0 ++ 0) := hk.append_congr.append_congr
  use k ++ 0 ++ 0, u
  exact ⟨hu, ⟨hx, hy, hps.of_append_pairOf hx hfirst', hfirst', ⟨u, hu, hlast⟩,
    fun s u' v' hu' hv' h ↦ hrec s u' v' hu' hv' h.append_right.append_right.append_right⟩,
    hlast, rfl⟩

/--
For a `1`-tally `x`, the only multiplication sequence for `x` and `1` is `0 0 x 0 1 0 0`.
- [Sve09, §3]
-/
lemma isMulSeq_one_iff (hx : IsTally 1 x) :
    IsMulSeq x 1 r ↔ r = 0 ++ 0 ++ pairOf x 1 ++ 0 ++ 0 := by
  have h1 : IsTally (1 : M) 1 := isTally_self <| Or.inr rfl
  constructor
  · rintro ⟨-, -, -, hfirst, ⟨w, hw, rfl | ⟨k, rfl⟩⟩, hrec⟩
    · rw [(hfirst.pairOf_inj h1 hw h1).1]
    · obtain ⟨u, v, -, -, -, h, -⟩ := hrec k w 1 hw h1 <| by
        left; simp only [Concatenation.append_assoc]
      exact absurd h (one_ne_append v 1)
  · rintro rfl
    refine ⟨hx, h1, isPairSeq_zero_zero_append_pairOf hx h1, IsInitialSegment.refl _,
      ⟨x, hx, IsEndSegment.refl _⟩, ?_⟩
    intro s u' v' hu' hv' h
    exfalso
    rw [show 0 ++ 0 ++ pairOf x 1 ++ 0 ++ 0 = 0 ++ 0 ++ (pairOf x 1 ++ 0 ++ 0) by
      simp [Concatenation.append_assoc]] at h
    rcases isInitialSegment_append_pairOf_cases hx h1 h with h | h
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
For `1`-tallies `x` and `y`, there is exactly one multiplication sequence for `x` and `y 1` if and
only if there is exactly one for `x` and `y`.
- [Gan09, §3, Theorem 4]
-/
theorem existsUnique_isMulSeq_succ_iff (hx : IsTally 1 x) (hy : IsTally 1 y) :
    (∃! r, IsMulSeq x (y ++ 1) r) ↔ ∃! r, IsMulSeq x y r := by
  constructor
  · rintro ⟨s, hs, huniq⟩
    obtain ⟨r, w, hw, hr, hl, rfl⟩ := hs.restrict hy
    apply ExistsUnique.intro r hr
    intro r' hr'
    obtain ⟨w', hw', hl'⟩ := hr'.2.2.2.2.1
    have H {r} (hr : IsMulSeq x y r) : IsEndSegment 0 r :=
      (isEndSegment_append (0 : M) 0).trans hr.isPairSeq.isSeq.isEndSegment_zero_zero
    exact (configuration_eq_of_isEndSegment (hw'.append hx) hs.isTally_right (hw.append hx)
      hs.isTally_right (H hr') (H hr) <| by
        simpa only [Concatenation.append_assoc] using huniq _ (hr'.extend hw' hl')).1
  · rintro ⟨r, hr, huniq⟩
    obtain ⟨w, hw, hl⟩ := hr.2.2.2.2.1
    apply ExistsUnique.intro _ <| hr.extend hw hl
    intro s hs
    obtain ⟨r', w', hw', hr', hl', rfl⟩ := hs.restrict hy
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
  obtain rfl := ((existsUnique_isMulSeq_succ_iff hr.isTally_left hr.isTally_right).mpr h).unique hs
    (hr.extend hw hlast)
  exact hr.isLast_extend

end FFL.FirstOrder.Concatenation

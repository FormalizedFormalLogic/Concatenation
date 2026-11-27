module

public import Concatenation.TC.Empty
public import Concatenation.WTC.Arithmetic

/-!
# $\mathsf{WTC}$ with and without the empty string

The neutrality of the empty string is redundant in $\mathsf{WTC}$ with the empty string, which is
mutually interpretable with $\mathsf{WTC}$ without it.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open ConcatenationStructure ConcatenationEmptyStructure DirectTranslation

lemma IsWTCEmptyMinusUnitAxiom.isWTCEmptyAxiom {σ : Sentence ℒ⌢ₑ}
    (h : IsWTCEmptyMinusUnitAxiom σ) : IsWTCEmptyAxiom σ := by
  cases h
  case equal hφ => exact .equal _ hφ
  case concatAssoc u => exact .concatAssoc u
  case editor u => exact .editor u
  all_goals first
    | exact .zeroNeEmpty | exact .zeroAtom | exact .oneNeEmpty | exact .oneAtom | exact .zeroNeOne

instance : 𝗪𝗧𝗖ₑ⁻ ⪯ 𝗪𝗧𝗖ₑ :=
  Entailment.WeakerThan.ofSubset fun _ ↦ IsWTCEmptyMinusUnitAxiom.isWTCEmptyAxiom

section models

variable {V : Type*} [ConcatenationEmptyStructure V] {c x y z s t : V} {u v : List Bool}

instance [V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ] : V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻ :=
  ⟨fun _ h ↦ Theory.models V 𝗪𝗧𝗖ₑ h.isWTCEmptyAxiom⟩

/--
`c` embeds the binary strings onto an initial part of `V`: if a concatenation is a standard string,
then so are its arguments.
-/
structure IsInitialEmptyEmbedding (c : List Bool → V) : Prop where
  injective : Function.Injective c
  map_nil : c [] = ∅
  map_false : c [false] = 0
  map_true : c [true] = 1
  map_append (u v : List Bool) : c (u ++ v) = c u ++ c v
  exists_of_append_eq {x y : V} {w : List Bool} (h : x ++ y = c w) : ∃ u v, x = c u ∧ y = c v

namespace IsInitialEmptyEmbedding

variable {c : List Bool → V} (hc : IsInitialEmptyEmbedding c)

include hc

lemma ofList_eq (u : List Bool) : ofList u = c u := by
  have hb (b : Bool) : ofList [b] = c [b] := by cases b <;> simp [hc.map_false, hc.map_true]
  induction u using List.reverseRecOn with
  | nil => exact hc.map_nil.symm
  | append_singleton u b ih =>
    rcases eq_or_ne u [] with rfl | hu
    · exact hb b
    · rw [ofList_append_singleton hu, ih, hb, ← hc.map_append]

lemma exists_of_isSubstring (h : IsSubstring x (c u)) : ∃ v, x = c v :=
  h.of_forall_append (P := fun x ↦ ∃ v, x = c v)
    (fun _ _ ⟨_, h⟩ ↦ let ⟨v, w, hv, hw⟩ := hc.exists_of_append_eq h; ⟨⟨v, hv⟩, ⟨w, hw⟩⟩) ⟨u, rfl⟩

lemma exists_of_isSubstring_append (h : IsSubstring (x ++ y) (c u)) :
    ∃ a b, x = c a ∧ y = c b := by
  obtain ⟨v, hv⟩ := hc.exists_of_isSubstring h
  exact hc.exists_of_append_eq hv

lemma append_empty (u : List Bool) : c u ++ ∅ = c u := by simp [← hc.map_nil, ← hc.map_append]

lemma empty_append (u : List Bool) : ∅ ++ c u = c u := by simp [← hc.map_nil, ← hc.map_append]

lemma append_assoc_of_isSubstring (h : IsSubstring (x ++ y ++ z) (c u) ∨
    IsSubstring (x ++ (y ++ z)) (c u)) : x ++ y ++ z = x ++ (y ++ z) := by
  obtain ⟨p, q, r, rfl, rfl, rfl⟩ : ∃ p q r, x = c p ∧ y = c q ∧ z = c r := by
    rcases h with h | h
    · obtain ⟨a, r, ha, rfl⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨p, q, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use p, q, r
    · obtain ⟨p, a, rfl, ha⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨q, r, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use p, q, r
  simp only [← hc.map_append, List.append_assoc]

lemma editor_of_isSubstring (h : x ++ y = s ++ t) (hu : IsSubstring (x ++ y) (c u)) :
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  obtain ⟨p, q, rfl, rfl⟩ := hc.exists_of_isSubstring_append hu
  obtain ⟨p', q', rfl, rfl⟩ := hc.exists_of_append_eq (h.symm.trans (hc.map_append p q).symm)
  rw [← hc.map_append, ← hc.map_append, hc.injective.eq_iff] at h
  rcases List.append_eq_append_iff.mp h with ⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩ <;>
    use c w <;> simp [← hc.map_append]

lemma eq_empty_of_append_eq_singleton {b : Bool} (h : x ++ y = c [b]) : x = ∅ ∨ y = ∅ := by
  obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq h
  rw [← hc.map_append, hc.injective.eq_iff, List.append_eq_singleton_iff] at h
  rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp [hc.map_nil]

/-- A structure with an initial copy of the binary strings is a model of $\mathsf{WTC}$. -/
lemma models_WTCEmpty : V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := by
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyUnit u =>
    suffices ∀ x, IsSubstring x (ofList u) → x ++ ∅ = x ∧ ∅ ++ x = x by simpa [models_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hc.exists_of_isSubstring (hc.ofList_eq u ▸ hx)
    exact ⟨hc.append_empty v, hc.empty_append v⟩
  case concatAssoc u =>
    suffices ∀ x y z : V, IsSubstring (x ++ y ++ z) (ofList u) ∨
        IsSubstring (x ++ (y ++ z)) (ofList u) → x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
    exact fun x y z h ↦ hc.append_assoc_of_isSubstring (hc.ofList_eq u ▸ h)
  case editor u =>
    suffices ∀ x y s t : V, x ++ y = s ++ t → IsSubstring (x ++ y) (ofList u) →
        ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) by simpa [models_iff]
    exact fun x y s t h hu ↦ hc.editor_of_isSubstring h (hc.ofList_eq u ▸ hu)
  case zeroNeEmpty =>
    simp [models_iff, ← hc.map_nil, ← hc.map_false, hc.injective.eq_iff]
  case zeroAtom =>
    suffices ∀ x y : V, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ hc.eq_empty_of_append_eq_singleton (h.trans hc.map_false.symm)
  case oneNeEmpty =>
    simp [models_iff, ← hc.map_nil, ← hc.map_true, hc.injective.eq_iff]
  case oneAtom =>
    suffices ∀ x y : V, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ hc.eq_empty_of_append_eq_singleton (h.trans hc.map_true.symm)
  case zeroNeOne =>
    simp [models_iff, ← hc.map_false, ← hc.map_true, hc.injective.eq_iff]

end IsInitialEmptyEmbedding

namespace WTCEmptyMinusUnit

lemma exists_ofList_append_isAtom (hc : IsAtom c) (hs : IsAtom s) :
    ∃ u : List Bool, c ++ s = ofList u := by
  rcases hc with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨[false, false], rfl⟩
  · exact ⟨[false, true], rfl⟩
  · exact ⟨[true, false], rfl⟩
  · exact ⟨[true, true], rfl⟩

private lemma exists_ofList_isAtom (hc : IsAtom c) : ∃ u : List Bool, c = ofList u := by
  rcases hc with rfl | rfl
  · exact ⟨[false], rfl⟩
  · exact ⟨[true], rfl⟩

variable [V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻]

lemma append_assoc (u : List Bool) (h : x ++ y ++ z = ofList u ∨ x ++ (y ++ z) = ofList u) :
    x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models V _ (IsWTCEmptyMinusUnitAxiom.concatAssoc u)
  apply this
  rcases h with h | h <;> simp [h]

lemma editor (u : List Bool) (h : x ++ y = ofList u) (h' : s ++ t = ofList u) :
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  have := by simpa [models_iff] using Theory.models V _ (IsWTCEmptyMinusUnitAxiom.editor u)
  exact this x y s t (h.trans h'.symm) (by simp [h])

lemma isAtom_ne_empty (hc : IsAtom c) : c ≠ ∅ := by
  rcases hc with rfl | rfl
  · simpa [models_iff] using Theory.models V _ IsWTCEmptyMinusUnitAxiom.zeroNeEmpty
  · simpa [models_iff] using Theory.models V _ IsWTCEmptyMinusUnitAxiom.oneNeEmpty

lemma eq_empty_of_append_isAtom (hc : IsAtom (x ++ y)) : x = ∅ ∨ y = ∅ := by
  rcases hc with h | h
  · have := by simpa [models_iff] using Theory.models V _ IsWTCEmptyMinusUnitAxiom.zeroAtom
    exact this x y h
  · have := by simpa [models_iff] using Theory.models V _ IsWTCEmptyMinusUnitAxiom.oneAtom
    exact this x y h

protected lemma zero_ne_one : (0 : V) ≠ 1 := by
  simpa [models_iff] using Theory.models V _ IsWTCEmptyMinusUnitAxiom.zeroNeOne

lemma eq_empty_of_append_eq_left (hc : IsAtom c) (h : c ++ x = c) : x = ∅ :=
  (eq_empty_of_append_isAtom (h.symm ▸ hc)).resolve_left (isAtom_ne_empty hc)

lemma eq_empty_of_append_eq_right (hc : IsAtom c) (h : x ++ c = c) : x = ∅ :=
  (eq_empty_of_append_isAtom (h.symm ▸ hc)).resolve_right (isAtom_ne_empty hc)

lemma empty_append_of_append_eq_ofList (hc : IsAtom c) (h : c ++ x = ofList u) : ∅ ++ x = x := by
  obtain ⟨w, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := editor u h h
  · rw [eq_empty_of_append_eq_left hc h₁] at h₂
    exact h₂.symm
  · rwa [eq_empty_of_append_eq_left hc h₁.symm] at h₂

lemma append_empty_of_append_eq_ofList (hc : IsAtom c) (h : x ++ c = ofList u) : x ++ ∅ = x := by
  obtain ⟨w, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := editor u h h
  · rwa [eq_empty_of_append_eq_right hc h₂.symm] at h₁
  · rw [eq_empty_of_append_eq_right hc h₂] at h₁
    exact h₁.symm

lemma empty_append_isAtom (hc : IsAtom c) : ∅ ++ c = c := by
  obtain ⟨u, hu⟩ := exists_ofList_append_isAtom hc hc
  exact empty_append_of_append_eq_ofList hc hu

lemma isAtom_append_empty (hc : IsAtom c) : c ++ ∅ = c := by
  obtain ⟨u, hu⟩ := exists_ofList_append_isAtom hc hc
  exact append_empty_of_append_eq_ofList hc hu

private lemma eq_of_empty_append_isAtom (hc : IsAtom c) (h : ∅ ++ x = c) : x = c := by
  obtain ⟨u, hu⟩ := exists_ofList_append_isAtom hc hc
  have h₁ : c ++ ∅ ++ x = c ++ (∅ ++ x) := append_assoc u <| Or.inr <| by rw [h, hu]
  rw [isAtom_append_empty hc, h] at h₁
  rw [← h, empty_append_of_append_eq_ofList hc (h₁.trans hu)]

lemma eq_of_append_empty_isAtom (hc : IsAtom c) (h : x ++ ∅ = c) : x = c := by
  obtain ⟨u, hu⟩ := exists_ofList_append_isAtom hc hc
  have h₁ : x ++ ∅ ++ c = x ++ (∅ ++ c) := append_assoc u <| Or.inl <| by rw [h, hu]
  rw [empty_append_isAtom hc, h] at h₁
  rw [← h, append_empty_of_append_eq_ofList hc (h₁.symm.trans hu)]

lemma eq_empty_and_eq_or_of_append_eq_isAtom (hc : IsAtom c) (h : x ++ y = c) :
    (x = ∅ ∧ y = c) ∨ (x = c ∧ y = ∅) := by
  rcases eq_empty_of_append_isAtom (h.symm ▸ hc) with rfl | rfl
  · exact Or.inl ⟨rfl, eq_of_empty_append_isAtom hc h⟩
  · exact Or.inr ⟨eq_of_append_empty_isAtom hc h, rfl⟩

lemma eq_empty_of_append_eq_empty (h : x ++ y = ∅) : x = ∅ ∧ y = ∅ := by
  have hx : x = ∅ := by
    by_contra hx
    have key {c : V} (hc : IsAtom c) : x = c := by
      obtain ⟨u, hu⟩ := exists_ofList_isAtom hc
      have e : x ++ y ++ c = x ++ (y ++ c) := append_assoc u <| Or.inl <| by
        rw [h, empty_append_isAtom hc, hu]
      rw [h, empty_append_isAtom hc] at e
      have hy := (eq_empty_of_append_isAtom (e ▸ hc)).resolve_left hx
      exact eq_of_append_empty_isAtom hc <| by rw [e.trans (congrArg _ hy)]
    exact WTCEmptyMinusUnit.zero_ne_one <| (key isAtom_zero).symm.trans (key isAtom_one)
  subst hx
  refine ⟨rfl, ?_⟩
  have e : (0 : V) ++ ∅ ++ y = 0 ++ (∅ ++ y) := append_assoc [false] <| Or.inr <| by
    rw [h, isAtom_append_empty isAtom_zero, ofList_false]
  rw [h, isAtom_append_empty isAtom_zero] at e
  exact eq_empty_of_append_eq_left isAtom_zero e

@[simp]
lemma ofList_append_singleton (u : List Bool) (b : Bool) :
    (ofList (u ++ [b]) : V) = ofList u ++ ofList [b] := by
  rcases eq_or_ne u [] with rfl | hu
  · exact (empty_append_isAtom <| isAtom_ofList_singleton b).symm
  · exact Concatenation.ofList_append_singleton hu b

lemma empty_append_empty : (∅ : V) ++ ∅ = ∅ := by
  have e : (0 : V) ++ ∅ ++ ∅ = 0 ++ (∅ ++ ∅) := append_assoc [false] <| Or.inl <| by
    simp [isAtom_append_empty]
  simp only [isAtom_append_empty isAtom_zero] at e
  exact eq_empty_of_append_eq_left isAtom_zero e.symm

@[simp]
lemma ofList_append_empty (u : List Bool) : (ofList u : V) ++ ∅ = ofList u := by
  induction u using List.reverseRecOn with
  | nil => exact empty_append_empty
  | append_singleton u b _ =>
    have hb := isAtom_append_empty (V := V) <| isAtom_ofList_singleton b
    rw [ofList_append_singleton, append_assoc (u ++ [b]), hb]
    right
    rw [hb, ofList_append_singleton]

@[simp]
lemma empty_append_ofList (u : List Bool) : ∅ ++ (ofList u : V) = ofList u := by
  induction u using List.reverseRecOn with
  | nil => exact empty_append_empty
  | append_singleton u b ih =>
    rw [ofList_append_singleton, ← append_assoc (u ++ [b]), ih]
    left
    rw [ih, ofList_append_singleton]

@[simp]
lemma ofList_append (u v : List Bool) : (ofList (u ++ v) : V) = ofList u ++ ofList v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    rw [← List.append_assoc, ofList_append_singleton, ih, ofList_append_singleton,
      append_assoc (u ++ v ++ [b])]
    left
    rw [ofList_append_singleton, ih]

lemma ofList_injective : Function.Injective (ofList : List Bool → V) := by
  have hne (u : List Bool) (b : Bool) : (ofList (u ++ [b]) : V) ≠ ofList [] := fun h ↦
    isAtom_ne_empty (isAtom_ofList_singleton b) <|
      (eq_empty_of_append_eq_empty <| (ofList_append_singleton u b).symm.trans h).2
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro v h
    rcases v.eq_nil_or_concat with rfl | ⟨v, b, rfl⟩
    · rfl
    · exact absurd h.symm (by simpa using hne v b)
  | append_singleton u b ih =>
    intro v h
    rcases v.eq_nil_or_concat with rfl | ⟨v, d, rfl⟩
    · exact absurd h (hne u b)
    · have hd := isAtom_ofList_singleton (V := V) d
      have hb := isAtom_ofList_singleton (V := V) b
      have hbd : (ofList [b] : V) = ofList [d] → b = d := by
        cases b <;> cases d <;>
          simp [WTCEmptyMinusUnit.zero_ne_one, WTCEmptyMinusUnit.zero_ne_one.symm]
      rw [ofList_append_singleton] at h
      simp only [List.concat_eq_append, ofList_append_singleton] at h
      rcases editor (v ++ [d]) (h.trans (ofList_append_singleton v d).symm)
        (ofList_append_singleton v d).symm with ⟨w, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · rcases eq_empty_and_eq_or_of_append_eq_isAtom hb h₂.symm with ⟨rfl, h⟩ | ⟨-, h⟩
        · simp [ih (by simpa using h₁), hbd h.symm]
        · exact absurd h (isAtom_ne_empty hd)
      · rcases eq_empty_and_eq_or_of_append_eq_isAtom hd h₂ with ⟨rfl, h⟩ | ⟨-, h⟩
        · simp [ih (by simpa using h₁), hbd h]
        · exact absurd h (isAtom_ne_empty hb)

lemma exists_of_append_eq_ofList (h : x ++ y = ofList u) :
    ∃ a b, x = ofList a ∧ y = ofList b := by
  induction u using List.reverseRecOn generalizing x y with
  | nil =>
    use [], []
    exact eq_empty_of_append_eq_empty h
  | append_singleton u b ih =>
    rcases editor (u ++ [b]) h (ofList_append_singleton u b).symm with
      ⟨w, ⟨h₁, rfl⟩ | ⟨rfl, h₂⟩⟩
    · obtain ⟨p, q, rfl, rfl⟩ := ih h₁
      use p, q ++ [b]
      simp
    · rcases eq_empty_and_eq_or_of_append_eq_isAtom (isAtom_ofList_singleton b) h₂ with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · use u, [b]
        simp
      · use u ++ [b], []
        simp

variable (V) in
/--
The values of the binary strings in a model of $\mathsf{WTC}$ with the empty string, without the
neutrality of the empty string, form an initial copy of the standard model.
- [Hor12, §3, Lemma 3.11]
-/
lemma isInitialEmptyEmbedding_ofList : IsInitialEmptyEmbedding (ofList : List Bool → V) where
  injective := ofList_injective
  map_nil := rfl
  map_false := rfl
  map_true := rfl
  map_append := ofList_append
  exists_of_append_eq := exists_of_append_eq_ofList

end WTCEmptyMinusUnit

/--
Every model of $\mathsf{WTC}$ with the empty string, without the neutrality of the empty string, is
a model of $\mathsf{WTC}$ with the empty string.
-/
lemma WTCEmptyMinusUnit.models_WTCEmpty [V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻] : V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ :=
  (WTCEmptyMinusUnit.isInitialEmptyEmbedding_ofList V).models_WTCEmpty

end models

/--
$\mathsf{WTC}$ with the empty string is weaker than its variant without the neutrality of the empty
string.
-/
instance : 𝗪𝗧𝗖ₑ ⪯ 𝗪𝗧𝗖ₑ⁻ :=
  weakerThan_of_models_empty.{0} _ _ fun _ _ _ ↦ WTCEmptyMinusUnit.models_WTCEmpty

/--
The neutrality of the empty string is redundant in $\mathsf{WTC}$ with the empty string.
- [HH14, Question 2]
-/
theorem WTCEmptyMinusUnit.equiv_WTCEmpty : 𝗪𝗧𝗖ₑ⁻ ≊ 𝗪𝗧𝗖ₑ :=
  Entailment.Equiv.antisymm_iff.mpr ⟨inferInstance, inferInstance⟩

section standard

instance : (List Bool)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ :=
  IsInitialEmptyEmbedding.models_WTCEmpty (c := id)
    { injective := Function.injective_id
      map_nil := rfl
      map_false := rfl
      map_true := rfl
      map_append := fun _ _ ↦ rfl
      exists_of_append_eq := fun {x y} _ _ ↦ ⟨x, y, rfl, rfl⟩ }

instance : Entailment.Consistent 𝗪𝗧𝗖ₑ :=
  let : (List Bool)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

end standard

namespace WTCEmpty

open WTCEmptyMinusUnit

variable {V : Type} [ConcatenationEmptyStructure V] {x : V}

instance : NonemptyClosed 𝗪𝗧𝗖ₑ where
  zero_ne_empty _ := isAtom_ne_empty isAtom_zero
  one_ne_empty _ := isAtom_ne_empty isAtom_one
  append_ne_empty _ _ _ _ _ hx h := hx (eq_empty_of_append_eq_empty h).1

namespace nonemptyTranslation

variable [V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ]

section

attribute [local instance] Concatenation.nonemptyTranslation.concatenationStructure

lemma val_ofFreeSemigroup (u : FreeSemigroup Bool) :
    ((ofFreeSemigroup u : (nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V) : V) = ofFreeSemigroup u :=
  (map_stringValue Model.val (fun _ _ ↦ rfl) _ u).trans <| by
    congr
    funext b
    cases b <;> rfl

lemma isSubstring_ofList_of_isSubstring {x : (nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V}
    {u : FreeSemigroup Bool} (h : IsSubstring x (ofFreeSemigroup u)) :
    IsSubstring (x : V) (ofList u.toList) := by
  suffices IsSubstring (x : V) ((ofFreeSemigroup u : (nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V) : V) by
    rwa [val_ofFreeSemigroup] at this
  rcases h with rfl | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, h⟩ | ⟨a, b, h⟩
  exacts [.inl rfl, .inr <| .inl ⟨a, congrArg Model.val h⟩,
    .inr <| .inr <| .inl ⟨b, congrArg Model.val h⟩,
    .inr <| .inr <| .inr <| .inl ⟨a, b, congrArg Model.val h⟩,
    .inr <| .inr <| .inr <| .inr ⟨a, b, congrArg Model.val h⟩]

end

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{WTC}$ with the empty string form a model of
$\mathsf{WTC}$.
- [HH14, Theorem 3]
-/
instance [V↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ] : ((nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure V 𝗪𝗧𝗖ₑ
  have hc := isInitialEmptyEmbedding_ofList V
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case concatAssoc u =>
    suffices ∀ x y z : (nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V,
        IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
          IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u) → x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    exact fun x y z h ↦ Model.ext <| hc.append_assoc_of_isSubstring <|
      h.imp nonemptyTranslation.isSubstring_ofList_of_isSubstring
        nonemptyTranslation.isSubstring_ofList_of_isSubstring
  case editor u =>
    suffices ∀ x y s t : (nonemptyTranslation 𝗪𝗧𝗖ₑ).Model V, x ++ y = s ++ t →
        IsSubstring (x ++ y) (ofFreeSemigroup u) → (x = s ∧ y = t) ∨
          ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) by
      simpa [models_iff]
    intro x y s t h hu
    have h : (x : V) ++ (y : V) = (s : V) ++ (t : V) := congrArg Model.val h
    have hu : IsSubstring ((x : V) ++ (y : V)) (ofList u.toList) :=
      nonemptyTranslation.isSubstring_ofList_of_isSubstring hu
    obtain ⟨p, q, hx, hy⟩ := hc.exists_of_isSubstring_append hu
    obtain ⟨r, o, hs, ht⟩ := hc.exists_of_isSubstring_append (h ▸ hu)
    obtain ⟨w, hw⟩ := hc.editor_of_isSubstring h hu
    rcases Classical.em (w = ∅) with rfl | hw'
    · left
      simp only [hx, hy, hs, ht, hc.append_empty, hc.empty_append] at hw
      simp only [Model.ext_iff, hx, hy, hs, ht]
      tauto
    · right
      use ⟨w, by simpa using hw'⟩
      exact hw.imp (And.imp Model.ext Model.ext) (And.imp Model.ext Model.ext)
  case concatNeZero =>
    simpa [models_iff, Model.forall_iff] using fun (x : V) (hx : x ≠ ∅) (y : V) (hy : y ≠ ∅)
      (h : x ++ y = 0) ↦ (eq_empty_of_append_isAtom <| by simp [h]).elim hx hy
  case concatNeOne =>
    simpa [models_iff, Model.forall_iff] using fun (x : V) (hx : x ≠ ∅) (y : V) (hy : y ≠ ∅)
      (h : x ++ y = 1) ↦ (eq_empty_of_append_isAtom <| by simp [h]).elim hx hy
  case zeroNeOne => simp [models_iff, WTCEmptyMinusUnit.zero_ne_one]

end WTCEmpty

/--
$\mathsf{WTC}$ with the empty string interprets $\mathsf{WTC}$ on the nonempty strings.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖ₑ ⊳ 𝗪𝗧𝗖 where
  trln := nonemptyTranslation 𝗪𝗧𝗖ₑ
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

namespace WTC

variable {V : Type} [ConcatenationStructure V] {w x y z : V}

/-- `w` is the only string that yields `y` after the letter $1$. -/
def IsDecode (w y : V) : Prop := y = 1 ++ w ∧ ∀ v, y = 1 ++ v → v = w

/-- `w` is the only string that yields `y` after the letter $1$. -/
def isDecode : Semisentence ℒ⌢ 2 :=
  “w y. y = !!(op(1).const) ⌢ w ∧ ∀ v, y = !!(op(1).const) ⌢ v → v = w”

instance isDecode_defined : ℒ⌢-relation[V] IsDecode via isDecode :=
  ⟨fun v ↦ by simp [isDecode, IsDecode]⟩

instance isDecode_definable : ℒ⌢-relation[V] IsDecode := isDecode_defined.to_definable

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def IsCodeAppend (z x y : V) : Prop :=
  (y = 1 ∧ z = x) ∨ (∃ w, IsDecode w y ∧ z = x ++ w) ∨ (y ≠ 1 ∧ (∀ w, ¬IsDecode w y) ∧ z = 0)

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(1).const) ∧ z = x) ∨ (∃ w, !isDecode w y ∧ z = x ⌢ w) ∨
    (y ≠ !!(op(1).const) ∧ (∀ w, ¬!isDecode w y) ∧ z = !!(op(0).const))”

instance isCodeAppend_defined : ℒ⌢-relation₃[V] IsCodeAppend via isCodeAppend :=
  ⟨fun v ↦ by simp [isCodeAppend, IsCodeAppend]⟩

instance isCodeAppend_definable : ℒ⌢-relation₃[V] IsCodeAppend := isCodeAppend_defined.to_definable

/-- The code of a possibly empty binary string: the string after the letter $1$. -/
def emptyCode (u : List Bool) : V := ofFreeSemigroup ⟨true, u⟩

@[simp]
lemma emptyCode_nil : (emptyCode [] : V) = 1 := rfl

section model

variable [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

private lemma not_isDecode_one : ¬IsDecode w (1 : V) := fun h ↦ append_ne_one _ _ h.1.symm

lemma existsUnique_isCodeAppend (x y : V) : ∃! z, IsCodeAppend z x y := by
  by_cases h₁ : y = 1
  · use x
    simp [IsCodeAppend, h₁, not_isDecode_one]
  by_cases h₂ : ∃ w, IsDecode w y
  · obtain ⟨w, hw⟩ := h₂
    have hw' (v : V) : IsDecode v y ↔ v = w :=
      ⟨fun h ↦ hw.2 v h.1, fun h ↦ h ▸ hw⟩
    use x ++ w
    simp [IsCodeAppend, h₁, hw']
  · use 0
    simp_all [IsCodeAppend]

/-- The code of the concatenation of the strings coded by `x` and `y`. -/
noncomputable def codeAppend (x y : V) : V := (existsUnique_isCodeAppend x y).choose

lemma isCodeAppend_codeAppend (x y : V) : IsCodeAppend (codeAppend x y) x y :=
  (existsUnique_isCodeAppend x y).choose_spec.1

lemma eq_codeAppend_of_isCodeAppend (h : IsCodeAppend z x y) : z = codeAppend x y :=
  (existsUnique_isCodeAppend x y).unique h (isCodeAppend_codeAppend x y)

lemma emptyCode_cons (b : Bool) (l : List Bool) :
    (emptyCode (b :: l) : V) = 1 ++ ofFreeSemigroup ⟨b, l⟩ :=
  ofFreeSemigroup_mul 1 ⟨b, l⟩

private lemma isDecode_emptyCode (b : Bool) (l : List Bool) :
    IsDecode (ofFreeSemigroup ⟨b, l⟩ : V) (emptyCode (b :: l)) := by
  refine ⟨emptyCode_cons b l, ?_⟩
  intro v h
  obtain ⟨p, q, hp, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
  obtain rfl : 1 = p := ofFreeSemigroup_injective hp
  have e := congrArg FreeSemigroup.toList e
  congr 1
  apply FreeSemigroup.toList_injective
  simpa [FreeSemigroup.toList, one_eq_of_true, FreeSemigroup.of] using e.symm

private lemma isCodeAppend_emptyCode (u v : List Bool) :
    IsCodeAppend (emptyCode (u ++ v) : V) (emptyCode u) (emptyCode v) := by
  rcases v with _ | ⟨b, l⟩
  · left
    simp
  · right; left
    use ofFreeSemigroup ⟨b, l⟩, isDecode_emptyCode b l, ofFreeSemigroup_mul ⟨true, u⟩ ⟨b, l⟩

private lemma exists_of_isCodeAppend_emptyCode {u : List Bool}
    (h : IsCodeAppend (emptyCode u) x y) :
    ∃ p q, x = emptyCode p ∧ y = emptyCode q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, -⟩, h⟩ | ⟨-, -, h⟩
  · use u, []
    simp
  · obtain ⟨⟨a, p⟩, ⟨b, q⟩, rfl, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
    obtain rfl : true = a := congrArg FreeSemigroup.head e
    use p, b :: q, rfl, (emptyCode_cons b q).symm
  · have e : (⟨true, u⟩ : FreeSemigroup Bool) = 0 := ofFreeSemigroup_injective (V := V) h
    exact absurd (congrArg FreeSemigroup.head e) (by simp [zero_eq_of_false, FreeSemigroup.of])

end model

/--
The translation of $\mathsf{WTC}$ with the empty string into $\mathsf{WTC}$ that codes a string by
the string itself after the letter $1$, and the empty string by the letter $1$.
- [HH14, Theorem 3]
-/
def emptyTranslation : DirectTranslation 𝗪𝗧𝗖 ℒ⌢ₑ where
  domain := ⟨“x. ⊤”⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isCodeAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(1).const)”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_isCodeAppend (e 0) (e 1)
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

lemma dom (x : V) : emptyTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

/-- The letters, the concatenation and the empty string coded in a model of $\mathsf{WTC}$. -/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure (emptyTranslation.Model V) where
  zero := ⟨1 ++ 0, dom _⟩
  one := ⟨1 ++ 1, dom _⟩
  append x y := ⟨codeAppend (x : V) y, dom _⟩
  emptyCollection := ⟨1, dom _⟩

/--
The structure of the model of `emptyTranslation` is the standard one of
`concatenationEmptyStructure`.
-/
lemma struc_eq :
    Model.struc emptyTranslation V = @standardModelEmpty _ concatenationEmptyStructure := by
  apply Tarski.Structure.ext
  · funext k f v
    symm
    apply Model.func_iff.mpr
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
    · rw [Matrix.fun_eq_vec_two fun i ↦ (v i : V)]
      exact (Defined.eval_iff (φ := isCodeAppend) _).mpr (isCodeAppend_codeAppend (v 0 : V) (v 1))
    · simp [emptyTranslation, Semiformula.Operator.val]
      rfl
  · funext k r v
    rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    exact propext <| Model.eq_iff v

end emptyTranslation

/--
The strings of a model of $\mathsf{WTC}$ code a model of $\mathsf{WTC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] : (emptyTranslation.Model V)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := by
  rw [emptyTranslation.struc_eq]
  let := emptyTranslation.concatenationEmptyStructure (V := V)
  have isCodeAppend (x y : emptyTranslation.Model V) : IsCodeAppend ((x ++ y : _) : V) x y :=
    isCodeAppend_codeAppend (x : V) y
  let c (u : List Bool) : emptyTranslation.Model V := ⟨emptyCode u, emptyTranslation.dom _⟩
  apply IsInitialEmptyEmbedding.models_WTCEmpty (c := c)
  constructor
  case injective =>
    intro u v h
    exact congrArg FreeSemigroup.tail <| ofFreeSemigroup_injective (congrArg Model.val h)
  case map_nil => rfl
  case map_false => rfl
  case map_true => rfl
  case map_append =>
    exact fun u v ↦ Model.ext <| eq_codeAppend_of_isCodeAppend (isCodeAppend_emptyCode u v)
  case exists_of_append_eq =>
    intro x y u h
    obtain ⟨p, q, hp, hq⟩ : ∃ p q, (x : V) = emptyCode p ∧ (y : V) = emptyCode q :=
      exists_of_isCodeAppend_emptyCode <| (congrArg Model.val h) ▸ isCodeAppend x y
    use p, q, Model.ext hp, Model.ext hq

end WTC

/--
$\mathsf{WTC}$ interprets $\mathsf{WTC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖 ⊳ 𝗪𝗧𝗖ₑ where
  trln := WTC.emptyTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{WTC}$ and $\mathsf{WTC}$ with the empty string are mutually interpretable.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖 ⋈ 𝗪𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{WTC}$ with the empty string interprets $\mathsf{R}_0$.
- [HH14, Theorem 1]
- [Hor12, §4, Theorem 4.1]
-/
instance : 𝗪𝗧𝗖ₑ ⊳ 𝗥₀ :=
  DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀) (inferInstance : 𝗪𝗧𝗖ₑ ⊳ 𝗪𝗧𝗖)

/--
$\mathsf{WTC}$ with the empty string is essentially undecidable.
- [HH14, Theorem 1, Theorem 11]
- [Hor12, §4, Corollary 4.11]
-/
instance : 𝗪𝗧𝗖ₑ.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖ₑ ⊳ 𝗥₀)

/--
$\mathsf{WTC}$ with the empty string is undecidable.
- [HH14, Theorem 1]
-/
theorem WTCEmpty.undecidable : Entailment.Undecidable 𝗪𝗧𝗖ₑ :=
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖ₑ

end FFL.FirstOrder.Concatenation

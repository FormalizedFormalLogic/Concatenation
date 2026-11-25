module

public import Concatenation.Semantics.Empty
public import Concatenation.WTC.Basic

/-!
# $\mathsf{WTC}$ with the empty string and without its neutrality

The axioms on the neutrality of the empty string follow from the other axioms of $\mathsf{WTC}$
with the empty string.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open ConcatenationStructure ConcatenationEmptyStructure

/--
Axioms of the weak theory of concatenation with the empty string, without the neutrality of the
empty string.
- [HH14, §3.2]
-/
inductive IsWTCEmptyMinusUnitAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsWTCEmptyMinusUnitAxiom φ
  | concatAssoc (u : List Bool) : IsWTCEmptyMinusUnitAxiom
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteralEmpty u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteralEmpty u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : List Bool) : IsWTCEmptyMinusUnitAxiom
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteralEmpty u) →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | zeroNeEmpty : IsWTCEmptyMinusUnitAxiom “!!(op(0).const) ≠ ⋆”
  | zeroAtom : IsWTCEmptyMinusUnitAxiom “∀ x y, x ⌢ y = !!(op(0).const) → x = ⋆ ∨ y = ⋆”
  | oneNeEmpty : IsWTCEmptyMinusUnitAxiom “!!(op(1).const) ≠ ⋆”
  | oneAtom : IsWTCEmptyMinusUnitAxiom “∀ x y, x ⌢ y = !!(op(1).const) → x = ⋆ ∨ y = ⋆”
  | zeroNeOne : IsWTCEmptyMinusUnitAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The weak theory of concatenation with the empty string, without the neutrality of the empty string.
- [HH14, §3.2]
-/
abbrev WTCEmptyMinusUnit : Theory ℒ⌢ₑ := Set.ofPred IsWTCEmptyMinusUnitAxiom

@[inherit_doc]
notation "𝗪𝗧𝗖ₑ⁻" => WTCEmptyMinusUnit

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗪𝗧𝗖ₑ⁻ :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCEmptyMinusUnitAxiom.equal φ hφ

lemma IsWTCEmptyMinusUnitAxiom.isWTCEmptyAxiom {σ : Sentence ℒ⌢ₑ}
    (h : IsWTCEmptyMinusUnitAxiom σ) : IsWTCEmptyAxiom σ := by
  cases h
  case equal hφ => exact .equal _ hφ
  case concatAssoc u => exact .concatAssoc u
  case editor u => exact .editor u
  case zeroNeEmpty => exact .zeroNeEmpty
  case zeroAtom => exact .zeroAtom
  case oneNeEmpty => exact .oneNeEmpty
  case oneAtom => exact .oneAtom
  case zeroNeOne => exact .zeroNeOne

instance : 𝗪𝗧𝗖ₑ⁻ ⪯ 𝗪𝗧𝗖ₑ :=
  Entailment.WeakerThan.ofSubset fun _ ↦ IsWTCEmptyMinusUnitAxiom.isWTCEmptyAxiom

section models

variable {M : Type*} [ConcatenationEmptyStructure M] {c x y z s t : M} {u v : List Bool}

instance [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ] : M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻ :=
  ⟨fun _ h ↦ Theory.models M 𝗪𝗧𝗖ₑ h.isWTCEmptyAxiom⟩

@[simp]
lemma ofList_nil : (ofList [] : M) = ∅ := rfl

@[simp]
lemma ofList_false : (ofList [false] : M) = 0 := rfl

@[simp]
lemma ofList_true : (ofList [true] : M) = 1 := rfl

lemma ofList_append_singleton (hu : u ≠ []) (b : Bool) :
    (ofList (u ++ [b]) : M) = ofList u ++ ofList [b] := by
  rcases u with _ | ⟨d, l⟩
  · exact absurd rfl hu
  · simp [ofList, ofFreeSemigroup]

lemma isAtom_ofList_singleton (b : Bool) : IsAtom (ofList [b] : M) := by
  cases b <;> simp

/--
`c` embeds the binary strings onto an initial part of `M`: if a concatenation is a standard string,
then so are its arguments.
-/
structure IsInitialEmptyEmbedding (c : List Bool → M) : Prop where
  injective : Function.Injective c
  map_nil : c [] = ∅
  map_false : c [false] = 0
  map_true : c [true] = 1
  map_append (u v : List Bool) : c (u ++ v) = c u ++ c v
  exists_of_append_eq {x y : M} {w : List Bool} (h : x ++ y = c w) : ∃ u v, x = c u ∧ y = c v

namespace IsInitialEmptyEmbedding

variable {c : List Bool → M} (hc : IsInitialEmptyEmbedding c)

include hc

lemma ofList_eq (u : List Bool) : ofList u = c u := by
  have hb (b : Bool) : ofList [b] = c [b] := by
    cases b
    · exact hc.map_false.symm
    · exact hc.map_true.symm
  induction u using List.reverseRecOn with
  | nil => exact hc.map_nil.symm
  | append_singleton u b ih =>
    rcases eq_or_ne u [] with rfl | hu
    · exact hb b
    · rw [ofList_append_singleton hu, ih, hb, ← hc.map_append]

lemma exists_of_isSubstring (h : IsSubstring x (c u)) : ∃ v, x = c v := by
  rcases h with rfl | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · use u
  · obtain ⟨-, b, -, rfl⟩ := hc.exists_of_append_eq h.symm
    use b
  · obtain ⟨a, -, rfl, -⟩ := hc.exists_of_append_eq h.symm
    use a
  · obtain ⟨a, -, ha, -⟩ := hc.exists_of_append_eq h.symm
    obtain ⟨-, b, -, rfl⟩ := hc.exists_of_append_eq ha
    use b
  · obtain ⟨-, b, -, hb⟩ := hc.exists_of_append_eq h.symm
    obtain ⟨a, -, rfl, -⟩ := hc.exists_of_append_eq hb
    use a

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
  rcases List.append_eq_append_iff.mp h with ⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩
  · use c w
    simp [← hc.map_append]
  · use c w
    simp [← hc.map_append]

lemma eq_empty_of_append_eq_singleton {b : Bool} (h : x ++ y = c [b]) : x = ∅ ∨ y = ∅ := by
  obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq h
  rw [← hc.map_append, hc.injective.eq_iff, List.append_eq_singleton_iff] at h
  rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> simp [hc.map_nil]

/-- A structure with an initial copy of the binary strings is a model of $\mathsf{WTC}$. -/
lemma models_WTCEmpty : M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := by
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
    suffices ∀ x y z : M, IsSubstring (x ++ y ++ z) (ofList u) ∨
        IsSubstring (x ++ (y ++ z)) (ofList u) → x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
    exact fun x y z h ↦ hc.append_assoc_of_isSubstring (hc.ofList_eq u ▸ h)
  case editor u =>
    suffices ∀ x y s t : M, x ++ y = s ++ t → IsSubstring (x ++ y) (ofList u) →
        ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) by simpa [models_iff]
    exact fun x y s t h hu ↦ hc.editor_of_isSubstring h (hc.ofList_eq u ▸ hu)
  case zeroNeEmpty =>
    simp [models_iff, ← hc.map_nil, ← hc.map_false, hc.injective.eq_iff]
  case zeroAtom =>
    suffices ∀ x y : M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ hc.eq_empty_of_append_eq_singleton (h.trans hc.map_false.symm)
  case oneNeEmpty =>
    simp [models_iff, ← hc.map_nil, ← hc.map_true, hc.injective.eq_iff]
  case oneAtom =>
    suffices ∀ x y : M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ hc.eq_empty_of_append_eq_singleton (h.trans hc.map_true.symm)
  case zeroNeOne =>
    simp [models_iff, ← hc.map_false, ← hc.map_true, hc.injective.eq_iff]

end IsInitialEmptyEmbedding

namespace WTCEmpty

lemma exists_ofList_append_isAtom (hc : IsAtom c) (hs : IsAtom s) :
    ∃ u : List Bool, c ++ s = ofList u := by
  rcases hc with rfl | rfl <;> rcases hs with rfl | rfl
  · exact ⟨[false, false], rfl⟩
  · exact ⟨[false, true], rfl⟩
  · exact ⟨[true, false], rfl⟩
  · exact ⟨[true, true], rfl⟩

lemma exists_ofList_isAtom (hc : IsAtom c) : ∃ u : List Bool, c = ofList u := by
  rcases hc with rfl | rfl
  · exact ⟨[false], rfl⟩
  · exact ⟨[true], rfl⟩

variable [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻]

lemma append_assoc (u : List Bool) (h : x ++ y ++ z = ofList u ∨ x ++ (y ++ z) = ofList u) :
    x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCEmptyMinusUnitAxiom.concatAssoc u)
  apply this
  rcases h with h | h <;> simp [h]

lemma editor (u : List Bool) (h : x ++ y = ofList u) (h' : s ++ t = ofList u) :
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCEmptyMinusUnitAxiom.editor u)
  exact this x y s t (h.trans h'.symm) (by simp [h])

lemma isAtom_ne_empty (hc : IsAtom c) : c ≠ ∅ := by
  rcases hc with rfl | rfl
  · simpa [models_iff] using Theory.models M _ IsWTCEmptyMinusUnitAxiom.zeroNeEmpty
  · simpa [models_iff] using Theory.models M _ IsWTCEmptyMinusUnitAxiom.oneNeEmpty

lemma eq_empty_of_append_isAtom (hc : IsAtom (x ++ y)) : x = ∅ ∨ y = ∅ := by
  rcases hc with h | h
  · have := by simpa [models_iff] using Theory.models M _ IsWTCEmptyMinusUnitAxiom.zeroAtom
    exact this x y h
  · have := by simpa [models_iff] using Theory.models M _ IsWTCEmptyMinusUnitAxiom.oneAtom
    exact this x y h

protected lemma zero_ne_one : (0 : M) ≠ 1 := by
  simpa [models_iff] using Theory.models M _ IsWTCEmptyMinusUnitAxiom.zeroNeOne

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

lemma eq_of_empty_append_isAtom (hc : IsAtom c) (h : ∅ ++ x = c) : x = c := by
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
    have key {c : M} (hc : IsAtom c) : x = c := by
      obtain ⟨u, hu⟩ := exists_ofList_isAtom hc
      have e : x ++ y ++ c = x ++ (y ++ c) := append_assoc u <| Or.inl <| by
        rw [h, empty_append_isAtom hc, hu]
      rw [h, empty_append_isAtom hc] at e
      have hy := (eq_empty_of_append_isAtom (e ▸ hc)).resolve_left hx
      exact eq_of_append_empty_isAtom hc <| by rw [e.trans (congrArg _ hy)]
    exact WTCEmpty.zero_ne_one <| (key isAtom_zero).symm.trans (key isAtom_one)
  subst hx
  and_intros
  · rfl
  · have e : (0 : M) ++ ∅ ++ y = 0 ++ (∅ ++ y) := append_assoc [false] <| Or.inr <| by
      rw [h, isAtom_append_empty isAtom_zero, ofList_false]
    rw [h, isAtom_append_empty isAtom_zero] at e
    exact eq_empty_of_append_eq_left isAtom_zero e

@[simp]
lemma ofList_append_singleton (u : List Bool) (b : Bool) :
    (ofList (u ++ [b]) : M) = ofList u ++ ofList [b] := by
  rcases eq_or_ne u [] with rfl | hu
  · exact (empty_append_isAtom <| isAtom_ofList_singleton b).symm
  · exact Concatenation.ofList_append_singleton hu b

lemma empty_append_empty : (∅ : M) ++ ∅ = ∅ := by
  have e : (0 : M) ++ ∅ ++ ∅ = 0 ++ (∅ ++ ∅) := append_assoc [false] <| Or.inl <| by
    simp [isAtom_append_empty]
  simp only [isAtom_append_empty isAtom_zero] at e
  exact eq_empty_of_append_eq_left isAtom_zero e.symm

@[simp]
lemma ofList_append_empty (u : List Bool) : (ofList u : M) ++ ∅ = ofList u := by
  induction u using List.reverseRecOn with
  | nil => exact empty_append_empty
  | append_singleton u b _ =>
    have hb := isAtom_append_empty (M := M) <| isAtom_ofList_singleton b
    rw [ofList_append_singleton, append_assoc (u ++ [b]), hb]
    right
    rw [hb, ofList_append_singleton]

@[simp]
lemma empty_append_ofList (u : List Bool) : ∅ ++ (ofList u : M) = ofList u := by
  induction u using List.reverseRecOn with
  | nil => exact empty_append_empty
  | append_singleton u b ih =>
    rw [ofList_append_singleton, ← append_assoc (u ++ [b]), ih]
    left
    rw [ih, ofList_append_singleton]

@[simp]
lemma ofList_append (u v : List Bool) : (ofList (u ++ v) : M) = ofList u ++ ofList v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    rw [← List.append_assoc, ofList_append_singleton, ih, ofList_append_singleton,
      append_assoc (u ++ v ++ [b])]
    left
    rw [ofList_append_singleton, ih]

lemma ofList_injective : Function.Injective (ofList : List Bool → M) := by
  have hne (u : List Bool) (b : Bool) : (ofList (u ++ [b]) : M) ≠ ofList [] := fun h ↦
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
    · have hd := isAtom_ofList_singleton (M := M) d
      have hb := isAtom_ofList_singleton (M := M) b
      have hbd : (ofList [b] : M) = ofList [d] → b = d := by
        cases b <;> cases d <;> simp [WTCEmpty.zero_ne_one, WTCEmpty.zero_ne_one.symm]
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

variable (M) in
/--
The values of the binary strings in a model of $\mathsf{WTC}$ with the empty string, without the
neutrality of the empty string, form an initial copy of the standard model.
- [Hor12, §3, Lemma 3.11]
-/
lemma isInitialEmptyEmbedding_ofList : IsInitialEmptyEmbedding (ofList : List Bool → M) where
  injective := ofList_injective
  map_nil := rfl
  map_false := rfl
  map_true := rfl
  map_append := ofList_append
  exists_of_append_eq := exists_of_append_eq_ofList

lemma isSubstring_ofList_iff : IsSubstring x (ofList u) ↔ ∃ v, x = ofList v ∧ v <:+: u := by
  constructor
  · rintro (rfl | ⟨s, h⟩ | ⟨t, h⟩ | ⟨s, t, h⟩ | ⟨s, t, h⟩)
    · use u
    · obtain ⟨a, b, rfl, rfl⟩ := exists_of_append_eq_ofList h.symm
      rw [← ofList_append, ofList_injective.eq_iff] at h
      use b
      simp [h, List.infix_append_of_infix_right]
    · obtain ⟨a, b, rfl, rfl⟩ := exists_of_append_eq_ofList h.symm
      rw [← ofList_append, ofList_injective.eq_iff] at h
      use a
      simp [h, List.prefix_append, List.IsPrefix.isInfix]
    · obtain ⟨a, b, ha, rfl⟩ := exists_of_append_eq_ofList h.symm
      obtain ⟨p, q, rfl, rfl⟩ := exists_of_append_eq_ofList ha
      rw [← ofList_append, ← ofList_append, ofList_injective.eq_iff] at h
      use q
      simp [h]
    · obtain ⟨a, b, rfl, hb⟩ := exists_of_append_eq_ofList h.symm
      obtain ⟨p, q, rfl, rfl⟩ := exists_of_append_eq_ofList hb
      rw [← ofList_append, ← ofList_append, ofList_injective.eq_iff] at h
      use p
      simp [h]
  · rintro ⟨v, rfl, s, t, rfl⟩
    simp only [ofList_append, isSubstring_append_append]

end WTCEmpty

/--
Every model of $\mathsf{WTC}$ with the empty string, without the neutrality of the empty string, is
a model of $\mathsf{WTC}$ with the empty string.
-/
lemma WTCEmptyMinusUnit.models_WTCEmpty [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ⁻] : M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ :=
  (WTCEmpty.isInitialEmptyEmbedding_ofList M).models_WTCEmpty

end models

/--
$\mathsf{WTC}$ with the empty string is a subtheory of its subtheory without the neutrality of the
empty string.
-/
instance : 𝗪𝗧𝗖ₑ ⪯ 𝗪𝗧𝗖ₑ⁻ :=
  weakerThan_of_models_empty.{0} _ _ fun _ _ _ ↦ WTCEmptyMinusUnit.models_WTCEmpty

/--
The neutrality of the empty string is redundant in $\mathsf{WTC}$ with the empty string.
- [HH14, Question 2]
-/
theorem WTCEmptyMinusUnit.equiv_WTCEmpty : 𝗪𝗧𝗖ₑ⁻ ≊ 𝗪𝗧𝗖ₑ :=
  Entailment.Equiv.antisymm_iff.mpr ⟨inferInstance, inferInstance⟩

end FFL.FirstOrder.Concatenation

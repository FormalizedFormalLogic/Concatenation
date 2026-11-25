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
  · simp [ofList, ofFreeSemigroup, stringValue]

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
  · intro h
    apply h.of_forall_append (P := fun x ↦ ∃ v, x = ofList v ∧ v <:+: u) _
      ⟨u, rfl, List.infix_refl u⟩
    rintro x y ⟨v, h, hv⟩
    obtain ⟨a, b, rfl, rfl⟩ := exists_of_append_eq_ofList h
    rw [← ofList_append, ofList_injective.eq_iff] at h
    subst h
    exact ⟨⟨a, rfl, (List.prefix_append a b).isInfix.trans hv⟩,
      ⟨b, rfl, (List.suffix_append a b).isInfix.trans hv⟩⟩
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

section standard

/--
The binary strings under concatenation.
- [HH14, §2]
-/
instance : ConcatenationEmptyStructure (List Bool) where
  zero := [false]
  one := [true]

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

variable {M : Type} [ConcatenationEmptyStructure M] {x : M}

/--
The translation of $\mathsf{WTC}$ into $\mathsf{WTC}$ with the empty string, relativized to the
nonempty strings.
- [HH14, Theorem 3]
-/
def nonemptyTranslation : DirectTranslation 𝗪𝗧𝗖ₑ ℒ⌢ where
  domain := ⟨isNonempty⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. z = !!(op(0).const)”⟩
    | Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const)”⟩
    | Language.Concatenation.Func.concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val, isAtom_ne_empty]
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : e i ≠ ∅ := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 0 by simpa [Semiformula.Operator.val]
      use 0
      simp [isAtom_ne_empty]
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 1 by simpa [Semiformula.Operator.val]
      use 1
      simp [isAtom_ne_empty]
    · suffices ∃! y : M, y ≠ ∅ ∧ y = e 0 ++ e 1 by simpa [Semiformula.Operator.val]
      use e 0 ++ e 1
      simpa using fun h ↦ he 0 (eq_empty_of_append_eq_empty h).1
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace nonemptyTranslation

@[simp]
lemma dom_iff : nonemptyTranslation.Dom x ↔ x ≠ ∅ := by
  simp [DirectTranslation.dom_iff, nonemptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ]

/-- The letters and the concatenation of `M` restricted to the nonempty strings. -/
abbrev concatenationStructure : ConcatenationStructure (nonemptyTranslation.Model M) where
  zero := ⟨0, by simp [isAtom_ne_empty]⟩
  one := ⟨1, by simp [isAtom_ne_empty]⟩
  append x y := ⟨x ++ y, dom_iff.mpr fun h ↦ dom_iff.mp x.dom (eq_empty_of_append_eq_empty h).1⟩

/--
The structure of the model of `nonemptyTranslation` is the standard one of the letters and the
concatenation restricted to the nonempty strings.
-/
lemma struc_eq :
    Model.struc nonemptyTranslation M = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [nonemptyTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationStructure

lemma val_ofFreeSemigroup (u : FreeSemigroup Bool) :
    ((ofFreeSemigroup u : nonemptyTranslation.Model M) : M) = ofFreeSemigroup u :=
  (map_stringValue Model.val (fun _ _ ↦ rfl) _ u).trans <| by
    congr
    funext b
    cases b <;> rfl

lemma isSubstring_val {x y : nonemptyTranslation.Model M} (h : IsSubstring x y) :
    IsSubstring (x : M) y := h.map Model.val fun _ _ ↦ rfl

lemma isSubstring_ofList_of_isSubstring {x : nonemptyTranslation.Model M} {u : FreeSemigroup Bool}
    (h : IsSubstring x (ofFreeSemigroup u)) : IsSubstring (x : M) (ofList u.toList) := by
  have h := isSubstring_val h
  rwa [val_ofFreeSemigroup] at h

end

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{WTC}$ with the empty string form a model of
$\mathsf{WTC}$.
- [HH14, Theorem 3]
-/
instance [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ] : (nonemptyTranslation.Model M)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure (M := M)
  have nonempty (x : nonemptyTranslation.Model M) : (x : M) ≠ ∅ :=
    nonemptyTranslation.dom_iff.mp x.dom
  have hc := isInitialEmptyEmbedding_ofList M
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case concatAssoc u =>
    suffices ∀ x y z : nonemptyTranslation.Model M,
        IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
          IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u) → x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    exact fun x y z h ↦ Model.ext <| hc.append_assoc_of_isSubstring <|
      h.imp nonemptyTranslation.isSubstring_ofList_of_isSubstring
        nonemptyTranslation.isSubstring_ofList_of_isSubstring
  case editor u =>
    suffices ∀ x y s t : nonemptyTranslation.Model M, x ++ y = s ++ t →
        IsSubstring (x ++ y) (ofFreeSemigroup u) → (x = s ∧ y = t) ∨
          ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) by
      simpa [models_iff]
    intro x y s t h hu
    have h : (x : M) ++ (y : M) = (s : M) ++ (t : M) := congrArg Model.val h
    have hu : IsSubstring ((x : M) ++ (y : M)) (ofList u.toList) :=
      nonemptyTranslation.isSubstring_ofList_of_isSubstring hu
    obtain ⟨p, q, hx, hy⟩ := hc.exists_of_isSubstring_append hu
    obtain ⟨r, o, hs, ht⟩ := hc.exists_of_isSubstring_append (h ▸ hu)
    obtain ⟨w, hw⟩ := hc.editor_of_isSubstring h hu
    rcases Classical.em (w = ∅) with rfl | hw'
    · left
      simp only [hx, hy, hs, ht, hc.append_empty, hc.empty_append] at hw
      and_intros
      · apply Model.ext
        rw [hx, hs]
        exact hw.elim And.left And.left
      · apply Model.ext
        rw [hy, ht]
        exact hw.elim And.right And.right
    · right
      use ⟨w, by simpa using hw'⟩
      exact hw.imp (And.imp Model.ext Model.ext) (And.imp Model.ext Model.ext)
  case concatNeZero =>
    suffices ∀ x y : nonemptyTranslation.Model M, x ++ y ≠ 0 by simpa [models_iff]
    exact fun x y h ↦ (eq_empty_of_append_isAtom <| Or.inl <| congrArg Model.val h).elim
      (nonempty x) (nonempty y)
  case concatNeOne =>
    suffices ∀ x y : nonemptyTranslation.Model M, x ++ y ≠ 1 by simpa [models_iff]
    exact fun x y h ↦ (eq_empty_of_append_isAtom <| Or.inr <| congrArg Model.val h).elim
      (nonempty x) (nonempty y)
  case zeroNeOne =>
    suffices (0 : nonemptyTranslation.Model M) ≠ 1 by simpa [models_iff]
    exact fun h ↦ WTCEmpty.zero_ne_one (M := M) <| congrArg Model.val h

end WTCEmpty

/--
$\mathsf{WTC}$ with the empty string interprets $\mathsf{WTC}$ on the nonempty strings.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖ₑ ⊳ 𝗪𝗧𝗖 where
  trln := WTCEmpty.nonemptyTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

namespace WTC

variable {M : Type} [ConcatenationStructure M] {w x y z : M}

/-- `w` is the only string that yields `y` after the letter $1$. -/
def IsDecode (w y : M) : Prop := y = 1 ++ w ∧ ∀ v, y = 1 ++ v → v = w

/-- `w` is the only string that yields `y` after the letter $1$. -/
def isDecode : Semisentence ℒ⌢ 2 :=
  “w y. y = !!(op(1).const) ⌢ w ∧ ∀ v, y = !!(op(1).const) ⌢ v → v = w”

@[simp]
lemma eval_isDecode : M ⊧/![w, y] isDecode ↔ IsDecode w y := by simp [isDecode, IsDecode]

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def IsCodeAppend (z x y : M) : Prop :=
  (y = 1 ∧ z = x) ∨ (∃ w, IsDecode w y ∧ z = x ++ w) ∨ (y ≠ 1 ∧ (∀ w, ¬IsDecode w y) ∧ z = 0)

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(1).const) ∧ z = x) ∨ (∃ w, !isDecode w y ∧ z = x ⌢ w) ∨
    (y ≠ !!(op(1).const) ∧ (∀ w, ¬!isDecode w y) ∧ z = !!(op(0).const))”

@[simp]
lemma eval_isCodeAppend : M ⊧/![z, x, y] isCodeAppend ↔ IsCodeAppend z x y := by
  simp [isCodeAppend, IsCodeAppend]

/-- The code of a possibly empty binary string: the string after the letter $1$. -/
def emptyCode (u : List Bool) : M := ofFreeSemigroup ⟨true, u⟩

@[simp]
lemma emptyCode_nil : (emptyCode [] : M) = 1 := rfl

section model

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

lemma not_isDecode_one : ¬IsDecode w (1 : M) := fun h ↦ append_ne_one _ _ h.1.symm

lemma existsUnique_isCodeAppend (x y : M) : ∃! z, IsCodeAppend z x y := by
  by_cases h₁ : y = 1
  · use x
    simp [IsCodeAppend, h₁, not_isDecode_one]
  by_cases h₂ : ∃ w, IsDecode w y
  · obtain ⟨w, hw⟩ := h₂
    have hw' (v : M) : IsDecode v y ↔ v = w :=
      ⟨fun h ↦ hw.2 v h.1, fun h ↦ h ▸ hw⟩
    use x ++ w
    simp [IsCodeAppend, h₁, hw']
  · use 0
    simp_all [IsCodeAppend]

lemma emptyCode_cons (b : Bool) (l : List Bool) :
    (emptyCode (b :: l) : M) = 1 ++ ofFreeSemigroup ⟨b, l⟩ :=
  ofFreeSemigroup_mul 1 ⟨b, l⟩

lemma isDecode_emptyCode (b : Bool) (l : List Bool) :
    IsDecode (ofFreeSemigroup ⟨b, l⟩ : M) (emptyCode (b :: l)) := by
  and_intros
  · exact emptyCode_cons b l
  · intro v h
    obtain ⟨p, q, hp, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
    obtain rfl : 1 = p := ofFreeSemigroup_injective hp
    have e := congrArg FreeSemigroup.toList e
    congr 1
    apply FreeSemigroup.toList_injective
    simpa [FreeSemigroup.toList, one_eq_of_true, FreeSemigroup.of] using e.symm

lemma isCodeAppend_emptyCode (u v : List Bool) :
    IsCodeAppend (emptyCode (u ++ v) : M) (emptyCode u) (emptyCode v) := by
  rcases v with _ | ⟨b, l⟩
  · left
    simp
  · right; left
    use ofFreeSemigroup ⟨b, l⟩
    exact ⟨isDecode_emptyCode b l, ofFreeSemigroup_mul ⟨true, u⟩ ⟨b, l⟩⟩

lemma exists_of_isCodeAppend_emptyCode {u : List Bool} (h : IsCodeAppend (emptyCode u) x y) :
    ∃ p q, x = emptyCode p ∧ y = emptyCode q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, -⟩, h⟩ | ⟨-, -, h⟩
  · use u, []
    simp
  · obtain ⟨⟨a, p⟩, ⟨b, q⟩, rfl, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
    obtain rfl : true = a := congrArg FreeSemigroup.head e
    use p, b :: q
    exact ⟨rfl, (emptyCode_cons b q).symm⟩
  · have e : (⟨true, u⟩ : FreeSemigroup Bool) = 0 := ofFreeSemigroup_injective (M := M) h
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
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_isCodeAppend (e 0) (e 1)
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

lemma dom (x : M) : emptyTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

/-- The letters, the concatenation and the empty string coded in a model of $\mathsf{WTC}$. -/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure (emptyTranslation.Model M) where
  zero := ⟨1 ++ 0, dom _⟩
  one := ⟨1 ++ 1, dom _⟩
  append x y := ⟨(existsUnique_isCodeAppend (x : M) y).choose, dom _⟩
  emptyCollection := ⟨1, dom _⟩

/--
The structure of the model of `emptyTranslation` is the standard one of
`concatenationEmptyStructure`.
-/
lemma struc_eq :
    Model.struc emptyTranslation M = @standardModelEmpty _ concatenationEmptyStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · rw [Matrix.fun_eq_vec_two fun i ↦ (v i : M)]
        exact eval_isCodeAppend.mpr (existsUnique_isCodeAppend (v 0 : M) (v 1)).choose_spec.1
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

end emptyTranslation

/--
The strings of a model of $\mathsf{WTC}$ code a model of $\mathsf{WTC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] : (emptyTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := by
  rw [emptyTranslation.struc_eq]
  let := emptyTranslation.concatenationEmptyStructure (M := M)
  have isCodeAppend (x y : emptyTranslation.Model M) : IsCodeAppend ((x ++ y : _) : M) x y :=
    (existsUnique_isCodeAppend (x : M) y).choose_spec.1
  let c (u : List Bool) : emptyTranslation.Model M := ⟨emptyCode u, emptyTranslation.dom _⟩
  apply IsInitialEmptyEmbedding.models_WTCEmpty (c := c)
  constructor
  case injective =>
    intro u v h
    exact congrArg FreeSemigroup.tail <| ofFreeSemigroup_injective (congrArg Model.val h)
  case map_nil => rfl
  case map_false => rfl
  case map_true => rfl
  case map_append =>
    exact fun u v ↦ Model.ext <| (existsUnique_isCodeAppend _ _).unique
      (isCodeAppend_emptyCode u v) (isCodeAppend (c u) (c v))
  case exists_of_append_eq =>
    intro x y u h
    obtain ⟨p, q, hp, hq⟩ : ∃ p q, (x : M) = emptyCode p ∧ (y : M) = emptyCode q :=
      exists_of_isCodeAppend_emptyCode <| (congrArg Model.val h) ▸ isCodeAppend x y
    use p, q
    exact ⟨Model.ext hp, Model.ext hq⟩

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

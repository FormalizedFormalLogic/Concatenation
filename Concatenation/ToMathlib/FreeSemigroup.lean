module

public import Mathlib.Algebra.Free
public import Mathlib.Data.List.Infix

/-!
# Prefixes, substrings and equidivisibility in the free semigroup
-/

@[expose] public section

namespace FreeSemigroup

variable {α : Type*} {x y : FreeSemigroup α}

/-- The nonempty list of letters of an element of the free semigroup. -/
def toList (x : FreeSemigroup α) : List α := x.head :: x.tail

/-- The element of the free semigroup with the given letters, if there are any. -/
def ofList? : List α → Option (FreeSemigroup α)
  | [] => none
  | a :: l => some ⟨a, l⟩

@[simp]
lemma toList_mul : (x * y).toList = x.toList ++ y.toList := rfl

@[simp]
lemma toList_of (a : α) : (of a).toList = [a] := rfl

lemma toList_injective : Function.Injective (toList : FreeSemigroup α → List α) := fun x y h ↦ by
  cases x; cases y; simpa [toList] using h

@[simp]
lemma ofList?_eq_some_iff {l : List α} : ofList? l = some x ↔ l = x.toList := by
  cases x; cases l <;> simp [ofList?, toList]

/-- Every list is empty or the list of letters of an element of the free semigroup. -/
lemma eq_nil_or_exists_toList (l : List α) : l = [] ∨ ∃ x : FreeSemigroup α, l = x.toList := by
  cases l with
  | nil => exact .inl rfl
  | cons a l => exact .inr ⟨⟨a, l⟩, rfl⟩

/-- The nonempty prefixes. -/
def prefixes (x : FreeSemigroup α) : List (FreeSemigroup α) := x.toList.inits.filterMap ofList?

/-- The nonempty substrings. -/
def substrings (x : FreeSemigroup α) : List (FreeSemigroup α) :=
  x.toList.tails.flatMap fun l ↦ l.inits.filterMap ofList?

lemma mem_prefixes_iff : y ∈ x.prefixes ↔ y = x ∨ ∃ z, x = y * z := by
  simp only [prefixes, List.mem_filterMap, List.mem_inits, ofList?_eq_some_iff, exists_eq_right]
  constructor
  · rintro ⟨l, hl⟩
    rcases eq_nil_or_exists_toList l with rfl | ⟨z, rfl⟩
    · exact .inl <| toList_injective <| by simpa using hl
    · exact .inr ⟨z, toList_injective hl.symm⟩
  · rintro (rfl | ⟨z, rfl⟩) <;> simp

lemma mem_substrings_iff :
    y ∈ x.substrings ↔
      y = x ∨ (∃ u, x = u * y) ∨ (∃ v, x = y * v) ∨ ∃ u v, x = u * y * v := by
  have h : y ∈ x.substrings ↔ y.toList <:+: x.toList := by
    simp [substrings, List.infix_iff_prefix_suffix, and_comm]
  rw [h]
  constructor
  · rintro ⟨s, t, e⟩
    rcases eq_nil_or_exists_toList s with rfl | ⟨u, rfl⟩ <;>
    rcases eq_nil_or_exists_toList t with rfl | ⟨v, rfl⟩
    · exact .inl <| toList_injective <| by simpa using e
    · exact .inr <| .inr <| .inl ⟨v, toList_injective <| by simpa using e.symm⟩
    · exact .inr <| .inl ⟨u, toList_injective <| by simpa using e.symm⟩
    · exact .inr <| .inr <| .inr ⟨u, v, toList_injective <| by simpa using e.symm⟩
  · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩)
    · exact List.infix_refl _
    · exact ⟨u.toList, [], by simp⟩
    · exact ⟨[], v.toList, by simp⟩
    · exact ⟨u.toList, v.toList, by simp⟩

lemma toList_inj : x.toList = y.toList ↔ x = y := toList_injective.eq_iff

lemma of_ne_mul (a : α) (x y : FreeSemigroup α) : of a ≠ x * y := fun h ↦ by
  simpa [length_mul, length_of, length] using congrArg length h

/-- Equidivisibility of the free semigroup. -/
lemma mul_eq_mul_iff {z w : FreeSemigroup α} :
    x * y = z * w ↔ (x = z ∧ y = w) ∨ ∃ u, (x * u = z ∧ y = u * w) ∨ (x = z * u ∧ u * y = w) := by
  rw [← toList_inj, toList_mul, toList_mul, List.append_eq_append_iff]
  constructor
  · rintro (⟨l, hz, hy⟩ | ⟨l, hx, hw⟩) <;> rcases eq_nil_or_exists_toList l with rfl | ⟨u, rfl⟩
    · exact .inl ⟨toList_injective <| by simpa using hz.symm, toList_injective hy⟩
    · exact .inr ⟨u, .inl ⟨toList_injective hz.symm, toList_injective hy⟩⟩
    · exact .inl ⟨toList_injective <| by simpa using hx, toList_injective hw.symm⟩
    · exact .inr ⟨u, .inr ⟨toList_injective hx, toList_injective hw.symm⟩⟩
  · rintro (⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact .inl ⟨[], by simp⟩
    · exact .inl ⟨u.toList, by simp⟩
    · exact .inr ⟨u.toList, by simp⟩

end FreeSemigroup

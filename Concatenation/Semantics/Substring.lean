module

public import Concatenation.Semantics.Basic

/-!
# Atoms, substrings and tallies

Atoms, substrings, initial and end segments, and tallies in a concatenation structure, with the
formulas of `ℒ⌢` defining them.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M]

/-- `x` is one of the letters `0` and `1`. -/
def IsAtom (x : M) : Prop := x = 0 ∨ x = 1

/--
`x` is a substring of `y`. Both associations of `u ++ x ++ v` are listed, so that the relation is
the one `isSubstring` defines in any concatenation structure.
- [Gan09, §1, Definition 1]
-/
def IsSubstring (x y : M) : Prop :=
  x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨ (∃ u v, y = (u ++ x) ++ v) ∨
    ∃ u v, y = u ++ (x ++ v)

/--
`x` is an initial segment of `y`.
- [Gan09, §1, Definition 1]
-/
def IsInitialSegment (x y : M) : Prop := x = y ∨ ∃ v, y = x ++ v

/--
`x` is an end segment of `y`.
- [Gan09, §1, Definition 1]
-/
def IsEndSegment (x y : M) : Prop := x = y ∨ ∃ u, y = u ++ x

/--
`x` is a `c`-tally: every atom that is a substring of `x` is `c`.
- [Gan09, §1, Definition 1]
-/
def IsTally (c x : M) : Prop := ∀ y, IsAtom y → IsSubstring y x → y = c

/-- `x` is one of the letters `0` and `1`. -/
def isAtom : Semisentence ℒ⌢ 1 := “x. x = !!(op(0).const) ∨ x = !!(op(1).const)”

/-- `x` is an initial segment of `y`. -/
def isInitialSegment : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ v, y = x ⌢ v”

/-- `x` is an end segment of `y`. -/
def isEndSegment : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

/-- `x` is a `c`-tally. -/
def isTally : Semisentence ℒ⌢ 2 := “c x. ∀ y, !isAtom y → !isSubstring y x → y = c”

variable {c x y : M}

@[simp]
lemma isAtom_zero : IsAtom (0 : M) := Or.inl rfl

@[simp]
lemma isAtom_one : IsAtom (1 : M) := Or.inr rfl

@[refl, simp]
lemma IsSubstring.refl (x : M) : IsSubstring x x := Or.inl rfl

@[simp]
lemma isSubstring_append_left (x y : M) : IsSubstring x (x ++ y) := by
  right; right; left; use y

@[simp]
lemma isSubstring_append_right (x y : M) : IsSubstring y (x ++ y) := by
  right; left; use x

@[simp]
lemma isSubstring_append_append (u x v : M) : IsSubstring x (u ++ x ++ v) := by
  right; right; right; left; use u, v

@[refl, simp]
lemma IsInitialSegment.refl (x : M) : IsInitialSegment x x := Or.inl rfl

@[simp]
lemma isInitialSegment_append (x y : M) : IsInitialSegment x (x ++ y) := by
  right; use y

@[refl, simp]
lemma IsEndSegment.refl (x : M) : IsEndSegment x x := Or.inl rfl

@[simp]
lemma isEndSegment_append (x y : M) : IsEndSegment y (x ++ y) := by
  right; use x

lemma IsInitialSegment.isSubstring (h : IsInitialSegment x y) : IsSubstring x y := by
  rcases h with rfl | ⟨v, rfl⟩ <;> simp

lemma IsEndSegment.isSubstring (h : IsEndSegment x y) : IsSubstring x y := by
  rcases h with rfl | ⟨u, rfl⟩ <;> simp

@[simp]
lemma eval_isAtom : M ⊧/![x] isAtom ↔ IsAtom x := by simp [isAtom, IsAtom]

@[simp]
lemma eval_isSubstring : M ⊧/![x, y] (isSubstring : Semisentence ℒ⌢ 2) ↔ IsSubstring x y := by
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := y)]

@[simp]
lemma eval_isInitialSegment : M ⊧/![x, y] isInitialSegment ↔ IsInitialSegment x y := by
  simp [isInitialSegment, IsInitialSegment]

@[simp]
lemma eval_isEndSegment : M ⊧/![x, y] isEndSegment ↔ IsEndSegment x y := by
  simp [isEndSegment, IsEndSegment]

@[simp]
lemma eval_isTally : M ⊧/![c, x] isTally ↔ IsTally c x := by
  simp [isTally, IsTally]

end FFL.FirstOrder.Concatenation

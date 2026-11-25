module

public import Concatenation.Semantics.Basic

/-!
# Pairs, sequences and multiplication sequences

Ganea's coding of finite sequences of pairs of `1`-tallies by strings in a concatenation structure,
with the formulas of `ℒ⌢` defining it.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {M : Type*} [ConcatenationStructure M]

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

/--
`z` is a sequence: it begins with `001`, ends with `100`, and its only `0`-tally substrings are
`0` and `00`.
- [Gan09, §1, Definition 1(d)]
-/
def IsSeq (z : M) : Prop :=
  0 ++ 0 ++ 1 ⊑ₚ z ∧ 1 ++ 0 ++ 0 ⊑ₛ z ∧
    ∀ y, IsTally 0 y → IsSubstring y z → y = 0 ∨ y = 0 ++ 0

/--
`y` is a member of the sequence `z`.
- [Gan09, §1, Definition 1(e)]
-/
def Mem (y z : M) : Prop :=
  IsSeq z ∧ ¬IsSubstring (0 ++ 0) y ∧ IsSubstring (0 ++ 0 ++ y ++ 0 ++ 0) z

/--
`z` is a sequence of ordered pairs.
- [Gan09, §1, Definition 1(e)]
-/
def IsPairSeq (z : M) : Prop := IsSeq z ∧ ∀ y, Mem y z → IsPair y

/--
`u` is the first member of `z`.
- [Gan09, §1, Definition 1(f)]
-/
def IsFirst (u z : M) : Prop := 0 ++ 0 ++ u ++ 0 ++ 0 ⊑ₚ z

/--
`u` is the last member of `z`.
- [Gan09, §1, Definition 1(f)]
-/
def IsLast (u z : M) : Prop := 0 ++ 0 ++ u ++ 0 ++ 0 ⊑ₛ z

/--
`z` is a multiplication sequence for the `1`-tallies `x` and `y`: a sequence of pairs from
`(x, 1)` to `(w, y)` for some `1`-tally `w`, in which each pair but the first is `(u x, v 1)` for
the pair `(u, v)` immediately before it. Each pair `(u, v)` in it records $x \cdot v = u$.
The last clause is the one of Švejdar.
- [Gan09, §1, Definition 1(g)]
- [Sve09, §3]
-/
def IsMulSeq (x y z : M) : Prop :=
  IsTally 1 x ∧ IsTally 1 y ∧ IsPairSeq z ∧ IsFirst (pairOf x 1) z ∧
    (∃ w, IsTally 1 w ∧ IsLast (pairOf w y) z) ∧
    ∀ s u' v', IsTally 1 u' → IsTally 1 v' →
      s ++ 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0 ⊑ₚ z →
      ∃ u v, IsTally 1 u ∧ IsTally 1 v ∧ u' = u ++ x ∧ v' = v ++ 1 ∧
        0 ++ 0 ++ pairOf u v ⊑ₛ s

/-- `z` is an ordered pair of `1`-tallies. -/
def isPair : Semisentence ℒ⌢ 1 :=
  “z. ∃ x y, !isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧
    z = x ⌢ !!(op(0).const) ⌢ y”

/-- `z` is a sequence. -/
def isSeq : Semisentence ℒ⌢ 1 :=
  “z. !isPrefix (!!(op(0).const) ⌢ !!(op(0).const) ⌢ !!(op(1).const)) z ∧
    !isSuffix (!!(op(1).const) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z ∧
    ∀ y, !isTally !!(op(0).const) y → !isSubstring y z →
      y = !!(op(0).const) ∨ y = !!(op(0).const) ⌢ !!(op(0).const)”

/-- `y` is a member of the sequence `z`. -/
def mem : Semisentence ℒ⌢ 2 :=
  “y z. !isSeq z ∧ ¬!isSubstring (!!(op(0).const) ⌢ !!(op(0).const)) y ∧
    !isSubstring
      (!!(op(0).const) ⌢ !!(op(0).const) ⌢ y ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

/-- `z` is a sequence of ordered pairs. -/
def isPairSeq : Semisentence ℒ⌢ 1 := “z. !isSeq z ∧ ∀ y, !mem y z → !isPair y”

/-- `u` is the first member of `z`. -/
def isFirst : Semisentence ℒ⌢ 2 :=
  “u z. !isPrefix
    (!!(op(0).const) ⌢ !!(op(0).const) ⌢ u ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

/-- `u` is the last member of `z`. -/
def isLast : Semisentence ℒ⌢ 2 :=
  “u z. !isSuffix
    (!!(op(0).const) ⌢ !!(op(0).const) ⌢ u ⌢ !!(op(0).const) ⌢ !!(op(0).const)) z”

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

variable {x y z u : M}

@[simp]
lemma eval_isPair : M ⊧/![z] isPair ↔ IsPair z := by simp [isPair, IsPair, pairOf]

@[simp]
lemma eval_isSeq : M ⊧/![z] isSeq ↔ IsSeq z := by simp [isSeq, IsSeq]

@[simp]
lemma eval_mem : M ⊧/![y, z] mem ↔ Mem y z := by simp [mem, Mem]

@[simp]
lemma eval_isPairSeq : M ⊧/![z] isPairSeq ↔ IsPairSeq z := by simp [isPairSeq, IsPairSeq]

@[simp]
lemma eval_isFirst : M ⊧/![u, z] isFirst ↔ IsFirst u z := by simp [isFirst, IsFirst]

@[simp]
lemma eval_isLast : M ⊧/![u, z] isLast ↔ IsLast u z := by simp [isLast, IsLast]

@[simp]
lemma eval_isMulSeq : M ⊧/![x, y, z] isMulSeq ↔ IsMulSeq x y z := by
  simp [isMulSeq, IsMulSeq, pairOf]

lemma IsPairSeq.isSeq (h : IsPairSeq z) : IsSeq z := h.1

lemma IsMulSeq.isTally_left (h : IsMulSeq x y z) : IsTally 1 x := h.1

lemma IsMulSeq.isTally_right (h : IsMulSeq x y z) : IsTally 1 y := h.2.1

lemma IsMulSeq.isPairSeq (h : IsMulSeq x y z) : IsPairSeq z := h.2.2.1

lemma IsMulSeq.exists_isLast (h : IsMulSeq x y z) : ∃ w, IsTally 1 w ∧ IsLast (pairOf w y) z :=
  h.2.2.2.2.1

end FFL.FirstOrder.Concatenation

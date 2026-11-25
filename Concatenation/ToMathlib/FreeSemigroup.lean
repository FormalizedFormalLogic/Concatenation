module

public import Mathlib.Algebra.Free
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Finite.List

/-!
# The free semigroup

Prefixes, substrings and equidivisibility in the free semigroup, and codes of its elements by
natural numbers.
-/

@[expose] public section

open Encodable

variable {α : Type*}

namespace List

variable [Encodable α]

lemma encode_le_encode_append_left (l₁ l₂ : List α) : encode l₁ ≤ encode (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, encode_list_cons, Nat.succ_le_succ_iff]
    rcases ih.eq_or_lt with h | h
    · rw [h]
    · exact (Nat.pair_lt_pair_right _ h).le

lemma encode_le_encode_append_right (l₁ l₂ : List α) : encode l₂ ≤ encode (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, encode_list_cons]
    exact ih.trans <| (Nat.right_le_pair _ _).trans <| Nat.le_succ _

end List

namespace FreeSemigroup

variable {x y : FreeSemigroup α}

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
  · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩) <;>
      simp [List.infix_append_left, List.infix_append_right]

lemma finite_length_le [Finite α] (n : ℕ) : {x : FreeSemigroup α | x.length ≤ n}.Finite :=
  ((List.finite_length_le α n).preimage toList_injective.injOn).subset
    fun x hx ↦ by simpa [toList, length] using hx

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

section Encodable

variable [Encodable α]

/-- The code of an element of the free semigroup: that of its list of letters. -/
def code (x : FreeSemigroup α) : ℕ := encode x.toList

lemma code_injective : Function.Injective (code : FreeSemigroup α → ℕ) :=
  encode_injective.comp toList_injective

@[simp]
lemma code_inj {x y : FreeSemigroup α} : x.code = y.code ↔ x = y := code_injective.eq_iff

@[simp]
lemma code_ne_zero (x : FreeSemigroup α) : x.code ≠ 0 := by simp [code, toList]

lemma code_le_code_mul_left (x y : FreeSemigroup α) : x.code ≤ (x * y).code :=
  List.encode_le_encode_append_left _ _

lemma code_le_code_mul_right (x y : FreeSemigroup α) : y.code ≤ (x * y).code :=
  List.encode_le_encode_append_right x.toList y.toList

/--
The code of the product of the elements coded by `m` and `n`, and `0` if one of them is not a
code.
-/
def mulCode (α : Type*) [Encodable α] (m n : ℕ) : ℕ :=
  ((decode₂ (List α) m).bind fun x ↦ (decode₂ (List α) n).map fun y ↦
    if x = [] ∨ y = [] then 0 else encode (x ++ y)).getD 0

@[simp]
lemma mulCode_code (x y : FreeSemigroup α) : mulCode α x.code y.code = (x * y).code := by
  simp [mulCode, code, decode₂_encode]
  simp [toList]

lemma eq_code_of_mulCode_ne_zero {m n : ℕ} (h : mulCode α m n ≠ 0) :
    ∃ x y : FreeSemigroup α, m = x.code ∧ n = y.code := by
  rcases hm : decode₂ (List α) m with _ | l₁
  · simp [mulCode, hm] at h
  rcases hn : decode₂ (List α) n with _ | l₂
  · simp [mulCode, hm, hn] at h
  rcases eq_nil_or_exists_toList l₁ with rfl | ⟨x, rfl⟩
  · simp [mulCode, hm, hn] at h
  rcases eq_nil_or_exists_toList l₂ with rfl | ⟨y, rfl⟩
  · simp [mulCode, hm, hn] at h
  use x, y
  exact ⟨(mem_decode₂.mp hm).symm, (mem_decode₂.mp hn).symm⟩

end Encodable

/-- The product on codes is primitive recursive. -/
lemma primrec₂_mulCode [Primcodable α] : Primrec₂ (mulCode α) := by
  have h₁ : Primrec fun p : ℕ × ℕ ↦ decode₂ (List α) p.1 :=
    Primrec.decode₂.comp Primrec.fst
  have h₂ : Primrec₂ fun (p : ℕ × ℕ) (_ : List α) ↦ decode₂ (List α) p.2 :=
    Primrec.decode₂.comp (Primrec.snd.comp Primrec.fst)
  have hx : Primrec fun q : ((ℕ × ℕ) × List α) × List α ↦ q.1.2 := Primrec.snd.comp Primrec.fst
  have h₃ : Primrec₂ fun (q : (ℕ × ℕ) × List α) (y : List α) ↦
      if q.2 = [] ∨ y = [] then 0 else encode (q.2 ++ y) :=
    Primrec.ite ((Primrec.eq.comp hx (Primrec.const [])).or
      (Primrec.eq.comp Primrec.snd (Primrec.const []))) (Primrec.const 0)
      (Primrec.encode.comp (Primrec.list_append.comp hx Primrec.snd))
  exact Primrec.option_getD.comp (Primrec.option_bind h₁ (Primrec.option_map h₂ h₃))
    (Primrec.const 0)

end FreeSemigroup

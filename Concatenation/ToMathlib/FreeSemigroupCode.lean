module

public import Concatenation.ToMathlib.FreeSemigroup
public import Mathlib.Computability.Primrec.List

/-!
# Codes of the elements of the free semigroup by natural numbers
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

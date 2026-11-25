module

public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Cobham's order on models of $\mathsf{R}_0$

Cobham's order compares every element of a model of $\mathsf{R}_0$ with every numeral.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure

/--
`y` is regular: $0 \le y$, and $v + 1 \le y$ for every $v < y$.
- [Sve08, §3.3]
-/
def isRegular : ArithmeticSemisentence 1 := “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

/--
Cobham's order: $x \le y$, or $y$ is not regular.
- [Sve08, §3.3]
-/
def cobhamLE : ArithmeticSemisentence 2 := “x y. x ≤ y ∨ ¬!isRegular y”

variable {M : Type*} [ORingStructure M] {x y : M}

/--
`y` is regular: $0 \le y$, and $v + 1 \le y$ for every $v < y$.
- [Sve08, §3.3]
-/
def IsRegular (y : M) : Prop := (0 = y ∨ 0 < y) ∧ ∀ v < y, v + 1 = y ∨ v + 1 < y

/--
Cobham's order: $x \le y$, or $y$ is not regular.
- [Sve08, §3.3]
-/
def CobhamLE (x y : M) : Prop := (x = y ∨ x < y) ∨ ¬IsRegular y
@[inherit_doc]
scoped infix:50 " ⊴ " => CobhamLE

@[simp]
lemma eval_isRegular : M ⊧/![y] isRegular ↔ IsRegular y := by
  simp [isRegular, IsRegular, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp]
lemma eval_cobhamLE : M ⊧/![x, y] cobhamLE ↔ x ⊴ y := by
  simp [cobhamLE, CobhamLE, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma numeral_add_one (n : ℕ) : (numeral n : M) + 1 = numeral (n + 1) := by
  simpa using numeral_add_numeral (M := M) n 1

/--
Every numeral is regular.
- [Sve08, §3.3, Lemma 2]
-/
lemma isRegular_numeral (n : ℕ) : IsRegular (numeral n : M) := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · right
      simpa using (numeral_lt_numeral_iff (M := M)).mpr hn
  · intro v hv
    rcases lt_numeral_iff.mp hv with ⟨i, rfl⟩
    rw [numeral_add_one, numeral_inj_iff, numeral_lt_numeral_iff]
    omega

/--
Below a numeral, Cobham's order is $\le$.
- [Sve08, §3.3, Lemma 2]
-/
lemma cobhamLE_numeral_iff {n : ℕ} : x ⊴ numeral n ↔ x = numeral n ∨ x < numeral n := by
  simp [CobhamLE, isRegular_numeral]

lemma exists_eq_numeral_or_numeral_le_of_isRegular (hx : IsRegular x) (k : ℕ) :
    (∃ i < k, x = numeral i) ∨ numeral k = x ∨ numeral k < x := by
  induction k with
  | zero => simpa using hx.1
  | succ k ih =>
    rcases ih with ⟨i, hi, rfl⟩ | h | h
    · left
      use i
      and_intros
      · omega
      · rfl
    · left
      use k
      and_intros
      · omega
      · exact h.symm
    · right
      simpa [numeral_add_one] using hx.2 _ h

/--
Every element is comparable with every numeral in Cobham's order.
- [Sve08, §3.3, Lemma 2]
-/
lemma cobhamLE_numeral_or (n : ℕ) : x ⊴ numeral n ∨ numeral n ⊴ x := by
  by_cases hx : IsRegular x
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hx n with ⟨i, hi, rfl⟩ | h
    · left
      simp [cobhamLE_numeral_iff, hi]
    · right
      exact Or.inl h
  · right
    exact Or.inr hx

lemma eq_numeral_of_cobhamLE_numeral {n : ℕ} (h : x ⊴ numeral n) :
    ∃ i ≤ n, x = numeral i := by
  rcases cobhamLE_numeral_iff.mp h with rfl | h
  · use n
  · rcases lt_numeral_iff.mp h with ⟨i, rfl⟩
    use i
    and_intros
    · exact i.isLt.le
    · rfl

lemma cobhamLE_numeral_of_le {k q : ℕ} {w : M} (hkq : k ≤ q) (h : numeral q ⊴ w) :
    numeral k ⊴ w := by
  by_cases hw : IsRegular w
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hw k with ⟨i, hi, rfl⟩ | h'
    · rcases h with h | h
      · simp only [numeral_inj_iff, numeral_lt_numeral_iff] at h
        omega
      · exact absurd hw h
    · exact Or.inl h'
  · exact Or.inr hw

@[simp]
lemma numeral_cobhamLE_numeral_iff {k n : ℕ} : (numeral k : M) ⊴ numeral n ↔ k ≤ n := by
  simp [cobhamLE_numeral_iff]
  omega

end FFL.FirstOrder.Arithmetic.R0

module

public import Concatenation.ToFoundation.Arithmetic.Q

/-!
# Local finite satisfiability of $\mathsf{R}_0$

$\mathsf{R}_0$ is locally finitely satisfiable, so that it does not interpret $\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

namespace R0

/-- The natural numbers up to `N`, with the operations truncated at `N`. -/
def Truncation (N : ℕ) : Type := Fin (N + 1)

namespace Truncation

variable {N : ℕ}

/-- The smaller of `n` and `N`. -/
def of (N n : ℕ) : Truncation N := ⟨min n N, by omega⟩

instance : Finite (Truncation N) := inferInstanceAs (Finite (Fin (N + 1)))

instance : ORingStructure (Truncation N) where
  zero := of N 0
  one := of N 1
  add x y := of N (x.val + y.val)
  mul x y := of N (x.val * y.val)
  lt x y := x.val < y.val

lemma ext_iff {x y : Truncation N} : x = y ↔ x.val = y.val := Fin.ext_iff

lemma lt_iff {x y : Truncation N} : x < y ↔ x.val < y.val := Iff.rfl

@[simp]
lemma val_of (n : ℕ) : (of N n).val = min n N := rfl

lemma of_add_of (n m : ℕ) : of N n + of N m = of N (n + m) := by
  change of N (min n N + min m N) = of N (n + m)
  simp only [ext_iff, val_of]
  omega

lemma of_mul_of (n m : ℕ) : of N n * of N m = of N (n * m) := by
  have h (a : ℕ) {b : ℕ} (hb : 0 < b) : min (min a N * b) N = min (a * b) N := by
    rcases le_total a N with h | h
    · simp [h]
    · simp [h, Nat.le_mul_of_pos_right _ hb, h.trans <| Nat.le_mul_of_pos_right _ hb]
  change of N (min n N * min m N) = of N (n * m)
  simp only [ext_iff, val_of]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [h n (by omega), mul_comm, h m hn, mul_comm]

@[simp]
lemma numeral_eq : (n : ℕ) → (ORingStructure.numeral n : Truncation N) = of N n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [ORingStructure.numeral, numeral_eq (n + 1)]
    exact of_add_of (n + 1) 1

lemma lt_of_iff {n : ℕ} (h : n ≤ N) {x : Truncation N} : x < of N n ↔ ∃ i < n, x = of N i := by
  simp only [lt_iff, ext_iff, val_of]
  constructor
  · intro hx
    exact ⟨x.val, by omega, by omega⟩
  · rintro ⟨i, hi, hx⟩
    omega

end Truncation

/--
$\mathsf{R}_0$ is locally finitely satisfiable.
- [Hor11, §3, Proposition 3.2]
- [Hor12, §1]
-/
theorem locallyFinitelySatisfiable : (𝗥₀ : ArithmeticTheory).LocallyFinitelySatisfiable := by
  apply Theory.LocallyFinitelySatisfiable.of_eventually Truncation
  rintro σ ⟨⟩
  case equal h =>
    have (N : ℕ) : (Truncation N)↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    exact .of_forall fun N ↦ models_theory_iff.mp (this N) _ h
  case Ω₁ n m => simp [models_iff, Truncation.of_add_of]
  case Ω₂ n m => simp [models_iff, Truncation.of_mul_of]
  case Ω₃ n =>
    filter_upwards [Filter.eventually_ge_atTop n] with N hN
    simpa [models_iff] using fun x ↦ Truncation.lt_of_iff hN

/--
$\mathsf{R}_0$ does not interpret $\mathsf{Q}$.
- [Hor11, §3, Proposition 3.2]
- [Hor12, §1]
-/
theorem notInterprets_Q : 𝗥₀ ⋫ 𝗤 :=
  DirectInterpretation.notInterprets_of_not_hasFiniteModel locallyFinitelySatisfiable
    RobinsonQ.finiteAxiomatizable RobinsonQ.not_hasFiniteModel

end R0

end FFL.FirstOrder.Arithmetic

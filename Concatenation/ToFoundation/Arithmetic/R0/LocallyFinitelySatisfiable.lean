module

public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Foundation.FirstOrder.Arithmetic.Q.Basic

/-!
# $\mathsf{R}_0$ does not interpret $\mathsf{Q}$

$\mathsf{R}_0$ is locally finitely satisfiable and $\mathsf{Q}$ has no finite models.
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

end R0

namespace RobinsonQ

lemma finite : (𝗤 : ArithmeticTheory).Finite := by
  apply ((Theory.Eq.finite (L := ℒₒᵣ)).union
    (Set.toFinite {_, _, _, _, _, _, _, _})).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | succNeZero => exact .inr <| .inl rfl
    | succInj => exact .inr <| .inr <| .inl rfl
    | zeroOrSucc => exact .inr <| .inr <| .inr <| .inl rfl
    | addZero => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | addSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulZero => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | ltDef => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr rfl

lemma finiteAxiomatizable : FiniteAxiomatizable 𝗤 := .of_finite finite

lemma infinite_of_models (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗤] : Infinite M :=
  not_finite_iff_infinite.mp fun _ ↦
    let ⟨x, hx⟩ := Finite.surjective_of_injective (fun _ _ ↦ succ_inj : (· + (1 : M)).Injective) 0
    Arithmetic.succ_ne_zero x hx

/--
$\mathsf{Q}$ has no finite models.
- [Hor11, §3, Proposition 3.2]
-/
theorem not_hasFiniteModel : ¬(𝗤 : ArithmeticTheory).HasFiniteModel := by
  intro h
  obtain ⟨M, _, hfin, _, _, hM⟩ := h.exists_eq
  obtain ⟨N, _, _, _, s, _, hN⟩ : ∃ (N : Type) (_ : Nonempty N) (_ : Finite N)
      (_ : ORingStructure N) (_ : Tarski.Structure ℒₒᵣ N) (_ : Tarski.Structure.ORing ℒₒᵣ N),
      N↓[ℒₒᵣ] ⊧* 𝗤 :=
    let e := Tarski.Structure.Model.equiv ℒₒᵣ M
    let s : Tarski.Structure ℒₒᵣ (Tarski.Structure.Model ℒₒᵣ M) := Tarski.Structure.ofEquiv e
    ⟨Tarski.Structure.Model ℒₒᵣ M, inferInstance, .of_equiv M e, inferInstance, s,
      inferInstance,
      (Tarski.Structure.Model.elementaryEquiv ℒₒᵣ M).modelsTheory.mp hM⟩
  rcases standardModel_unique N s
  exact not_finite_iff_infinite.mpr (infinite_of_models N) inferInstance

end RobinsonQ

/--
$\mathsf{R}_0$ does not interpret $\mathsf{Q}$.
- [Hor11, §3, Proposition 3.2]
- [Hor12, §1]
-/
theorem isEmpty_R0_interprets_Q : IsEmpty (𝗥₀ ⊳ 𝗤) :=
  DirectInterpretation.isEmpty_of_not_hasFiniteModel R0.locallyFinitelySatisfiable
    RobinsonQ.finiteAxiomatizable RobinsonQ.not_hasFiniteModel

end FFL.FirstOrder.Arithmetic

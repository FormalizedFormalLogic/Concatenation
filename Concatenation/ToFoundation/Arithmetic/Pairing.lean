module

public import Foundation.FirstOrder.Arithmetic.Exponential.Bit
public import Foundation.FirstOrder.Arithmetic.R0.Basic
public import Mathlib.Tactic.Linarith

/-!
# Codes of finite objects

A pairing that is defined by a term, the codes of tuples it gives, and the codes of finite sets of
numbers.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure

variable {V : Type*} [ORingStructure V]

section pair

/-- The pairing $(a + b + 1) (a + b + 1) + a$. -/
def mkPair (a b : V) : V := (a + b + 1) * (a + b + 1) + a

/-- The pairing $(a + b + 1) (a + b + 1) + a$. -/
def mkPairTerm : ClosedSemiterm ℒₒᵣ 2 := ‘a b. (a + b + 1) * (a + b + 1) + a’

@[simp]
lemma val_subst_mkPairTerm {n : ℕ} {e : Fin n → V} {f : Empty → V}
    {t u : ClosedSemiterm ℒₒᵣ n} :
    (Rew.subst ![t, u] mkPairTerm).val e f = mkPair (t.val e f) (u.val e f) := by
  simp [mkPairTerm, mkPair]

@[simp, grind =]
lemma mkPair_inj {a b a' b' : ℕ} : mkPair a b = mkPair a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have : a + b = a' + b' := by
      simp only [mkPair] at h
      rcases lt_trichotomy (a + b) (a' + b') with h' | h' | h'
      · nlinarith
      · exact h'
      · nlinarith
    simp only [mkPair, this] at h
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp, grind .]
lemma mkPair_pos (a b : ℕ) : 0 < mkPair a b := by
  simp [mkPair]

@[simp, grind .]
lemma left_lt_mkPair (a b : ℕ) : a < mkPair a b := by
  simp [mkPair]

@[simp, grind .]
lemma right_lt_mkPair (a b : ℕ) : b < mkPair a b := by
  simp only [mkPair]
  nlinarith

@[grind ←]
lemma mkPair_le_mkPair {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    mkPair a b ≤ mkPair a' b' := by
  simp only [mkPair]
  gcongr

@[simp, grind =]
lemma mkPair_numeral [V↓[ℒₒᵣ] ⊧* 𝗥₀] (a b : ℕ) :
    mkPair (numeral a : V) (numeral b) = numeral (mkPair a b) := by
  have h : (1 : V) = numeral 1 := by simp
  simp only [mkPair, h, numeral_add_numeral, numeral_mul_numeral]

end pair

section envCode

/-- The code of the environment `v`. -/
def envCode : {n : ℕ} → (Fin n → V) → V
  | 0, _ => 0
  | _ + 1, v => mkPair (v 0) (envCode fun i ↦ v i.succ)

@[simp]
lemma envCode_zero {v : Fin 0 → V} : envCode v = 0 := rfl

@[simp, grind =]
lemma envCode_cons {n : ℕ} {a : V} {v : Fin n → V} :
    envCode (a :> v) = mkPair a (envCode v) := by
  simp [envCode]

lemma lt_envCode {n : ℕ} {v : Fin n → ℕ} (i : Fin n) : v i < envCode v := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact left_lt_mkPair _ _
    | succ i => exact (ih (v := fun i ↦ v i.succ) i).trans <| right_lt_mkPair _ _

lemma eq_of_envCode_eq {n m : ℕ} {v : Fin n → ℕ} {w : Fin m → ℕ} (h : envCode v = envCode w) :
    n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => exact absurd h (mkPair_pos _ _).ne
  | succ n ih =>
    cases m with
    | zero => exact absurd h (mkPair_pos _ _).ne'
    | succ m => exact congrArg _ <| ih (mkPair_inj.mp h).2

lemma envCode_injective {n : ℕ} : Function.Injective (envCode : (Fin n → ℕ) → ℕ) := by
  induction n with
  | zero => exact fun _ _ _ ↦ Subsingleton.elim _ _
  | succ n ih =>
    intro v w h
    obtain ⟨h₀, h₁⟩ := mkPair_inj.mp h
    funext i
    cases i using Fin.cases with
    | zero => exact h₀
    | succ i => exact congrFun (ih h₁) i

@[simp, grind =]
lemma envCode_inj {n : ℕ} {v w : Fin n → ℕ} : envCode v = envCode w ↔ v = w :=
  envCode_injective.eq_iff

/-- The code of the environment `t`. -/
def envCodeTerm {m : ℕ} : {n : ℕ} → (Fin n → ClosedSemiterm ℒₒᵣ m) → ClosedSemiterm ℒₒᵣ m
  | 0, _ => ‘0’
  | _ + 1, t => Rew.subst ![t 0, envCodeTerm fun i ↦ t i.succ] mkPairTerm

@[simp]
lemma val_envCodeTerm {m n : ℕ} {t : Fin n → ClosedSemiterm ℒₒᵣ m} {e : Fin m → V}
    {f : Empty → V} : (envCodeTerm t).val e f = envCode fun i ↦ (t i).val e f := by
  induction n with
  | zero => simp [envCodeTerm]
  | succ n ih => simp [envCodeTerm, envCode, ih]

end envCode

lemma exists_forall_mem_iff {s : Set ℕ} (hs : s.Finite) : ∃ c : ℕ, ∀ e : ℕ, e ∈ c ↔ e ∈ s := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨insert a c, fun e ↦ by simp [hc]⟩

end FFL.FirstOrder.Arithmetic

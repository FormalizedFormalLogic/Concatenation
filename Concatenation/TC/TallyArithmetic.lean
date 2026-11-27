module

public import Concatenation.TC.TallyMultiplication
public import Concatenation.ToMathlib.VecCons
public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# $\Sigma_{n+1}\text{-}\mathsf{TCI}$ interprets $\mathsf{I}\Sigma_{n+1}$

The `1`-tallies of a model of $\Sigma_{n+1}\text{-}\mathsf{TCI}$, with concatenation as addition and
the multiplication of tallies, form a model of $\mathsf{I}\Sigma_{n+1}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Bounding Arithmetic

section tallyNumber

variable (V : Type*) [ConcatenationEmptyStructure V]

/-- The `1`-tallies of `V`. -/
def TallyNumber : Type _ := {x : V // IsTally 1 x}

variable {V} [V↓[ℒ⌢ₑ] ⊧* TCISigma 1]

/--
The arithmetic of the `1`-tallies: `0` is the empty string, `1` is the letter `1`, the sum is the
concatenation, the product is the multiplication of tallies, and the order is the proper prefix
relation.
- [Gan09, §1, Definition 2]
-/
noncomputable instance : ORingStructure (TallyNumber V) where
  zero := ⟨∅, by simp⟩
  one := ⟨1, TCEmpty.isTally_one⟩
  add a b := ⟨a.1 ++ b.1, TCEmpty.isTally_append a.2 b.2⟩
  mul a b := ⟨(exists_isTallyMul a.2 b.2).choose, (exists_isTallyMul a.2 b.2).choose_spec.isTally⟩
  lt a b := IsProperPrefix a.1 b.1

namespace TallyNumber

variable {a b c : TallyNumber V}

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma ext_iff' : a = b ↔ a.1 = b.1 := Subtype.ext_iff

@[simp]
lemma val_zero : (0 : TallyNumber V).1 = ∅ := rfl

@[simp]
lemma val_one : (1 : TallyNumber V).1 = 1 := rfl

@[simp]
lemma val_add (a b : TallyNumber V) : (a + b).1 = a.1 ++ b.1 := rfl

lemma isTallyMul_val_mul (a b : TallyNumber V) : IsTallyMul a.1 b.1 (a * b).1 :=
  (exists_isTallyMul a.2 b.2).choose_spec

lemma val_mul_eq_iff {z : V} : (a * b).1 = z ↔ IsTallyMul a.1 b.1 z :=
  ⟨fun h ↦ h ▸ isTallyMul_val_mul a b, fun h ↦ (isTallyMul_val_mul a b).unique h⟩

lemma lt_iff : a < b ↔ IsProperPrefix a.1 b.1 := Iff.rfl

end TallyNumber

end tallyNumber

section definability

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] {ξ : Type*} {k : ℕ}

/--
The graph of the value of an arithmetic term on the tallies has a $\Sigma_1$ definition.
- [Gan09, §1, Definition 2]
-/
lemma exists_termGraph (t : Semiterm ℒₒᵣ ξ k) (f : ξ → TallyNumber V) :
    ∃ G : (Fin (k + 1) → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 G ∧
      ∀ (v : Fin k → TallyNumber V) (y : V), G (y :> fun i ↦ (v i).1) ↔ y = (t.val v f).1 := by
  have : Nonempty V := ⟨∅⟩
  induction t with
  | bvar i =>
    exact ⟨_, .of_delta0 (definable_eq_term #0 #i.succ), fun v y ↦ by simp⟩
  | fvar x =>
    exact ⟨_, .of_delta0 (definable_eq_term #0 &(f x).1), fun v y ↦ by simp⟩
  | func g ts ih =>
    cases g with
    | zero => exact ⟨_, .of_delta0 (definable_eq_term #0 ‘⋆’), fun v y ↦ by simp; rfl⟩
    | one => exact ⟨_, .of_delta0 (definable_eq_term #0 ‘!!(op(1).const)’), fun v y ↦ by simp; rfl⟩
    | add =>
      obtain ⟨G₁, hG₁, H₁⟩ := ih 0
      obtain ⟨G₂, hG₂, H₂⟩ := ih 1
      refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> fun i ↦ w i.succ) ∧ G₂ (y₂ :> fun i ↦ w i.succ) ∧
        w 0 = y₁ ++ y₂, ?_, fun v y ↦ ?_⟩
      · refine (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
          PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ.succ)) <|
            (hG₂.retraction (0 :> fun i ↦ i.succ.succ.succ)).and_delta0 <|
              definable_eq_term #2 ‘#1 ⌢ #0’).of_iff fun w ↦ ?_
        simp [Matrix.fun_vecCons_apply]
      · simp [H₁, H₂]
        rfl
    | mul =>
      obtain ⟨G₁, hG₁, H₁⟩ := ih 0
      obtain ⟨G₂, hG₂, H₂⟩ := ih 1
      refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> fun i ↦ w i.succ) ∧ G₂ (y₂ :> fun i ↦ w i.succ) ∧
        IsTallyMul y₁ y₂ (w 0), ?_, fun v y ↦ ?_⟩
      · refine (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
          PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ.succ)) <|
            PrenexDefinable.and_Sigma1 (hG₂.retraction (0 :> fun i ↦ i.succ.succ.succ)) <|
              prenexDefinable_isTallyMul.retraction ![1, 0, 2]).of_iff fun w ↦ ?_
        simp [Matrix.fun_vecCons_apply]
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, H₁, H₂]
        change _ ↔ y = ((ts 0).val v f * (ts 1).val v f).1
        constructor
        · rintro ⟨_, _, rfl, rfl, h⟩
          exact (TallyNumber.val_mul_eq_iff.mpr h).symm
        · rintro rfl
          exact ⟨_, _, rfl, rfl, TallyNumber.isTallyMul_val_mul _ _⟩

end definability

end FFL.FirstOrder.Concatenation

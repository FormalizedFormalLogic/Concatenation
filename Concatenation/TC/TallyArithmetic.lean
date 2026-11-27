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

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma exists_iff {P : TallyNumber V → Prop} : (∃ a, P a) ↔ ∃ x, ∃ hx : IsTally 1 x, P ⟨x, hx⟩ :=
  Subtype.exists

omit [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] in
lemma forall_iff {P : TallyNumber V → Prop} : (∀ a, P a) ↔ ∀ x, ∀ hx : IsTally 1 x, P ⟨x, hx⟩ :=
  Subtype.forall

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

/-- A relation of three $\Sigma_1$ relations through the values of two terms. -/
private lemma exists_prenexDefinable_terms (t₁ t₂ : Semiterm ℒₒᵣ ξ k) (f : ξ → TallyNumber V)
    {R : V → V → Prop} (hR : PrenexDefinable ℬₛ 𝚺 1 fun v : Fin 2 → V ↦ R (v 0) (v 1)) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 Q ∧ ∀ v : Fin k → TallyNumber V,
      (Q fun i ↦ (v i).1) ↔ R (t₁.val v f).1 (t₂.val v f).1 := by
  obtain ⟨G₁, hG₁, H₁⟩ := exists_termGraph t₁ f
  obtain ⟨G₂, hG₂, H₂⟩ := exists_termGraph t₂ f
  refine ⟨fun w ↦ ∃ y₁, ∃ y₂, G₁ (y₁ :> w) ∧ G₂ (y₂ :> w) ∧ R y₁ y₂, ?_, fun v ↦ ?_⟩
  · exact (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.exs_Sigma1 <|
      PrenexDefinable.and_Sigma1 (hG₁.retraction (1 :> fun i ↦ i.succ.succ)) <|
        PrenexDefinable.and_Sigma1 (hG₂.retraction (0 :> fun i ↦ i.succ.succ)) <|
          hR.retraction ![1, 0]).of_iff fun w ↦ by simp [Matrix.fun_vecCons_apply]
  · simp [H₁, H₂]

/--
A bounded arithmetic formula is $\Sigma_1$ on the tallies.
- [HH14, Question 3]
-/
lemma exists_prenexDefinable_of_closure {φ : Semiformula ℒₒᵣ ξ k} (hφ : ℬ[<, ℒₒᵣ].Closure φ)
    (f : ξ → TallyNumber V) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ 𝚺 1 Q ∧
      ∀ v : Fin k → TallyNumber V, (Q fun i ↦ (v i).1) ↔ φ.Eval v f := by
  have : Nonempty V := ⟨∅⟩
  induction hφ with
  | verum => exact ⟨fun _ ↦ True, .of_delta0 (by simp), by simp⟩
  | falsum => exact ⟨fun _ ↦ False, .of_delta0 (by simp), by simp⟩
  | rel r ts =>
    cases r with
    | eq =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := (· = ·))
        (.of_delta0 <| definable_eq_term #0 #1)
      exact ⟨Q, hQ, fun v ↦ (H v).trans TallyNumber.ext_iff'.symm⟩
    | lt =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := IsProperPrefix)
        (.of_delta0 isProperPrefix_definable)
      exact ⟨Q, hQ, fun v ↦ (H v).trans Iff.rfl⟩
  | nrel r ts =>
    cases r with
    | eq =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f (R := (· ≠ ·))
        (.of_delta0 <| (definable_eq_term #0 #1).not_zero)
      exact ⟨Q, hQ, fun v ↦ (H v).trans (not_congr TallyNumber.ext_iff'.symm)⟩
    | lt =>
      obtain ⟨Q, hQ, H⟩ := exists_prenexDefinable_terms (ts 0) (ts 1) f
        (R := fun x y ↦ ¬IsProperPrefix x y) (.of_delta0 isProperPrefix_definable.not_zero)
      exact ⟨Q, hQ, fun v ↦ (H v).trans Iff.rfl⟩
  | and _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, H₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂, H₂⟩ := ih₂
    exact ⟨_, PrenexDefinable.and_Sigma1 hQ₁ hQ₂, fun v ↦ by simp [H₁, H₂]⟩
  | or _ _ ih₁ ih₂ =>
    obtain ⟨Q₁, hQ₁, H₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂, H₂⟩ := ih₂
    exact ⟨_, PrenexDefinable.or_Sigma1 hQ₁ hQ₂, fun v ↦ by simp [H₁, H₂]⟩
  | @ball k R φ t hR ht _ ih =>
    obtain rfl : R = Semiformula.Operator.LT.lt := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    have key (v : Fin k → TallyNumber V) :
        (∀¹[(Semiformula.Operator.LT.lt).operator ![#0, Rew.bShift t]] φ).Eval v f ↔
          ∀ x : TallyNumber V, x < t.val v f → φ.Eval (x :> v) f := by
      simp [Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, Semiterm.val_bShift']
    obtain ⟨G, hG, HG⟩ := exists_termGraph t f
    obtain ⟨Q, hQ, HQ⟩ := ih
    obtain ⟨C, hC, HC⟩ := TCISigma.exists_prenexDefinable_ball (k := k)
      (P := fun u ↦ Q (u 0 :> fun i ↦ u i.succ.succ) ∨ u 0 = u 1)
      ((hQ.retraction (0 :> fun i ↦ i.succ.succ)).or_delta0 (definable_eq_term #0 #1) |>.of_iff
        fun u ↦ by simp [Matrix.fun_vecCons_apply])
    refine ⟨fun w ↦ ∃ b, G (b :> w) ∧ C (b :> w),
      PrenexDefinable.exs_Sigma1 (PrenexDefinable.and_Sigma1 hG hC), fun v ↦ ?_⟩
    have HC' := HC ((t.val v f).1 :> fun i ↦ (v i).1) (t.val v f).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at HC'
    rw [key]
    constructor
    · rintro ⟨b, hb, hc⟩ x hx
      obtain rfl := (HG v b).mp hb
      have hx' := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mpr ⟨x.2, hx⟩
      rcases HC'.mp hc x.1 hx'.1 with h | h
      · exact (HQ (x :> v)).mp <|
          cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val x v).symm) h
      · exact absurd h hx'.2
    · intro h
      refine ⟨_, (HG v _).mpr rfl, HC'.mpr fun y hy ↦ ?_⟩
      by_cases hyb : y = (t.val v f).1
      · exact .inr hyb
      · obtain ⟨ty, hlt⟩ := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mp ⟨hy, hyb⟩
        have := (HQ ((⟨y, ty⟩ : TallyNumber V) :> v)).mpr (h ⟨y, ty⟩ hlt)
        exact .inl <| cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val _ v)) this
  | @bexs k R φ t hR ht _ ih =>
    obtain rfl : R = Semiformula.Operator.LT.lt := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    have key (v : Fin k → TallyNumber V) :
        (∃¹[(Semiformula.Operator.LT.lt).operator ![#0, Rew.bShift t]] φ).Eval v f ↔
          ∃ x : TallyNumber V, x < t.val v f ∧ φ.Eval (x :> v) f := by
      simp [Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, Semiterm.val_bShift']
    obtain ⟨G, hG, HG⟩ := exists_termGraph t f
    obtain ⟨Q, hQ, HQ⟩ := ih
    refine ⟨fun w ↦ ∃ b, G (b :> w) ∧ ∃ x, Q (x :> fun i ↦ w i) ∧ IsSubstring x b ∧ x ≠ b,
      (PrenexDefinable.exs_Sigma1 <| PrenexDefinable.and_Sigma1 hG <|
        PrenexDefinable.exs_Sigma1 <| (hQ.retraction (0 :> fun i ↦ i.succ.succ)).and_delta0 <|
          (definable_isSubstring_term #0 #1).and (definable_eq_term #0 #1).not_zero).of_iff
        fun w ↦ by simp [Matrix.fun_vecCons_apply], fun v ↦ ?_⟩
    rw [key]
    constructor
    · rintro ⟨b, hb, x, hx, hxb, hne⟩
      obtain rfl := (HG v b).mp hb
      obtain ⟨tx, hlt⟩ := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mp ⟨hxb, hne⟩
      refine ⟨⟨x, tx⟩, hlt, (HQ (⟨x, tx⟩ :> v)).mp ?_⟩
      exact cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val _ v).symm) hx
    · rintro ⟨x, hx, h⟩
      have hx' := (TCISigma.isSubstring_and_ne_iff (t.val v f).2).mpr ⟨x.2, hx⟩
      exact ⟨_, (HG v _).mpr rfl, x.1,
        cast (congrArg Q (Matrix.fun_vecCons_apply Subtype.val x v)) ((HQ (x :> v)).mpr h),
        hx'.1, hx'.2⟩

/--
A prenex arithmetic formula of the level `s + 1` has a prenex definition of the same class and level
on the tallies.
- [HH14, Question 3]
-/
lemma exists_prenexDefinable_of_prenex (Γ : Polarity) (s : ℕ)
    (φ : ℬ[<, ℒₒᵣ].Prenex Γ (s + 1) ξ k) (f : ξ → TallyNumber V) :
    ∃ Q : (Fin k → V) → Prop, PrenexDefinable ℬₛ Γ (s + 1) Q ∧
      ∀ v : Fin k → TallyNumber V, (Q fun i ↦ (v i).1) ↔ φ.val.Eval v f := by
  have : Nonempty V := ⟨∅⟩
  have hT : 𝚺-[ℬₛ, 0].Definable fun w : Fin (k + 1) → V ↦ IsTally 1 (w 0) :=
    isTally_one_definable.retraction ![0]
  have hcons (x : TallyNumber V) (v : Fin k → TallyNumber V) :
      (fun i ↦ ((x :> v) i).1) = x.1 :> fun i ↦ (v i).1 :=
    Matrix.fun_vecCons_apply Subtype.val x v
  induction s generalizing k Γ with
  | zero =>
    rcases Γ
    · have hθ : ℬ[<, ℒₒᵣ].Closure φ.sigmaInv.val :=
        Hierarchy.zero_iff_bounded.mp φ.sigmaInv.val_hierarchy
      obtain ⟨Q, hQ, HQ⟩ := exists_prenexDefinable_of_closure hθ f
      refine ⟨fun w ↦ ∃ x, Q (x :> w) ∧ IsTally 1 x,
        PrenexDefinable.exs_Sigma1 (hQ.and_delta0 hT), fun v ↦ ?_⟩
      rw [φ.models_sigmaInv, TallyNumber.exists_iff]
      refine exists_congr fun x ↦ ⟨fun ⟨h, hx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, h⟩ ↦ ⟨?_, hx⟩⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) h)
      · exact cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr h)
    · have hθ : ℬ[<, ℒₒᵣ].Closure (∼φ.piInv.val) :=
        (Hierarchy.zero_iff_bounded.mp φ.piInv.val_hierarchy).neg
      obtain ⟨Q, hQ, HQ⟩ := exists_prenexDefinable_of_closure hθ f
      refine ⟨fun w ↦ ∀ x, ¬Q (x :> w) ∨ ¬IsTally 1 x,
        PrenexDefinable.all_Pi1 (hQ.not.or_delta0 hT.not_zero), fun v ↦ ?_⟩
      rw [φ.models_piInv, TallyNumber.forall_iff]
      refine forall_congr' fun x ↦ ⟨fun h hx ↦ ?_, fun h ↦ ?_⟩
      · have := (h.resolve_right (not_not.mpr hx))
        rw [← hcons ⟨x, hx⟩ v, HQ] at this
        simpa using this
      · by_cases hx : IsTally 1 x
        · left
          rw [← hcons ⟨x, hx⟩ v, HQ]
          simpa using h hx
        · exact .inr hx
  | succ s ih =>
    rcases Γ
    · obtain ⟨Q, hQ, HQ⟩ := ih 𝚷 φ.sigmaInv (isTally_one_definable.retraction ![0])
        fun x v ↦ Matrix.fun_vecCons_apply _ x v
      refine ⟨fun w ↦ ∃ x, Q (x :> w) ∧ IsTally 1 x, PrenexDefinable.exs (hQ.and_delta0 hT),
        fun v ↦ ?_⟩
      rw [φ.models_sigmaInv, TallyNumber.exists_iff]
      refine exists_congr fun x ↦ ⟨fun ⟨h, hx⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, h⟩ ↦ ⟨?_, hx⟩⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) h)
      · exact cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr h)
    · obtain ⟨Q, hQ, HQ⟩ := ih 𝚺 φ.piInv (isTally_one_definable.retraction ![0])
        fun x v ↦ Matrix.fun_vecCons_apply _ x v
      refine ⟨fun w ↦ ∀ x, Q (x :> w) ∨ ¬IsTally 1 x,
        PrenexDefinable.all (hQ.or_delta0 hT.not_zero), fun v ↦ ?_⟩
      rw [φ.models_piInv, TallyNumber.forall_iff]
      refine forall_congr' fun x ↦ ⟨fun h hx ↦ ?_, fun h ↦ ?_⟩
      · exact (HQ (⟨x, hx⟩ :> v)).mp
          (cast (congrArg Q (hcons ⟨x, hx⟩ v).symm) (h.resolve_right (not_not.mpr hx)))
      · by_cases hx : IsTally 1 x
        · exact .inl <| cast (congrArg Q (hcons ⟨x, hx⟩ v)) ((HQ (⟨x, hx⟩ :> v)).mpr (h hx))
        · exact .inr hx

end definability

end FFL.FirstOrder.Concatenation

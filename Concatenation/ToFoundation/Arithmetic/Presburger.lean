module

public import Concatenation.ToFoundation.Interpretability.Undecidability
public import Concatenation.ToMathlib.Presburger
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Decidability of Presburger arithmetic

The theory of a structure definable in the integers with addition and order is decidable.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- The axiom of the discretely ordered commutative rings with division by positive elements. -/
def discreteEuclideanRingAxiom : ArithmeticSentence :=
  “(∀ x y z, (x + y) + z = x + (y + z)) ∧ (∀ x y, x + y = y + x) ∧ (∀ x, x + 0 = x) ∧
    (∀ x, ∃ y, x + y = 0) ∧ (∀ x y z, (x * y) * z = x * (y * z)) ∧ (∀ x y, x * y = y * x) ∧
    (∀ x, x * 1 = x) ∧ (∀ x y z, x * (y + z) = x * y + x * z) ∧ (∀ x, ¬x < x) ∧
    (∀ x y z, x < y → y < z → x < z) ∧ (∀ x y, x < y ∨ x = y ∨ y < x) ∧
    (∀ x y z, x < y → x + z < y + z) ∧ (∀ x y, 0 < x → 0 < y → 0 < x * y) ∧ 0 < 1 ∧
    (∀ x, 0 < x → ¬x < 1) ∧ (∀ n x, 0 < n → ∃ q r, x = n * q + r ∧ ¬r < 0 ∧ r < n)”

/-- The theory of the discretely ordered commutative rings with division by positive elements. -/
abbrev DiscreteEuclideanRing : ArithmeticTheory := insert discreteEuclideanRingAxiom (𝗘𝗤 ℒₒᵣ)

instance : ℤ↓[ℒₒᵣ] ⊧* DiscreteEuclideanRing := ⟨by
  rintro σ (rfl | h)
  · suffices (∀ x y z : ℤ, x + y + z = x + (y + z)) ∧ (∀ x y : ℤ, x + y = y + x) ∧
        (∀ x : ℤ, ∃ y, x + y = 0) ∧ (∀ x y z : ℤ, x * y * z = x * (y * z)) ∧
        (∀ x y : ℤ, x * y = y * x) ∧ (∀ x y z : ℤ, x * (y + z) = x * y + x * z) ∧
        (∀ x y z : ℤ, x < y → y < z → x < z) ∧ (∀ x y : ℤ, x < y ∨ x = y ∨ y < x) ∧
        (∀ x y : ℤ, 0 < x → 0 < y → 0 < x * y) ∧ (∀ x : ℤ, 0 < x → 1 ≤ x) ∧
        ∀ n x : ℤ, 0 < n → ∃ q r, x = n * q + r ∧ 0 ≤ r ∧ r < n by
      simpa [models_iff, discreteEuclideanRingAxiom] using this
    exact ⟨add_assoc, add_comm, fun x ↦ ⟨-x, add_neg_cancel x⟩, mul_assoc, mul_comm, mul_add,
      fun _ _ _ ↦ lt_trans, lt_trichotomy, fun _ _ ↦ mul_pos, fun _ h ↦ h,
      fun n x hn ↦ ⟨x / n, x % n, (Int.mul_ediv_add_emod x n).symm,
        Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩⟩
  · have : ℤ↓[ℒₒᵣ] ⊧* 𝗘𝗤 ℒₒᵣ := inferInstance
    exact models_theory_iff.mp this _ h⟩

open Classical in
/-- A sentence true in the Presburger rings that are models of a theory is provable in it. -/
lemma DiscreteEuclideanRing.provable_of_presburgerRing {T : ArithmeticTheory}
    (hT : DiscreteEuclideanRing ⊆ T) (σ : ArithmeticSentence)
    (H : ∀ (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [PresburgerRing R],
      R↓[ℒₒᵣ] ⊧* T → R↓[ℒₒᵣ] ⊧ σ) : T ⊢ σ := by
  have : 𝗘𝗤 ℒₒᵣ ⪯ T :=
    Entailment.WeakerThan.ofSubset fun φ hφ ↦ hT <| Set.mem_insert_of_mem _ hφ
  apply Arithmetic.complete T σ fun (M : Type) inst hM ↦ ?_
  have h : (∀ x y z : M, x + y + z = x + (y + z)) ∧ (∀ x y : M, x + y = y + x) ∧
      (∀ x : M, x + 0 = x) ∧ (∀ x : M, ∃ y, x + y = 0) ∧
      (∀ x y z : M, x * y * z = x * (y * z)) ∧ (∀ x y : M, x * y = y * x) ∧
      (∀ x : M, x * 1 = x) ∧ (∀ x y z : M, x * (y + z) = x * y + x * z) ∧ (∀ x : M, ¬x < x) ∧
      (∀ x y z : M, x < y → y < z → x < z) ∧ (∀ x y : M, x < y ∨ x = y ∨ y < x) ∧
      (∀ x y z : M, x < y → x + z < y + z) ∧ (∀ x y : M, 0 < x → 0 < y → 0 < x * y) ∧
      (0 : M) < 1 ∧ (∀ x : M, 0 < x → ¬x < 1) ∧
      ∀ n x : M, 0 < n → ∃ q r, x = n * q + r ∧ ¬r < 0 ∧ r < n := by
    simpa [models_iff, discreteEuclideanRingAxiom] using
      Theory.models M T (hT <| Set.mem_insert _ _)
  obtain ⟨add_assoc', add_comm', add_zero', hneg, mul_assoc', mul_comm', mul_one', distr, irr,
    trans, tri, add_lt, mul_pos', zero_lt_one', discrete, euclid⟩ := h
  let : Neg M := ⟨fun x ↦ Classical.choose (hneg x)⟩
  have neg_spec : ∀ x : M, x + -x = 0 := fun x ↦ Classical.choose_spec (hneg x)
  let : CommRing M := CommRing.ofMinimalAxioms add_assoc' (fun x ↦ by rw [add_comm', add_zero'])
    (fun x ↦ by rw [add_comm', neg_spec]) mul_assoc' mul_comm'
    (fun x ↦ by rw [mul_comm', mul_one']) distr
  have : IsStrictTotalOrder M (· < ·) :=
    { irrefl := irr, trans := trans,
      trichotomous := fun a b h₁ h₂ ↦ ((tri a b).resolve_left h₁).resolve_right h₂ }
  let : LinearOrder M := linearOrderOfSTO (· < ·)
  have : IsOrderedAddMonoid M :=
    { add_le_add_left := fun a b h c ↦ by
        rcases h with rfl | h
        · exact le_rfl
        · exact (add_lt a b c h).le }
  have : ZeroLEOneClass M := ⟨zero_lt_one'.le⟩
  have : Nontrivial M := ⟨⟨0, 1, zero_lt_one'.ne⟩⟩
  have : IsStrictOrderedRing M := IsStrictOrderedRing.of_mul_pos mul_pos'
  have : PresburgerRing M := PresburgerRing.of_forall_exists
    (fun x hx ↦ not_lt.mp (discrete x hx)) fun n x hn ↦ by
      obtain ⟨q, r, e, h0, hr⟩ := euclid n x hn
      exact ⟨q, r, e, not_lt.mp h0, hr⟩
  exact H M hM

end FFL.FirstOrder

open FFL FirstOrder

namespace Presburger

section

variable {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {v : Fin n → R}

omit [IsStrictOrderedRing R] in
lemma numeral_eq_natCast (k : ℕ) : (ORingStructure.numeral k : R) = k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      simp only [ORingStructure.numeral, ih (k + 1) (by omega)]
      push_cast
      ring

/-- The term `c 0 * #0 + ⋯ + c (n - 1) * #(n - 1) + k`. -/
def natTerm (c : Fin n → ℕ) (k : ℕ) : ClosedSemiterm ℒₒᵣ n :=
  (List.finRange n).foldr
    (fun i s ↦ ‘!!((Semiterm.Operator.numeral ℒₒᵣ (c i)).const) * #i + !!s’)
    (Semiterm.Operator.numeral ℒₒᵣ k).const

omit [IsStrictOrderedRing R] in
lemma valb_natTerm (c : Fin n → ℕ) (k : ℕ) :
    (natTerm c k).valb v = ∑ i, (c i : R) * v i + k := by
  have : ∀ l : List (Fin n), (l.foldr
      (fun i s ↦ ‘!!((Semiterm.Operator.numeral ℒₒᵣ (c i)).const) * #i + !!s’)
      (Semiterm.Operator.numeral ℒₒᵣ k).const : ClosedSemiterm ℒₒᵣ n).valb v =
        (l.map fun i ↦ (c i : R) * v i).sum + k := by
    intro l
    induction l with
    | nil => simp [numeral_eq_natCast]
    | cons i l ih => simp [ih, numeral_eq_natCast, add_assoc]
  rw [natTerm, this, Fin.sum_univ_def]

end

end Presburger

namespace Presburger.LinearTerm

variable {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {v : Fin n → R}

/-- The positive part of a linear term, as a term of arithmetic. -/
def posTerm (t : LinearTerm n) : ClosedSemiterm ℒₒᵣ n :=
  natTerm (fun i ↦ (t.coeff i).toNat) t.const.toNat

/-- The negative part of a linear term, as a term of arithmetic. -/
def negTerm (t : LinearTerm n) : ClosedSemiterm ℒₒᵣ n :=
  natTerm (fun i ↦ (-t.coeff i).toNat) (-t.const).toNat

omit [IsStrictOrderedRing R] in
lemma valb_posTerm_sub_valb_negTerm (t : LinearTerm n) :
    t.posTerm.valb v - t.negTerm.valb v = t.eval v := by
  have e (z : ℤ) : ((z.toNat : ℕ) : R) - ((-z).toNat : ℕ) = z := by
    rw [← Int.cast_natCast, ← Int.cast_natCast (R := R), ← Int.cast_sub, Int.toNat_sub_toNat_neg]
  simp only [posTerm, negTerm, valb_natTerm, eval]
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, e]
  simp [← sub_mul, e]

end Presburger.LinearTerm

namespace Presburger.Formula

variable {n : ℕ} {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {v : Fin n → R}

/-- A formula as a formula of arithmetic. -/
def toSemisentence : Presburger.Formula n → ArithmeticSemisentence n
  | verum => ⊤
  | falsum => ⊥
  | pos t => “!!t.negTerm < !!t.posTerm”
  | dvd true m t => “∃ q, !!(Rew.bShift t.posTerm) =
      !!((Semiterm.Operator.numeral ℒₒᵣ m).const) * q + !!(Rew.bShift t.negTerm)”
  | dvd false m t => “¬∃ q, !!(Rew.bShift t.posTerm) =
      !!((Semiterm.Operator.numeral ℒₒᵣ m).const) * q + !!(Rew.bShift t.negTerm)”
  | and φ ψ => φ.toSemisentence ⋏ ψ.toSemisentence
  | or φ ψ => φ.toSemisentence ⋎ ψ.toSemisentence

@[simp]
lemma evalb_toSemisentence (φ : Presburger.Formula n) : R ⊧/v φ.toSemisentence ↔ φ.eval v := by
  induction φ with
  | verum => simp [toSemisentence]
  | falsum => simp [toSemisentence]
  | pos t => simp [toSemisentence, ← t.valb_posTerm_sub_valb_negTerm]
  | dvd b m t =>
    have e : ((m : ℕ) : R) ∣ t.eval v ↔
        ∃ q : R, t.posTerm.valb v = (m : ℕ) * q + t.negTerm.valb v := by
      rw [← t.valb_posTerm_sub_valb_negTerm]
      exact exists_congr fun q ↦ sub_eq_iff_eq_add
    cases b <;> simp [toSemisentence, e, numeral_eq_natCast]
  | and φ ψ ihφ ihψ => simp [toSemisentence, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [toSemisentence, ihφ, ihψ]

end Presburger.Formula

namespace FFL.FirstOrder

/--
A definition of a structure for the language `L` in a Presburger ring: its domain, the graphs of
its functions, whose first variable is the value, and its relations.
-/
structure PresburgerDefinition (L : Language) where
  /-- The domain. -/
  domain : Presburger.Formula 1
  /-- The graph of a function symbol; the first variable is the value. -/
  func {k : ℕ} : L.Func k → Presburger.Formula (k + 1)
  /-- The interpretation of a relation symbol. -/
  rel {k : ℕ} : L.Rel k → Presburger.Formula k

namespace PresburgerDefinition

open Presburger

variable {L : Language} (Δ : PresburgerDefinition L) {n k : ℕ}

/-- The map `ι` identifies the structure `M` with the structure that `Δ` defines in `R`. -/
structure Defines {R M : Type*} [CommRing R] [LinearOrder R] [Tarski.Structure L M] (ι : M → R) :
    Prop where
  injective : Function.Injective ι
  domain_iff (z : R) : Δ.domain.eval ![z] ↔ ∃ x, ι x = z
  func_iff {k : ℕ} (f : L.Func k) (v : Fin k → M) (y : M) :
    (Δ.func f).eval (ι y :> ι ∘ v) ↔ Tarski.Structure.func f v = y
  rel_iff {k : ℕ} (r : L.Rel k) (v : Fin k → M) :
    (Δ.rel r).eval (ι ∘ v) ↔ Tarski.Structure.rel r v

/-- The first `k` variables are in the domain and satisfy the formulas `G`. -/
def args (G : Fin k → Presburger.Formula (n + 1)) : Presburger.Formula (k + n) :=
  .conj <| List.ofFn fun i ↦ .and (Δ.domain.rename ![Fin.castAdd n i])
    ((G i).rename (Fin.cases (Fin.castAdd n i) (Fin.natAdd k)))

/-- The graph of a term; the first variable is the value. -/
def termGraph : ClosedSemiterm L n → Presburger.Formula (n + 1)
  | #x => .eq (.var 0) (.var x.succ)
  | &x => x.elim
  | .func (arity := k) f v =>
    .exsN k <| .and
      (Δ.args fun i ↦ (termGraph (v i)).rename (Fin.cases 0 fun j ↦ j.succ.succ))
      ((Δ.func f).rename (Fin.cases (Fin.natAdd k 0) (Fin.castAdd (n + 1))))

/-- The relation `r` holds of the terms `v`. -/
def relGraph (r : L.Rel k) (v : Fin k → ClosedSemiterm L n) : Presburger.Formula n :=
  .exsN k <| .and (Δ.args fun i ↦ Δ.termGraph (v i)) ((Δ.rel r).rename (Fin.castAdd n))

/-- The translation of a formula of `L`. -/
def translate : {n : ℕ} → Semisentence L n → Presburger.Formula n
  | _, .rel r v => Δ.relGraph r v
  | _, .nrel r v => (Δ.relGraph r v).neg
  | _, ⊤ => .verum
  | _, ⊥ => .falsum
  | _, φ ⋏ ψ => .and (translate φ) (translate ψ)
  | _, φ ⋎ ψ => .or (translate φ) (translate ψ)
  | _, ∀¹ φ => .all <| .or (Δ.domain.rename ![0]).neg (translate φ)
  | _, ∃¹ φ => .elim <| .and (Δ.domain.rename ![0]) (translate φ)

section

variable {R M : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [PresburgerRing R]
  [Tarski.Structure L M] {ι : M → R} {Δ}

omit [IsStrictOrderedRing R] [PresburgerRing R] [Tarski.Structure L M] in
lemma eval_args (G : Fin k → Presburger.Formula (n + 1)) (w : Fin k → R) (z : Fin n → R) :
    (Δ.args G).eval (Fin.append w z) ↔ ∀ i, Δ.domain.eval ![w i] ∧ (G i).eval (w i :> z) := by
  have e₁ (i : Fin k) : Fin.append w z ∘ ![Fin.castAdd n i] = ![w i] := by
    funext j
    simp
  have e₂ (i : Fin k) :
      Fin.append w z ∘ Fin.cases (Fin.castAdd n i) (Fin.natAdd k) = w i :> z := by
    funext j
    cases j using Fin.cases <;> simp
  simp [args, e₁, e₂]

variable (h : Δ.Defines ι)

include h

lemma Defines.eval_termGraph (t : ClosedSemiterm L n) (e : Fin n → M) (y : M) :
    (Δ.termGraph t).eval (ι y :> ι ∘ e) ↔ t.valb e = y := by
  induction t generalizing y with
  | bvar x => simp [termGraph, h.injective.eq_iff, eq_comm]
  | fvar x => exact x.elim
  | @func k f v ih =>
    have e₁ (w : R) :
        (w :> ι y :> ι ∘ e) ∘ (Fin.cases 0 fun j ↦ j.succ.succ) = w :> ι ∘ e := by
      funext j
      cases j using Fin.cases <;> simp
    have e₂ (w : Fin k → R) : Fin.append w (ι y :> ι ∘ e) ∘
        Fin.cases (Fin.natAdd k 0) (Fin.castAdd (n + 1)) = ι y :> w := by
      funext j
      cases j using Fin.cases <;> simp
    simp only [termGraph, Formula.eval_exsN, Formula.eval, eval_args, Formula.eval_rename, e₁, e₂]
    constructor
    · rintro ⟨w, hw, hf⟩
      have : w = ι ∘ fun i ↦ (v i).valb e := by
        funext i
        obtain ⟨x, hx⟩ := (h.domain_iff _).mp (hw i).1
        have := (hw i).2
        rw [← hx, ih] at this
        rw [← hx, Function.comp_apply, this]
      rw [this, h.func_iff] at hf
      exact hf
    · intro hf
      use ι ∘ fun i ↦ (v i).valb e
      and_intros
      · intro i
        exact ⟨(h.domain_iff _).mpr ⟨_, rfl⟩, (ih i _).mpr rfl⟩
      · exact (h.func_iff _ _ _).mpr hf

lemma Defines.eval_relGraph (r : L.Rel k) (v : Fin k → ClosedSemiterm L n) (e : Fin n → M) :
    (Δ.relGraph r v).eval (ι ∘ e) ↔ Tarski.Structure.rel r fun i ↦ (v i).valb e := by
  have e₁ (w : Fin k → R) : Fin.append w (ι ∘ e) ∘ Fin.castAdd n = w := by
    funext j
    simp
  simp only [relGraph, Formula.eval_exsN, Formula.eval, eval_args, Formula.eval_rename, e₁]
  constructor
  · rintro ⟨w, hw, hr⟩
    have : w = ι ∘ fun i ↦ (v i).valb e := by
      funext i
      obtain ⟨x, hx⟩ := (h.domain_iff _).mp (hw i).1
      have := (hw i).2
      rw [← hx, h.eval_termGraph] at this
      rw [← hx, Function.comp_apply, this]
    rw [this, h.rel_iff] at hr
    exact hr
  · intro hr
    use ι ∘ fun i ↦ (v i).valb e
    and_intros
    · intro i
      exact ⟨(h.domain_iff _).mpr ⟨_, rfl⟩, (h.eval_termGraph _ _ _).mpr rfl⟩
    · exact (h.rel_iff _ _).mpr hr

lemma Defines.eval_translate (φ : Semisentence L n) (e : Fin n → M) :
    (Δ.translate φ).eval (ι ∘ e) ↔ M ⊧/e φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp [translate]
  | hfalsum => simp [translate]
  | hrel r v => exact h.eval_relGraph r v e
  | hnrel r v => exact (Formula.eval_neg _).trans <| not_congr <| h.eval_relGraph r v e
  | hand φ ψ ihφ ihψ => simp [translate, ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [translate, ihφ, ihψ]
  | hall φ ih =>
    have e₁ (x : R) : (x :> ι ∘ e) ∘ ![0] = ![x] := by
      funext j
      simp
    simp only [translate, Formula.eval_all, Formula.eval, Formula.eval_neg, Formula.eval_rename,
      e₁, h.domain_iff, Semiformula.eval_all]
    constructor
    · intro H x
      have := (H (ι x)).resolve_left (not_not.mpr ⟨x, rfl⟩)
      rwa [← Matrix.comp_vecCons'', ih] at this
    · intro H z
      by_cases hz : ∃ x, ι x = z
      · obtain ⟨x, rfl⟩ := hz
        right
        rw [← Matrix.comp_vecCons'', ih]
        exact H x
      · exact .inl hz
  | hexs φ ih =>
    have e₁ (x : R) : (x :> ι ∘ e) ∘ ![0] = ![x] := by
      funext j
      simp
    simp only [translate, Formula.eval_elim, Formula.eval, Formula.eval_rename, e₁, h.domain_iff,
      Semiformula.eval_ex]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, H⟩
      rw [← Matrix.comp_vecCons'', ih] at H
      exact ⟨x, H⟩
    · rintro ⟨x, H⟩
      use ι x
      and_intros
      · exact ⟨x, rfl⟩
      · rwa [← Matrix.comp_vecCons'', ih]

/-- Two structures with the same definition in Presburger rings satisfy the same sentences. -/
theorem Defines.models_iff [Nonempty M] {R' M' : Type} [CommRing R'] [LinearOrder R']
    [IsStrictOrderedRing R'] [PresburgerRing R'] [Nonempty M'] [Tarski.Structure L M']
    {ι' : M' → R'} (h' : Δ.Defines ι') (σ : Sentence L) : M↓[L] ⊧ σ ↔ M'↓[L] ⊧ σ := by
  rw [FirstOrder.models_iff, FirstOrder.models_iff, ← h.eval_translate, ← h'.eval_translate,
    Formula.eval_iff_eval_int _ _ ![], Formula.eval_iff_eval_int _ (ι' ∘ ![]) ![]]

end

section

variable [L.Eq]

/-- The domain as a formula of arithmetic. -/
def domainOperator : Semiformula.Operator ℒₒᵣ 1 := ⟨Δ.domain.toSemisentence⟩

/-- The graph of a function symbol as a formula of arithmetic. -/
def funcOperator (f : L.Func k) : Semiformula.Operator ℒₒᵣ (k + 1) :=
  ⟨(Δ.func f).toSemisentence⟩

/-- The interpretation of a relation symbol as a formula of arithmetic. -/
def relOperator (r : L.Rel k) : Semiformula.Operator ℒₒᵣ k := ⟨(Δ.rel r).toSemisentence⟩

/-- The domain is not empty. -/
def domainNonempty : ArithmeticSentence := “∃ x, %(Δ.domainOperator) x”

/-- The graph of a function symbol is that of a function on the domain. -/
def funcDefined (f : L.Func k) : ArithmeticSentence :=
  ∀¹* “(⋀ i, %(Δ.domainOperator) #(i : Fin k)) →
    ∃! y, %(Δ.domainOperator) y ∧ %(Δ.funcOperator f) y ⋯”

/-- The interpretation of the equality is the equality on the domain. -/
def preserveEq : ArithmeticSentence :=
  “∀ x y, %(Δ.domainOperator) x → %(Δ.domainOperator) y →
    (%(Δ.relOperator Language.Eq.eq) x y ↔ x = y)”

/--
The theory of the discretely ordered commutative rings with division by positive elements in
which `Δ` defines a structure for `L`.
-/
def theory : ArithmeticTheory :=
  DiscreteEuclideanRing ∪
    ({Δ.domainNonempty, Δ.preserveEq} ∪ Set.range fun f : (k : ℕ) × L.Func k ↦ Δ.funcDefined f.2)

lemma theory_finite [L.Finite] : Δ.theory.Finite := by
  have : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  exact (Theory.Eq.finite.insert _).union <|
    ((Set.finite_singleton _).insert _).union <| Set.finite_range _

noncomputable instance [L.Finite] : Δ.theory.Δ₁ := Theory.Δ₁.ofFinite _ Δ.theory_finite

instance : 𝗘𝗤 ℒₒᵣ ⪯ Δ.theory :=
  Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl <| Set.mem_insert_of_mem _ h

/-- The translation of `L` into arithmetic that `Δ` gives. -/
def translation : DirectTranslation Δ.theory L where
  domain := Δ.domainOperator
  rel := Δ.relOperator
  func := Δ.funcOperator
  domain_nonempty := Entailment.by_axm <| Or.inr <| Or.inl <| Or.inl rfl
  func_defined f := Entailment.by_axm <| Or.inr <| Or.inr ⟨⟨_, f⟩, rfl⟩
  preserve_eq := Entailment.by_axm <| Or.inr <| Or.inl <| Or.inr rfl

variable {Δ}

/-- A ring in which `Δ` defines a structure is a model of the theory of such rings. -/
lemma Defines.models_theory {M : Type} [Nonempty M] [Tarski.Structure L M]
    [Tarski.Structure.Eq L M] {ι : M → ℤ} (h : Δ.Defines ι) : ℤ↓[ℒₒᵣ] ⊧* Δ.theory := ⟨by
  rintro σ (hσ | (rfl | rfl) | ⟨⟨k, f⟩, rfl⟩)
  · exact Theory.models ℤ DiscreteEuclideanRing hσ
  · apply (DirectTranslation.models_domainNonempty_iff _).mpr
    obtain ⟨x⟩ := ‹Nonempty M›
    use ι x
    simpa [domainOperator, Semiformula.Operator.val] using (h.domain_iff _).mpr ⟨x, rfl⟩
  · apply (DirectTranslation.models_preserveEq_iff _ _).mpr
    intro x y hx hy
    obtain ⟨a, rfl⟩ := (h.domain_iff x).mp <| by
      simpa [domainOperator, Semiformula.Operator.val] using hx
    obtain ⟨b, rfl⟩ := (h.domain_iff y).mp <| by
      simpa [domainOperator, Semiformula.Operator.val] using hy
    have := h.rel_iff Language.Eq.eq ![a, b]
    simp only [Matrix.comp_vecCons'', Tarski.Structure.eq_lang] at this
    simpa [relOperator, Semiformula.Operator.val, h.injective.eq_iff] using this
  · apply (DirectTranslation.models_funcDefined_iff _ _).mpr
    intro e he
    have he' : ∀ i, ∃ x, ι x = e i := fun i ↦ (h.domain_iff _).mp <| by
      simpa [domainOperator, Semiformula.Operator.val] using he i
    choose v hv using he'
    obtain rfl : ι ∘ v = e := funext hv
    use ι (Tarski.Structure.func f v)
    and_intros
    · simpa [domainOperator, Semiformula.Operator.val] using (h.domain_iff _).mpr ⟨_, rfl⟩
    · simpa [funcOperator, Semiformula.Operator.val] using (h.func_iff f v _).mpr rfl
    · rintro y ⟨hy, hf⟩
      obtain ⟨b, rfl⟩ := (h.domain_iff y).mp <| by
        simpa [domainOperator, Semiformula.Operator.val] using hy
      rw [(h.func_iff f v b).mp <| by simpa [funcOperator, Semiformula.Operator.val] using hf]⟩

variable (Δ) in
/-- In a model of `Δ.theory`, the formulas of `Δ` define the model of its translation. -/
lemma defines_model (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [R↓[ℒₒᵣ] ⊧* Δ.theory] : Δ.Defines fun x : Δ.translation.Model R ↦ (x : R) where
  injective _ _ h := DirectTranslation.Model.ext h
  domain_iff z := by
    constructor
    · intro hz
      exact ⟨⟨z, by simpa [DirectTranslation.Dom, translation, domainOperator,
        Semiformula.Operator.val] using hz⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      simpa [DirectTranslation.Dom, translation, domainOperator, Semiformula.Operator.val] using
        x.dom
  func_iff f v y := by
    rw [eq_comm, DirectTranslation.Model.func_iff]
    exact (Formula.evalb_toSemisentence (Δ.func f)).symm
  rel_iff r v := by
    rw [DirectTranslation.Model.rel_iff]
    exact (Formula.evalb_toSemisentence (Δ.rel r)).symm

variable {M : Type} [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M] {ι : M → ℤ}
  (h : Δ.Defines ι)

include h

/-- The theory of a structure defined in the integers is interpreted by its definition. -/
abbrev Defines.interpretation : Δ.theory ⊳ Tarski.Structure.theory L M where
  trln := Δ.translation
  interpret_theory σ hσ := by
    apply DiscreteEuclideanRing.provable_of_presburgerRing fun _ h ↦ Or.inl h
    intro R _ _ _ _ hR
    exact DirectTranslation.Model.translate_iff.mpr <| ((Δ.defines_model R).models_iff h σ).mpr hσ

/--
The theory of a structure for a finite language that is definable in the integers with addition
and order is decidable.
-/
theorem Defines.decidable [L.Encodable] [L.Primcodable] [L.LORDefinable] [L.Finite] :
    Entailment.Decidable (Tarski.Structure.theory L M) :=
  have := h.models_theory
  have : Entailment.Consistent Δ.theory := consistent_of_model Δ.theory ℤ
  have : Entailment.Complete (Tarski.Structure.theory L M) := ⟨fun σ ↦ by
    by_cases hσ : M↓[L] ⊧ σ
    · exact .inl <| Entailment.by_axm hσ
    · exact .inr <| Entailment.by_axm <| by simpa [models_iff] using hσ⟩
  DirectInterpretation.decidable_of_complete h.interpretation

end

end PresburgerDefinition

end FFL.FirstOrder

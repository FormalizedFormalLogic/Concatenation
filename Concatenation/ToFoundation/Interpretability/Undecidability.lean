module

public import AlphaCentauri.Bootstrapping.Interpretability.Translation
public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Undecidability and direct interpretations

A direct translation of a finite language is computable on sentences, so that undecidability and
essential undecidability transfer along direct interpretations.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder

namespace Arithmetic.Bootstrapping

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ι : ℕ → Type*}
  [∀ k, Encodable (ι k)] [Finite ((k : ℕ) × ι k)]

lemma exists_nth_pair_encode_eq (g : (k : ℕ) → ι k → V) :
    ∃ w : V, ∀ k (i : ι k), w.[⟪(k : V), (Encodable.encode i : V)⟫] = g k i := by
  let c : (k : ℕ) × ι k → ℕ := fun x ↦ Nat.pair x.1 (Encodable.encode x.2)
  have hc : Function.Injective c := by
    rintro ⟨k, i⟩ ⟨l, j⟩ h
    obtain ⟨rfl, h⟩ := Nat.pair_eq_pair.mp h
    simpa using h
  obtain ⟨N, hN⟩ := (Set.finite_range c).bddAbove
  let u : Fin (N + 1) → V := fun j ↦ Function.extend c (fun x ↦ g x.1 x.2) 0 j
  use matrixToVec u
  intro k i
  have h : c ⟨k, i⟩ < N + 1 := Nat.lt_succ_of_le <| hN <| Set.mem_range_self _
  rw [← coe_pair_eq_pair_coe]
  exact (matrixToVec_nth u ⟨c ⟨k, i⟩, h⟩).trans <| hc.extend_apply (fun x ↦ g x.1 x.2) 0 ⟨k, i⟩

end

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L₁ L₂ : Language} [L₁.Encodable]
  [L₁.LORDefinable] [L₁.Eq] [L₂.Encodable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

lemma exists_isTableOf (π : DirectTranslation T L₂) : ∃ tbl : V, IsTableOf π tbl := by
  have : Fintype ((k : ℕ) × L₂.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L₂.Rel k) := Language.Finite.rel
  obtain ⟨r, hr⟩ := exists_nth_pair_encode_eq fun k (R : L₂.Rel k) ↦ (⌜(π.rel R).sentence⌝ : V)
  obtain ⟨f, hf⟩ := exists_nth_pair_encode_eq fun k (f : L₂.Func k) ↦ (⌜(π.func f).sentence⌝ : V)
  have h₁ : (?[⌜π.domain.sentence⌝, r, f] : V).[1] = r := by simp
  have h₂ : (?[⌜π.domain.sentence⌝, r, f] : V).[2] = f := by simp [← one_add_one_eq_two]
  use ?[⌜π.domain.sentence⌝, r, f]
  constructor
  · simp [tableDomain]
  · intro k R
    rw [tableRel, h₁]
    exact hr k R
  · intro k F
    rw [tableFunc, h₂]
    exact hf k F

end Arithmetic.Bootstrapping

namespace DirectTranslation

open Arithmetic Arithmetic.Bootstrapping

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.Primcodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.Primcodable] [L₂.LORDefinable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/-- Every direct translation of a finite language is computable on semisentences. -/
theorem computable_translate (π : DirectTranslation T L₂) {n : ℕ} :
    Computable fun σ : Semisentence L₂ n ↦ (π.translate σ : Semisentence L₁ n) := by
  obtain ⟨tbl, h⟩ := exists_isTableOf (V := ℕ) π
  apply computable_iff_sigma1_simulate (f := Bootstrapping.translate L₁ L₂ tbl) (by definability)
  intro σ
  rw [← Sentence.quote_eq_encode_nat, h.translate_quote_sentence, Sentence.quote_eq_encode_nat]

end DirectTranslation

namespace DirectInterpretation

section pullback

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

/-- The theory of the sentences whose translation `T` proves. -/
def pullback (π : T ⊳ U) : Theory L₂ := {σ | T ⊢ π σ}

variable {π : T ⊳ U} {σ : Sentence L₂}

@[simp]
lemma mem_pullback_iff : σ ∈ π.pullback ↔ T ⊢ π σ := Iff.rfl

variable (π) in
/-- The interpretation of the theory `π.pullback` by the translation of `π`. -/
abbrev interpretPullback : T ⊳ π.pullback where
  trln := π.trln
  interpret_theory _ h := h

lemma provable_pullback_iff : π.pullback ⊢ σ ↔ T ⊢ π σ :=
  ⟨π.interpretPullback.sound, fun h ↦ Entailment.by_axm h⟩

lemma theory_pullback : Theory.theory π.pullback = π.pullback := by
  ext
  simp [provable_pullback_iff]

instance : U ⪯ π.pullback := Entailment.weakerThan_iff.mpr fun h ↦ Entailment.by_axm (π.sound h)

instance [Entailment.Consistent T] : Entailment.Consistent π.pullback :=
  π.interpretPullback.consistent

end pullback

section

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.Primcodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.Primcodable] [L₂.LORDefinable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]
  {U : Theory L₂} (π : T ⊳ U)

lemma undecidable_of_undecidable_pullback (h : Entailment.Undecidable π.pullback) :
    Entailment.Undecidable T := by
  rintro ⟨hT⟩
  apply h
  constructor
  apply ComputablePred.computable_of_manyOneReducible _ hT
  use π.translate, π.trln.computable_translate
  exact fun _ ↦ provable_pullback_iff

include π

/--
A consistent theory directly interpreting an essentially undecidable theory is undecidable.
- [Sve08, §1]
-/
theorem undecidable [U.EssentiallyUndecidable] [Entailment.Consistent T] :
    Entailment.Undecidable T :=
  π.undecidable_of_undecidable_pullback <|
    Theory.EssentiallyUndecidable.undecidable_of_consistent (T := U) _ inferInstance inferInstance

/--
A theory directly interpreting an essentially undecidable theory is essentially undecidable.
- [Sve08, §1]
-/
theorem essentiallyUndecidable [U.EssentiallyUndecidable] : T.EssentiallyUndecidable where
  undecidable_of_consistent T' hT _ :=
    have : 𝗘𝗤 L₁ ⪯ T' := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 L₁ ⪯ T)) hT
    (π.ofWeakerThanLeft (T' := T')).undecidable

end

/--
A theory none of whose finite subsets is essentially undecidable interprets no finitely
axiomatizable essentially undecidable theory.
-/
theorem notInterprets_of_forall_finite_not_essentiallyUndecidable {L₁ L₂ : Language}
    [L₁.Encodable] [L₁.Primcodable] [L₁.LORDefinable] [L₁.Eq] [L₁.Finite] [L₂.Encodable]
    [L₂.Primcodable] [L₂.LORDefinable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]
    {U : Theory L₂} [U.EssentiallyUndecidable] (hU : FiniteAxiomatizable U)
    (h : ∀ F ⊆ T, F.Finite → ¬F.EssentiallyUndecidable) : T ⋫ U :=
  ⟨fun π ↦
    let ⟨F, hF, hfin, _, ⟨ρ⟩⟩ := π.exists_finite_subset hU
    h F hF hfin ρ.essentiallyUndecidable⟩

end DirectInterpretation

end FFL.FirstOrder

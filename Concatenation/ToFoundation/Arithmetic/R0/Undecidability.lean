module

public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Concatenation.ToFoundation.Decidability
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Essential undecidability of $\mathsf{R}_0$

No consistent extension of $\mathsf{R}_0$ has a decidable set of theorems.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open Bootstrapping Bootstrapping.Arithmetic

/--
A consistent extension of $\mathsf{R}_0$ is undecidable.
- [Sve08, §3.3]
- [HH14, §1]
-/
theorem undecidable_of_consistent (T : ArithmeticTheory) [𝗥₀ ⪯ T]
    [Entailment.Consistent T] : Entailment.Undecidable T := by
  rintro ⟨hC⟩
  have hQuoteSubst :
      Computable₂ fun σ π : ArithmeticSemisentence 1 ↦ (σ/[⌜π⌝] : ArithmeticSentence) :=
    computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ)) (by definability)
      fun σ τ ↦ by simp [← Sentence.quote_eq_encode_nat, substNumeral_app_quote]
  have hSubst : Computable fun σ : ArithmeticSemisentence 1 ↦ (σ/[⌜σ⌝] : ArithmeticSentence) :=
    hQuoteSubst.comp Computable.id Computable.id
  have hD : ComputablePred fun σ : ArithmeticSemisentence 1 ↦ T ⊢ σ/[⌜σ⌝] :=
    ComputablePred.computable_of_manyOneReducible (ManyOneReducible.mk (fun σ ↦ T ⊢ σ) hSubst) hC
  let D : ℕ → Prop :=
    fun n ↦ (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      fun σ ↦ T ⊢ σ/[⌜σ⌝]
  obtain ⟨_, hDdec⟩ : ComputablePred D := ComputablePred.iff_decoded_pred.mp hD
  have hγ := cobhamRepresentation_spec
    (Computable.cond hDdec (Computable.const 0) (Computable.const 1))
  generalize cobhamRepresentation _ = γ at hγ
  let δ : ArithmeticSemisentence 1 := “x. ¬!γ x 0”
  have hδ : D (Encodable.encode δ) ↔ T ⊢ δ/[⌜δ⌝] := by simp [D, Encodable.encodek]
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance
  by_cases h : T ⊢ δ/[⌜δ⌝]
  · apply Entailment.Consistent.not_bot (𝓢 := T)
    apply complete.{0} T
    intro M _ _
    have hR0 : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    have h₁ := models_of_provable hR0 (hγ (Encodable.encode δ))
    have h₂ := models_of_provable (M := M) inferInstance h
    simp [hδ.mpr h, models_iff, δ, Arithmetic.gödelNumber'_eq_coe_encode] at h₁ h₂
    simp_all
  · apply h
    apply complete.{0} T
    intro M _ _
    have hR0 : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    have h₁ := models_of_provable hR0 (hγ (Encodable.encode δ))
    simp [hδ.not.mpr h, models_iff] at h₁
    simpa [models_iff, δ, Arithmetic.gödelNumber'_eq_coe_encode, h₁]
      using numeral_ne_numeral_of_ne (M := M) zero_ne_one

/--
$\mathsf{R}_0$ is essentially undecidable.
- [Sve08, §3.3]
- [HH14, §1]
-/
instance : (𝗥₀ : ArithmeticTheory).EssentiallyUndecidable where
  undecidable_of_consistent T _ _ := undecidable_of_consistent T

/--
The theorems of $\mathsf{R}_0$ are not computable.
- [Sve08, §3.3]
-/
theorem undecidable : Entailment.Undecidable 𝗥₀ := Theory.EssentiallyUndecidable.undecidable 𝗥₀

end FFL.FirstOrder.Arithmetic.R0

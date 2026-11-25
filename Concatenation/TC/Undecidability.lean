module

public import Concatenation.Semantics.Standard
public import Concatenation.TC.Representation
public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Concatenation.ToFoundation.Decidability

/-!
# Essential undecidability of $\mathsf{TC}$

No consistent extension of $\mathsf{TC}$ has a decidable set of theorems.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
The theorems of a consistent extension of $\mathsf{TC}$ are not computable.
- [GZ08, Theorem 16]
- [Sve08, §3.3, Theorem 3]
-/
theorem uncomputable_theory_of_consistent (T : ConcatenationTheory) [𝗧𝗖 ⪯ T]
    [Entailment.Consistent T] : ¬ComputablePred (· ∈ T.theory) := by
  intro hC
  let P : Semisentence ℒ⌢ 1 → Prop := fun σ ↦ T ⊢ σ/[numeralTerm (Encodable.encode σ)]
  have hD : ComputablePred P :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun σ ↦ T ⊢ σ) computable_subst_numeralTerm_encode) hC
  let D : ℕ → Prop :=
    fun n ↦ (Encodable.decode (α := Semisentence ℒ⌢ 1) n).elim False P
  obtain ⟨_, hDdec⟩ : ComputablePred D := ComputablePred.iff_decoded_pred.mp hD
  have hf := Computable.cond hDdec (Computable.const 0) (Computable.const 1)
  obtain ⟨γ, hγ⟩ : ∃ γ : Semisentence ℒ⌢ 2, ∀ n, T ⊢ “∀ y, !γ !!(Rew.bShift (numeralTerm n)) y ↔
      y = !!(Rew.bShift (numeralTerm (bif decide (D n) then 0 else 1)))” :=
    ⟨_, fun n ↦ Entailment.WeakerThan.pbl <|
      weakRepresentation_spec (Arithmetic.R0.cobhamRepresentation_spec hf) n⟩
  let δ : Semisentence ℒ⌢ 1 := “x. ¬!γ x !!(Rew.bShift (numeralTerm 0))”
  have hδ : D (Encodable.encode δ) ↔ T ⊢ δ/[numeralTerm (Encodable.encode δ)] := by
    simp [D, P, Encodable.encodek]
  have : 𝗘𝗤 ℒ⌢ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗧𝗖) inferInstance inferInstance
  by_cases h : T ⊢ δ/[numeralTerm (Encodable.encode δ)]
  · apply Entailment.Consistent.not_bot (𝓢 := T)
    apply complete.{0} T
    intro M _ _
    have h₁ := models_of_provable (M := M) inferInstance (hγ (Encodable.encode δ))
    have h₂ := models_of_provable (M := M) inferInstance h
    rw [decide_eq_true (hδ.mpr h), Bool.cond_true] at h₁
    generalize numeralTerm (Encodable.encode δ) = t at h₁ h₂
    simp [models_iff, δ] at h₁ h₂
    simp [h₁] at h₂
  · apply h
    apply complete.{0} T
    intro M _ _
    have hTC : M↓[ℒ⌢] ⊧* 𝗧𝗖 := ModelsTheory.of_provably_subtheory M 𝗧𝗖 T inferInstance
    have h₁ := models_of_provable (M := M) inferInstance (hγ (Encodable.encode δ))
    rw [decide_eq_false (hδ.not.mpr h), Bool.cond_false] at h₁
    generalize numeralTerm (Encodable.encode δ) = t at h₁ ⊢
    simp [models_iff] at h₁
    simp [models_iff, δ, h₁]

/--
$\mathsf{TC}$ is essentially undecidable.
- [GZ08, Theorem 16]
-/
instance : (𝗧𝗖 : ConcatenationTheory).EssentiallyUndecidable where
  undecidable_of_consistent T _ _ h := uncomputable_theory_of_consistent T h.dec

/--
The theorems of $\mathsf{TC}$ are not computable.
- [GZ08, Theorem 16]
-/
theorem undecidable : Entailment.Undecidable 𝗧𝗖 := Theory.EssentiallyUndecidable.undecidable 𝗧𝗖

end FFL.FirstOrder.Concatenation

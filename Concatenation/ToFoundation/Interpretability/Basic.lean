module

public import Foundation.FirstOrder.LK.Interpretation
public import Foundation.FirstOrder.Tarski.Definability

/-!
# Non-interpretability

The negation of direct interpretability, and its transfer along interpretations.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- `T` does not directly interpret `U`. -/
abbrev NotInterprets {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T]
    (U : Theory L₂) : Prop := IsEmpty (T ⊳ U)

@[inherit_doc]
infix:50 " ⋫ " => NotInterprets

variable {L₁ L₂ L₃ : Language} [L₁.Eq] [L₂.Eq] [L₃.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

/--
A sentence of `U` translates to one true in `M` when the model of the translation in `M` satisfies
`U`.
-/
lemma DirectTranslation.models_translate_of_mem {τ : DirectTranslation T L₂} {M : Type*}
    [Nonempty M] [Tarski.Structure L₁ M] [Tarski.Structure.Eq L₁ M] [M↓[L₁] ⊧* T]
    [(τ.Model M)↓[L₂] ⊧* U] {σ : Sentence L₂} (hσ : σ ∈ U) : M↓[L₁] ⊧ τ.translate σ :=
  DirectTranslation.Model.translate_iff.mpr <| models_theory_iff.mp inferInstance σ hσ

/--
A binary function symbol translated to a formula that defines `R` takes a value related by `R` to
its arguments.
-/
lemma DirectTranslation.Model.rel_func_of_defined {τ : DirectTranslation T L₂} {M : Type*}
    [Nonempty M] [Tarski.Structure L₁ M] [Tarski.Structure.Eq L₁ M] [M↓[L₁] ⊧* T] {f : L₂.Func 2}
    {R : M → M → M → Prop} {φ : Semisentence L₁ 3} (hf : τ.func f = ⟨φ⟩)
    [L₁-relation₃[M] R via φ] (a b : τ.Model M) :
    R (Tarski.Structure.func f ![a, b] : τ.Model M) a b := by
  have h := Model.eval_func (π := τ) (M := M) f ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → τ.Model M) i : M), hf] at h
  simpa [Semiformula.Operator.val, Defined.eval_iff] using h

lemma notInterprets_iff : T ⋫ U ↔ ¬Nonempty (T ⊳ U) := not_nonempty_iff.symm

namespace NotInterprets

variable [𝗘𝗤 _ ⪯ U] {S : Theory L₃}

/-- A theory interpreted in `T` does not interpret what `T` does not interpret. -/
lemma of_left (h : T ⋫ S) (π : T ⊳ U) : U ⋫ S := ⟨fun ρ ↦ h.false (ρ.comp π)⟩

/-- `T` does not interpret a theory that interprets what `T` does not interpret. -/
lemma of_right (h : T ⋫ S) (π : U ⊳ S) : T ⋫ U := ⟨fun ρ ↦ h.false (π.comp ρ)⟩

end NotInterprets

end FFL.FirstOrder

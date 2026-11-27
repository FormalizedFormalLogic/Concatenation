module

public import Foundation.FirstOrder.Incompleteness.Essentially
public import Foundation.FirstOrder.LK.Basic

/-!
# Decidable and essentially undecidable theories

Complete recursively enumerable theories are decidable, and a theory with a model whose theory is
decidable is not essentially undecidable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

variable {L : Language} [L.Encodable] [L.Primcodable]

/-- A theory with a model whose theory is decidable is not essentially undecidable. -/
lemma Theory.not_essentiallyUndecidable_of_models {T : Theory L} (V : Type*) [Nonempty V]
    [Tarski.Structure L V] [V↓[L] ⊧* T]
    (h : Entailment.Decidable (Tarski.Structure.theory L V)) :
    ¬Entailment.EssentiallyUndecidable T fun _ ↦ True := fun _ ↦
  have : V↓[L] ⊧* Tarski.Structure.theory L V := models_theory_iff.mpr fun _ h ↦ h
  Entailment.EssentiallyUndecidable.essentially_undec (𝓢 := T) (P := fun _ ↦ True)
    (Tarski.Structure.theory L V)
    (Entailment.weakerThan_iff.mpr fun h ↦
      Entailment.by_axm <| consequence_iff'.mp (Theory.Proof.sound h) V)
    (consistent_of_model _ V) trivial h

namespace Theory

open Arithmetic Arithmetic.Bootstrapping

variable [L.LORDefinable] [L.DecidableEq] (T : Theory L) [T.RE]

/-- A complete recursively enumerable theory is decidable. -/
theorem decidable_of_complete (h : Entailment.Complete T) : Entailment.Decidable T := by
  by_cases hT : Entailment.Consistent T
  · exact ⟨computablePred_theory_of_complete h⟩
  · exact Entailment.decidable_of_inconsistent <| Entailment.not_consistent_iff_inconsistent.mp hT

/-- The theory of a model of a complete recursively enumerable theory is decidable. -/
theorem decidable_theory_of_complete (V : Type*) [Nonempty V] [Tarski.Structure L V] [V↓[L] ⊧* T]
    (h : Entailment.Complete T) : Entailment.Decidable (Tarski.Structure.theory L V) where
  dec := by
    have : V↓[L] ⊧* Tarski.Structure.theory L V := models_theory_iff.mpr fun _ h ↦ h
    apply (decidable_of_complete T h).dec.of_eq
    intro σ
    change T ⊢ σ ↔ Tarski.Structure.theory L V ⊢ σ
    constructor
    · exact fun hσ ↦ Entailment.by_axm <| consequence_iff'.mp (Theory.Proof.sound hσ) V
    · intro hσ
      refine (h.con σ).resolve_right fun hn ↦ ?_
      have h₁ := consequence_iff'.mp (Theory.Proof.sound hσ) V
      have h₂ := consequence_iff'.mp (Theory.Proof.sound hn) V
      simp_all [models_iff]

end Theory

end FFL.FirstOrder

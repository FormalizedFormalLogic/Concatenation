module

public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-!
# Finite models and finite parts of theories

Theories with a finite model, and the finite parts of a theory that prove finitely many of its
theorems.
-/

@[expose] public section

namespace FFL.FirstOrder

open _root_.FFL.Entailment

namespace Theory

variable {L : Language} {T U : Theory L}

/-- `T` has a finite model. -/
def HasFiniteModel (T : Theory L) : Prop :=
  ∃ (V : Type) (_ : Nonempty V) (_ : Finite V) (_ : Tarski.Structure L V), V↓[L] ⊧* T

/-- A finite model can be taken to interpret the equality symbol as equality. -/
lemma HasFiniteModel.exists_eq [L.Eq] [𝗘𝗤 L ⪯ T] (h : T.HasFiniteModel) :
    ∃ (V : Type) (_ : Nonempty V) (_ : Finite V) (_ : Tarski.Structure L V)
      (_ : Tarski.Structure.Eq L V), V↓[L] ⊧* T := by
  obtain ⟨V, hV, hf, s, hT⟩ := h
  have : V↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hT
  exact ⟨Tarski.Structure.Eq.QuotEq L V, inferInstance,
    inferInstanceAs (Finite (Quotient (Tarski.Structure.Eq.eqvSetoid L V))), inferInstance,
    inferInstance, (Tarski.Structure.Eq.QuotEq.elementaryEquiv L V).modelsTheory.mpr hT⟩

/-- Finitely many theorems of `T` follow from finitely many axioms of `T`. -/
lemma exists_finite_subset_weakerThan (hU : U.Finite) (h : U ⪯ T) :
    ∃ F ⊆ T, F.Finite ∧ U ⪯ F := by
  have (σ : U) : ∃ F : Theory L, F ⊆ T ∧ F.Finite ∧ F ⊢ σ.val :=
    let ⟨F, hF, hfin, hσ⟩ := Compact.finite_provable (h.pbl <| by_axm σ.prop)
    ⟨F, hF, by simpa using hfin, hσ⟩
  choose F hF hfin hσ using this
  have := hU.to_subtype
  use ⋃ σ, F σ
  exact ⟨Set.iUnion_subset hF, Set.finite_iUnion hfin,
    WeakerThan.ofAxm! fun {σ} hσU ↦
      Axiomatized.weakening (Set.subset_iUnion F ⟨σ, hσU⟩) (hσ ⟨σ, hσU⟩)⟩

end Theory

end FFL.FirstOrder

module

public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Foundation.FirstOrder.Arithmetic.Q.Basic

/-!
# Robinson's arithmetic $\mathsf{Q}$

$\mathsf{Q}$ is finitely axiomatizable, has no finite models, and is essentially undecidable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

namespace RobinsonQ

lemma finite : (𝗤 : ArithmeticTheory).Finite := by
  apply ((Theory.Eq.finite (L := ℒₒᵣ)).union
    (Set.toFinite {_, _, _, _, _, _, _, _})).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | succNeZero => exact .inr <| .inl rfl
    | succInj => exact .inr <| .inr <| .inl rfl
    | zeroOrSucc => exact .inr <| .inr <| .inr <| .inl rfl
    | addZero => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | addSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulZero => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | mulSucc => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | ltDef => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr rfl

lemma finiteAxiomatizable : FiniteAxiomatizable 𝗤 := .of_finite finite

lemma infinite_of_models (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗤] : Infinite M :=
  not_finite_iff_infinite.mp fun _ ↦
    let ⟨x, hx⟩ := Finite.surjective_of_injective (fun _ _ ↦ succ_inj : (· + (1 : M)).Injective) 0
    Arithmetic.succ_ne_zero x hx

/--
$\mathsf{Q}$ has no finite models.
- [Hor11, §3, Proposition 3.2]
-/
theorem not_hasFiniteModel : ¬(𝗤 : ArithmeticTheory).HasFiniteModel := by
  intro h
  obtain ⟨M, _, hfin, _, _, hM⟩ := h.exists_eq
  obtain ⟨N, _, _, _, s, _, hN⟩ : ∃ (N : Type) (_ : Nonempty N) (_ : Finite N)
      (_ : ORingStructure N) (_ : Tarski.Structure ℒₒᵣ N) (_ : Tarski.Structure.ORing ℒₒᵣ N),
      N↓[ℒₒᵣ] ⊧* 𝗤 :=
    let e := Tarski.Structure.Model.equiv ℒₒᵣ M
    let s : Tarski.Structure ℒₒᵣ (Tarski.Structure.Model ℒₒᵣ M) := Tarski.Structure.ofEquiv e
    ⟨Tarski.Structure.Model ℒₒᵣ M, inferInstance, .of_equiv M e, inferInstance, s,
      inferInstance,
      (Tarski.Structure.Model.elementaryEquiv ℒₒᵣ M).modelsTheory.mp hM⟩
  rcases standardModel_unique N s
  exact not_finite_iff_infinite.mpr (infinite_of_models N) inferInstance

end RobinsonQ

/--
$\mathsf{Q}$ is essentially undecidable.
- [Sve08, §2]
-/
instance : (𝗤 : ArithmeticTheory).EssentiallyUndecidable :=
  Theory.EssentiallyUndecidable.of_weakerThan 𝗥₀ 𝗤

end FFL.FirstOrder.Arithmetic

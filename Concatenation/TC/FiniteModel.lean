module

public import Concatenation.TC.Substring
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable

/-!
# $\mathsf{TC}$ is finitely axiomatizable and has no finite models
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

lemma finite_TC : (𝗧𝗖 : ConcatenationTheory).Finite := by
  apply ((Theory.Eq.finite (L := ℒ⌢)).union (Set.toFinite {_, _, _, _, _})).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | concatAssoc => exact .inr <| .inl rfl
    | editor => exact .inr <| .inr <| .inl rfl
    | zeroNeConcat => exact .inr <| .inr <| .inr <| .inl rfl
    | oneNeConcat => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | zeroNeOne => exact .inr <| .inr <| .inr <| .inr <| .inr rfl

lemma finiteAxiomatizable_TC : FiniteAxiomatizable 𝗧𝗖 := .of_finite finite_TC

lemma infinite_of_models (M : Type*) [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖] : Infinite M :=
  not_finite_iff_infinite.mp fun _ ↦
    let ⟨x, hx⟩ := Finite.surjective_of_injective
      (fun _ _ ↦ isAtom_zero.append_right_cancel : (· ++ (0 : M)).Injective) 0
    zero_ne_append x 0 hx.symm

theorem not_hasFiniteModel_TC : ¬(𝗧𝗖 : ConcatenationTheory).HasFiniteModel := by
  intro h
  obtain ⟨M, _, _, s, _, hM⟩ := h.exists_eq
  let c : ConcatenationStructure M :=
    { zero := s.func Language.Zero.zero ![]
      one := s.func Language.One.one ![]
      append a b := s.func Language.Concat.concat ![a, b] }
  have : Tarski.Structure.Zero ℒ⌢ M := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.One ℒ⌢ M := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.Concat ℒ⌢ M := ⟨fun a b ↦ rfl⟩
  rw [standardModel_unique M s] at hM
  exact not_finite_iff_infinite.mpr (infinite_of_models M) inferInstance

end FFL.FirstOrder.Concatenation

module

public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Concatenation.ToFoundation.Interpretability.Table

/-!
# Undecidability and direct interpretations

Undecidability and essential undecidability transfer along direct interpretations.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A theory with a model whose theory is decidable is not essentially undecidable. -/
lemma Theory.not_essentiallyUndecidable_of_models {L : Language} [L.Encodable] [L.Primcodable]
    {T : Theory L} (M : Type*) [Nonempty M] [Tarski.Structure L M] [M↓[L] ⊧* T]
    (h : Entailment.Decidable (Tarski.Structure.theory L M)) : ¬T.EssentiallyUndecidable := fun _ ↦
  have : M↓[L] ⊧* Tarski.Structure.theory L M := models_theory_iff.mpr fun _ h ↦ h
  Theory.EssentiallyUndecidable.undecidable_of_consistent (T := T) (Tarski.Structure.theory L M)
    (Entailment.weakerThan_iff.mpr fun h ↦
      Entailment.by_axm <| consequence_iff'.mp (Theory.Proof.sound h) M)
    (consistent_of_model _ M) h

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

theorem undecidable_of_undecidable_pullback (h : Entailment.Undecidable π.pullback) :
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

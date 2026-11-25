module

public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.Table

/-!
# Undecidability and direct interpretations

Undecidability and essential undecidability transfer along direct interpretations.
-/

@[expose] public section

namespace FFL.FirstOrder.DirectInterpretation

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
- [Sve08, §2]
-/
theorem undecidable [U.EssentiallyUndecidable] [Entailment.Consistent T] :
    Entailment.Undecidable T :=
  π.undecidable_of_undecidable_pullback <|
    Theory.EssentiallyUndecidable.undecidable_of_consistent (T := U) _ inferInstance inferInstance

/--
A theory directly interpreting an essentially undecidable theory is essentially undecidable.
- [Sve08, §2]
-/
theorem essentiallyUndecidable [U.EssentiallyUndecidable] : T.EssentiallyUndecidable where
  undecidable_of_consistent T' hT _ :=
    have : 𝗘𝗤 L₁ ⪯ T' := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 L₁ ⪯ T)) hT
    (π.ofWeakerThanLeft (T' := T')).undecidable

end FFL.FirstOrder.DirectInterpretation

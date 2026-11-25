module

public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToFoundation.FirstOrder.Axiomatizability

/-!
# Locally finitely satisfiable theories

A locally finitely satisfiable theory interprets no finitely axiomatizable theory without finite
models.
-/

@[expose] public section

namespace FFL.FirstOrder

open _root_.FFL.Entailment

namespace Theory

variable {L : Language} {T U : Theory L}

/-- `T` has a finite model. -/
def HasFiniteModel (T : Theory L) : Prop :=
  ∃ (M : Type) (_ : Nonempty M) (_ : Finite M) (_ : Tarski.Structure L M), M↓[L] ⊧* T

/--
`T` is locally finitely satisfiable: every finite subset of `T` has a finite model.
- [Hor11, §3]
- [Hor12, §1]
-/
def LocallyFinitelySatisfiable (T : Theory L) : Prop := ∀ F ⊆ T, F.Finite → F.HasFiniteModel

lemma HasFiniteModel.of_weakerThan (h : U.HasFiniteModel) (hT : T ⪯ U) : T.HasFiniteModel :=
  let ⟨M, hM, hf, s, hU⟩ := h
  ⟨M, hM, hf, s, models_of_subtheory hU⟩

/-- A finite model can be taken to interpret the equality symbol as equality. -/
lemma HasFiniteModel.exists_eq [L.Eq] [𝗘𝗤 L ⪯ T] (h : T.HasFiniteModel) :
    ∃ (M : Type) (_ : Nonempty M) (_ : Finite M) (_ : Tarski.Structure L M)
      (_ : Tarski.Structure.Eq L M), M↓[L] ⊧* T := by
  obtain ⟨M, hM, hf, s, hT⟩ := h
  have : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hT
  exact ⟨Tarski.Structure.Eq.QuotEq L M, inferInstance,
    inferInstanceAs (Finite (Quotient (Tarski.Structure.Eq.eqvSetoid L M))), inferInstance,
    inferInstance, (Tarski.Structure.Eq.QuotEq.elementaryEquiv L M).modelsTheory.mpr hT⟩

lemma LocallyFinitelySatisfiable.of_subset (h : U.LocallyFinitelySatisfiable) (hT : T ⊆ U) :
    T.LocallyFinitelySatisfiable := fun F hF ↦ h F (hF.trans hT)

/--
A theory each of whose axioms holds in all but finitely many of the finite structures `M 0`,
`M 1`, … is locally finitely satisfiable.
-/
lemma LocallyFinitelySatisfiable.of_eventually (M : ℕ → Type) [∀ n, Nonempty (M n)]
    [∀ n, Finite (M n)] [∀ n, Tarski.Structure L (M n)]
    (h : ∀ σ ∈ T, ∀ᶠ n in Filter.atTop, (M n)↓[L] ⊧ σ) : T.LocallyFinitelySatisfiable := by
  intro F hF hfin
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finite hfin).mpr fun σ hσ ↦ h σ (hF hσ)).exists
  exact ⟨M n, inferInstance, inferInstance, inferInstance, models_theory_iff.mpr hn⟩

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

namespace DirectInterpretation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

/--
A finitely axiomatizable theory interpreted in `T` is interpreted in a finite subset of `T`.
- [Hor11, §3, Proposition 3.2]
-/
theorem exists_finite_subset [L₁.Finite] [L₂.Finite] (π : T ⊳ U) (hU : FiniteAxiomatizable U) :
    ∃ F ⊆ T, F.Finite ∧ ∃ _ : 𝗘𝗤 L₁ ⪯ F, Nonempty (F ⊳ U) := by
  have : Fintype ((k : ℕ) × L₂.Func k) := Language.Finite.func
  obtain ⟨V, hV, hUV⟩ := hU
  have : V ⪯ U := hUV.symm.le
  have hT : 𝗘𝗤 L₁ ∪ π.translate '' V ⪯ T := WeakerThan.ofAxm! <| by
    rintro σ (hσ | ⟨σ, hσ, rfl⟩)
    · exact WeakerThan.pbl (𝓢 := 𝗘𝗤 L₁) <| by_axm hσ
    · exact π.sound <| WeakerThan.pbl (𝓢 := V) <| by_axm hσ
  obtain ⟨F₀, hF₀, hfin₀, h₀⟩ := Theory.exists_finite_subset_weakerThan
    (Theory.Eq.finite.union <| hV.image _) hT
  obtain ⟨F₁, hF₁, hfin₁, h₁⟩ := Compact.finite_provable π.trln.domain_nonempty
  obtain ⟨F₂, hF₂, hfin₂, h₂⟩ := Compact.finite_provable π.trln.preserve_eq
  choose F₃ hF₃ hfin₃ h₃ using fun f : (k : ℕ) × L₂.Func k ↦
    Compact.finite_provable (π.trln.func_defined f.2)
  let F : Theory L₁ := F₀ ∪ F₁ ∪ F₂ ∪ ⋃ f, F₃ f
  have hFT : F ⊆ T :=
    Set.union_subset (Set.union_subset (Set.union_subset hF₀ hF₁) hF₂) <| Set.iUnion_subset hF₃
  have : F ⪯ T := Theory.Proof.weakerThan_of_le hFT
  have h₀ : 𝗘𝗤 L₁ ∪ π.translate '' V ⪯ F :=
    h₀.trans <| WeakerThan.ofSubset fun _ h ↦ .inl <| .inl <| .inl h
  have : 𝗘𝗤 L₁ ⪯ F := WeakerThan.trans (WeakerThan.ofSubset Set.subset_union_left) h₀
  let ρ : DirectTranslation F L₂ := {
    domain := π.trln.domain
    rel := π.trln.rel
    func := π.trln.func
    domain_nonempty := Axiomatized.weakening (fun _ h ↦ .inl <| .inl <| .inr h) h₁
    func_defined f := Axiomatized.weakening
      (fun _ h ↦ .inr <| Set.mem_iUnion_of_mem ⟨_, f⟩ h) (h₃ ⟨_, f⟩)
    preserve_eq := Axiomatized.weakening (fun _ h ↦ .inl <| .inr h) h₂ }
  have hρ (σ : Sentence L₂) : ρ.translate σ = π.translate σ :=
    (ρ.ofWeakerThan_translate (T' := T) σ).symm
  let ρ' : F ⊳ V := {
    trln := ρ
    interpret_theory σ hσ := hρ σ ▸ h₀.pbl (by_axm <| Or.inr <| Set.mem_image_of_mem _ hσ) }
  exact ⟨F, hFT,
    ((hfin₀.union <| by simpa using hfin₁).union <| by simpa using hfin₂).union <|
      Set.finite_iUnion fun f ↦ by simpa using hfin₃ f,
    inferInstance, ⟨ρ, fun σ hσ ↦ ρ'.sound <| hUV.le.pbl <| by_axm hσ⟩⟩

/--
A finitely axiomatizable theory interpreted in a locally finitely satisfiable theory has a finite
model.
- [Hor11, §3, Proposition 3.2]
-/
theorem hasFiniteModel [L₁.Finite] [L₂.Finite] (π : T ⊳ U) (hT : T.LocallyFinitelySatisfiable)
    (hU : FiniteAxiomatizable U) : U.HasFiniteModel := by
  obtain ⟨F, hF, hfin, _, ⟨ρ⟩⟩ := π.exists_finite_subset hU
  obtain ⟨M, _, _, _, _, _⟩ := (hT F hF hfin).exists_eq
  exact ⟨ρ.trln.Model M, inferInstance,
    Finite.of_injective _ fun _ _ ↦ DirectTranslation.Model.val_inj_iff.mp, inferInstance,
    models_theory_iff.mpr fun σ hσ ↦ DirectTranslation.Model.translate_iff.mp <|
      models_of_provable inferInstance <| ρ.interpret_theory σ hσ⟩

/--
A theory interpreted in a locally finitely satisfiable theory is locally finitely satisfiable.
- [Hor11, §3, Theorem 3.3]
-/
theorem locallyFinitelySatisfiable [L₁.Finite] [L₂.Finite] (π : T ⊳ U)
    (hT : T.LocallyFinitelySatisfiable) : U.LocallyFinitelySatisfiable := fun F hF hfin ↦
  let ρ : T ⊳ F := ⟨π.trln, fun σ hσ ↦ π.interpret_theory σ (hF hσ)⟩
  ρ.hasFiniteModel hT <| .of_finite hfin

/--
A locally finitely satisfiable theory interprets no finitely axiomatizable theory without finite
models.
- [Hor11, §3, Proposition 3.2]
-/
theorem isEmpty_of_not_hasFiniteModel [L₁.Finite] [L₂.Finite] (hT : T.LocallyFinitelySatisfiable)
    (hU : FiniteAxiomatizable U) (h : ¬U.HasFiniteModel) : IsEmpty (T ⊳ U) :=
  ⟨fun π ↦ h <| π.hasFiniteModel hT hU⟩

end DirectInterpretation

end FFL.FirstOrder

module

public import Foundation.FirstOrder.Incompleteness.Church
public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.Logic.Decidability

/-!
# Essentially undecidable theories

First-order theories all of whose consistent extensions are undecidable, and criteria for a theory
to be decidable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

universe u

section

variable {L : Language.{u}} {M N : Type*} [Nonempty M] [Nonempty N] [sM : Tarski.Structure L M]
  [sN : Tarski.Structure L N]

/-- Two structures in which every relation symbol holds everywhere satisfy the same formulas. -/
lemma Semiformula.eval_iff_eval_of_rel {ξ : Type*} {n : ℕ} (hM : ∀ k (r : L.Rel k) v, sM.rel r v)
    (hN : ∀ k (r : L.Rel k) v, sN.rel r v) (φ : Semiformula L ξ n) (e : Fin n → M) (ε : ξ → M)
    (e' : Fin n → N) (ε' : ξ → N) : Eval (s := sM) e ε φ ↔ Eval (s := sN) e' ε' φ := by
  induction φ using Semiformula.rec' with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => simp [eval_rel, hM, hN]
  | hnrel r v => simp [eval_nrel, hM, hN]
  | hand φ ψ ihφ ihψ => simp [ihφ e e', ihψ e e']
  | hor φ ψ ihφ ihψ => simp [ihφ e e', ihψ e e']
  | hall φ ih =>
    simp only [eval_all]
    exact ⟨fun h y ↦ (ih (Classical.arbitrary M :> e) _).mp <| h _,
      fun h x ↦ (ih _ (Classical.arbitrary N :> e')).mpr <| h _⟩
  | hexs φ ih =>
    simp only [eval_ex]
    exact ⟨fun ⟨x, h⟩ ↦ ⟨Classical.arbitrary N, (ih _ _).mp h⟩,
      fun ⟨y, h⟩ ↦ ⟨Classical.arbitrary M, (ih _ _).mpr h⟩⟩

/--
A theory in all of whose models every relation symbol holds everywhere proves exactly the sentences
true in one such model.
-/
lemma Theory.provable_iff_models_of_rel {U : Theory L} (N : Type u) [Nonempty N]
    [sN : Tarski.Structure L N] [h₀ : N↓[L] ⊧* U] (hN : ∀ k (r : L.Rel k) v, sN.rel r v)
    (h : ∀ (M : Type u) [Nonempty M] [s : Tarski.Structure L M], M↓[L] ⊧* U →
      ∀ k (r : L.Rel k) v, s.rel r v) {σ : Sentence L} : U ⊢ σ ↔ N↓[L] ⊧ σ := by
  constructor
  · exact models_of_provable h₀
  · intro hσ
    apply Theory.Proof.small_complete
    apply consequence_iff.mpr
    intro M _ s hM
    exact (Semiformula.eval_iff_eval_of_rel (h M hM) hN σ _ _ _ _).mpr hσ

end

variable {L : Language.{u}} [L.Encodable] [L.Primcodable]

/--
Every consistent extension of `T` in its language is undecidable.
- [Sve08, §1]
-/
class Theory.EssentiallyUndecidable (T : Theory L) : Prop where
  undecidable_of_consistent : ∀ U : Theory L, T ⪯ U → Entailment.Consistent U →
    Entailment.Undecidable U

namespace Theory.EssentiallyUndecidable

theorem undecidable (T : Theory L) [T.EssentiallyUndecidable] [Entailment.Consistent T] :
    Entailment.Undecidable T :=
  undecidable_of_consistent (T := T) T (Entailment.WeakerThan.refl T) inferInstance

theorem of_weakerThan (T U : Theory L) [T.EssentiallyUndecidable] [T ⪯ U] :
    U.EssentiallyUndecidable where
  undecidable_of_consistent V hUV hV :=
    undecidable_of_consistent (T := T) V (Entailment.WeakerThan.trans inferInstance hUV) hV

instance (T : Theory L) [T.EssentiallyUndecidable] : Entailment.EssentiallyUndecidable T where
  essentially_undec U hTU hU := undecidable_of_consistent U hTU <|
    Entailment.consistent_of_incomplete (h := hU)

end Theory.EssentiallyUndecidable

namespace Theory

/-- A theory with a consistent decidable extension is not essentially undecidable. -/
theorem not_essentiallyUndecidable_of_decidable (T U : Theory L) [T ⪯ U] [Entailment.Consistent U]
    (h : Entailment.Decidable U) : ¬T.EssentiallyUndecidable := fun _ ↦
  EssentiallyUndecidable.undecidable_of_consistent (T := T) U inferInstance inferInstance h

/-- A theory with a model whose theory is decidable is not essentially undecidable. -/
theorem not_essentiallyUndecidable_of_models (T : Theory L) (M : Type u) [Nonempty M]
    [Tarski.Structure L M] [hM : M↓[L] ⊧* T]
    (h : Entailment.Decidable (Tarski.Structure.theory L M)) : ¬T.EssentiallyUndecidable :=
  have : T ⪯ Tarski.Structure.theory L M :=
    Entailment.WeakerThan.ofSubset <| Tarski.Structure.subset_of_models.mpr hM
  have : Entailment.Consistent (Tarski.Structure.theory L M) :=
    consistent_of_satisfiable Tarski.Structure.theory_satisfiable
  not_essentiallyUndecidable_of_decidable T _ h

variable [L.LORDefinable]

open Arithmetic Bootstrapping

lemma rePred_provable (T : Theory L) [T.Δ₁] : REPred fun σ : Sentence L ↦ T ⊢ σ := by
  have h : 𝚺ᴬ₁-Predicate fun n : ℕ ↦ Provable T n := by definability
  apply ((rePred_iff_sigma1.mpr h).comp Computable.encode).of_eq
  intro σ
  simp [← Sentence.quote_eq_encode_nat]

lemma rePred_provable_neg (T : Theory L) [T.Δ₁] : REPred fun σ : Sentence L ↦ T ⊢ ∼σ := by
  have h : 𝚺ᴬ₁-Predicate fun n : ℕ ↦ Provable T (neg L n) := by definability
  apply ((rePred_iff_sigma1.mpr h).comp Computable.encode).of_eq
  intro σ
  change Provable T (neg L (Encodable.encode σ)) ↔ T ⊢ ∼σ
  rw [← provable_iff_provable (T := T), ← Sentence.quote_eq_encode_nat]
  simp [Sentence.quote_def, Semiformula.quote_def]

open Classical in
/-- A complete theory with a $\Delta_1$ set of axioms is decidable. -/
theorem decidable_of_complete (T : Theory L) [T.Δ₁] [Entailment.Complete T] :
    Entailment.Decidable T := by
  by_cases hT : Entailment.Inconsistent T
  · exact Entailment.decidable_of_incomplete hT
  have : Entailment.Consistent T := Entailment.not_inconsistent_iff_consistent.mp hT
  constructor
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  constructor
  · exact (rePred_provable T).of_eq fun σ ↦ by simp [Entailment.theory]
  · apply (rePred_provable_neg T).of_eq
    intro σ
    have : T ⊢ ∼σ ↔ ¬T ⊢ σ := by
      constructor
      · intro h h'
        exact Entailment.Consistent.not_bot (𝓢 := T) <| by cl_prover [h, h']
      · exact (Entailment.Complete.con (𝓢 := T) σ).resolve_left
    exact this

/--
A theory with a model in which every relation symbol holds everywhere is not essentially
undecidable, if a $\Delta_1$ set of sentences true in that model forces this on every model.
-/
theorem not_essentiallyUndecidable_of_models_of_rel (T U : Theory L) [U.Δ₁] (N : Type u)
    [Nonempty N] [sN : Tarski.Structure L N] [hT : N↓[L] ⊧* T] [N↓[L] ⊧* U]
    (hN : ∀ k (r : L.Rel k) v, sN.rel r v)
    (h : ∀ (M : Type u) [Nonempty M] [s : Tarski.Structure L M], M↓[L] ⊧* U →
      ∀ k (r : L.Rel k) v, s.rel r v) : ¬T.EssentiallyUndecidable :=
  have : T ⪯ U := Entailment.weakerThan_iff.mpr fun hσ ↦
    (provable_iff_models_of_rel N hN h).mpr <| models_of_provable hT hσ
  have : Entailment.Consistent U := consistent_of_model U N
  have : Entailment.Complete U := ⟨fun σ ↦ by
    by_cases hσ : N↓[L] ⊧ σ
    · exact .inl <| (provable_iff_models_of_rel N hN h).mpr hσ
    · exact .inr <| (provable_iff_models_of_rel N hN h).mpr <| by simpa [models_iff] using hσ⟩
  not_essentiallyUndecidable_of_decidable T U <| decidable_of_complete U

end Theory

end FFL.FirstOrder

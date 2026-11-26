module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick
public import Foundation.FirstOrder.LK.Basic
public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
public import Foundation.Logic.Decidability

/-!
# Decidable and essentially undecidable theories

Complete recursively enumerable theories are decidable; first-order theories all of whose
consistent extensions are undecidable.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

universe u

section rel

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

end rel

variable {L : Language} [L.Encodable] [L.Primcodable]

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

lemma of_weakerThan (T U : Theory L) [T.EssentiallyUndecidable] [T ⪯ U] :
    U.EssentiallyUndecidable where
  undecidable_of_consistent V hUV hV :=
    undecidable_of_consistent (T := T) V (Entailment.WeakerThan.trans inferInstance hUV) hV

instance (T : Theory L) [T.EssentiallyUndecidable] : Entailment.EssentiallyUndecidable T where
  essentially_undec U hTU hU := undecidable_of_consistent U hTU <|
    Entailment.consistent_of_incomplete (h := hU)

end Theory.EssentiallyUndecidable

/-- A theory with a model whose theory is decidable is not essentially undecidable. -/
lemma Theory.not_essentiallyUndecidable_of_models {T : Theory L} (M : Type*) [Nonempty M]
    [Tarski.Structure L M] [M↓[L] ⊧* T]
    (h : Entailment.Decidable (Tarski.Structure.theory L M)) : ¬T.EssentiallyUndecidable := fun _ ↦
  have : M↓[L] ⊧* Tarski.Structure.theory L M := models_theory_iff.mpr fun _ h ↦ h
  Theory.EssentiallyUndecidable.undecidable_of_consistent (T := T) (Tarski.Structure.theory L M)
    (Entailment.weakerThan_iff.mpr fun h ↦
      Entailment.by_axm <| consequence_iff'.mp (Theory.Proof.sound h) M)
    (consistent_of_model _ M) h

namespace Theory

open Arithmetic Arithmetic.Bootstrapping

variable [L.LORDefinable] [L.DecidableEq] (T : Theory L) [T.RE]

/-- The theorems of a recursively enumerable theory are recursively enumerable. -/
lemma rePred_provable : REPred fun σ : Sentence L ↦ T ⊢ σ := by
  have h : 𝚺ᴬ₁-Predicate fun n : ℕ ↦ Provable T.craig n := by definability
  apply ((rePred_iff_sigma1.mpr h).comp Computable.encode).of_eq
  intro σ
  rw [← Sentence.quote_eq_encode_nat, provable_iff_provable]
  exact (Entailment.Equiv.iff.mp inferInstance σ).symm

/-- The sentences refuted by a recursively enumerable theory are recursively enumerable. -/
lemma rePred_provable_neg : REPred fun σ : Sentence L ↦ T ⊢ ∼σ := by
  have h : 𝚺ᴬ₁-Predicate fun n : ℕ ↦ Provable T.craig (neg L n) := by definability
  apply ((rePred_iff_sigma1.mpr h).comp Computable.encode).of_eq
  intro σ
  have : neg L (⌜σ⌝ : ℕ) = ⌜∼σ⌝ := by simp [Sentence.quote_def, Semiformula.quote_def]
  rw [← Sentence.quote_eq_encode_nat, this, provable_iff_provable]
  exact (Entailment.Equiv.iff.mp inferInstance _).symm

/-- A complete recursively enumerable theory is decidable. -/
theorem decidable_of_complete (h : Entailment.Complete T) : Entailment.Decidable T := by
  classical
  by_cases hT : Entailment.Consistent T
  · constructor
    apply ComputablePred.computable_iff_re_compl_re'.mpr
    and_intros
    · exact T.rePred_provable
    · apply T.rePred_provable_neg.of_eq
      intro σ
      constructor
      · intro hσ hσ'
        exact Entailment.Consistent.not_bot (𝓢 := T) <| Entailment.neg_mdp hσ hσ'
      · intro hσ
        exact (h.con σ).resolve_left hσ
  · exact Entailment.decidable_of_incomplete <| Entailment.not_consistent_iff_inconsistent.mp hT

end Theory

section

variable {L : Language.{u}} [L.Encodable] [L.Primcodable] [L.LORDefinable] [L.DecidableEq]

/--
A theory with a model in which every relation symbol holds everywhere is not essentially
undecidable, if a recursively enumerable set of sentences true in that model forces this on every
model.
-/
theorem Theory.not_essentiallyUndecidable_of_models_of_rel
    (T U : Theory L) [U.RE] (N : Type u) [Nonempty N] [sN : Tarski.Structure L N] [hT : N↓[L] ⊧* T]
    [N↓[L] ⊧* U] (hN : ∀ k (r : L.Rel k) v, sN.rel r v)
    (h : ∀ (M : Type u) [Nonempty M] [s : Tarski.Structure L M], M↓[L] ⊧* U →
      ∀ k (r : L.Rel k) v, s.rel r v) : ¬T.EssentiallyUndecidable := fun hT' ↦
  have : T ⪯ U := Entailment.weakerThan_iff.mpr fun hσ ↦
    (provable_iff_models_of_rel N hN h).mpr <| models_of_provable hT hσ
  have : Entailment.Consistent U := consistent_of_model U N
  have : Entailment.Complete U := ⟨fun σ ↦ by
    by_cases hσ : N↓[L] ⊧ σ
    · exact .inl <| (provable_iff_models_of_rel N hN h).mpr hσ
    · exact .inr <| (provable_iff_models_of_rel N hN h).mpr <| by simpa [models_iff] using hσ⟩
  Theory.EssentiallyUndecidable.undecidable_of_consistent (T := T) U inferInstance inferInstance
    (Theory.decidable_of_complete U inferInstance)

end

end FFL.FirstOrder

module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick
public import Foundation.FirstOrder.LK.Basic
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
  undecidable_of_consistent S hUV hV :=
    undecidable_of_consistent (T := T) S (Entailment.WeakerThan.trans inferInstance hUV) hV

instance (T : Theory L) [T.EssentiallyUndecidable] : Entailment.EssentiallyUndecidable T where
  essentially_undec U hTU hU := undecidable_of_consistent U hTU <|
    Entailment.consistent_of_incomplete (h := hU)

end Theory.EssentiallyUndecidable

/-- A theory with a model whose theory is decidable is not essentially undecidable. -/
lemma Theory.not_essentiallyUndecidable_of_models {T : Theory L} (V : Type*) [Nonempty V]
    [Tarski.Structure L V] [V↓[L] ⊧* T]
    (h : Entailment.Decidable (Tarski.Structure.theory L V)) : ¬T.EssentiallyUndecidable := fun _ ↦
  have : V↓[L] ⊧* Tarski.Structure.theory L V := models_theory_iff.mpr fun _ h ↦ h
  Theory.EssentiallyUndecidable.undecidable_of_consistent (T := T) (Tarski.Structure.theory L V)
    (Entailment.weakerThan_iff.mpr fun h ↦
      Entailment.by_axm <| consequence_iff'.mp (Theory.Proof.sound h) V)
    (consistent_of_model _ V) h

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

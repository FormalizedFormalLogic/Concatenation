module

public import Concatenation.Semantics.Standard
public import Concatenation.TC.FiniteModel
public import Concatenation.TC.Undecidability
public import Concatenation.WTC.Basic
public import Concatenation.WTC.Pairing

/-!
# $\mathsf{WTC}$ with the editor axiom

Every finite part of $\mathsf{WTC}$ with the unrestricted editor axiom holds in a structure of
strings and formal pairs, whose theory is decidable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of $\mathsf{WTC}$ without the empty string and with the unrestricted editor axiom.
- [HH14, Definition 5, Question 1]
-/
inductive IsWTCEditorAxiom : Sentence ℒ⌢ → Prop
  | wtc : ∀ φ ∈ 𝗪𝗧𝗖, IsWTCEditorAxiom φ
  | editor : IsWTCEditorAxiom “∀ x y z w, x ⌢ y = z ⌢ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ⌢ u = z ∧ y = u ⌢ w) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”

/--
$\mathsf{WTC}$ without the empty string and with the unrestricted editor axiom.
- [HH14, Definition 5, Question 1]
-/
abbrev WTCEditor : Theory ℒ⌢ := Set.ofPred IsWTCEditorAxiom

instance : 𝗪𝗧𝗖 ⪯ WTCEditor := Entailment.WeakerThan.ofSubset IsWTCEditorAxiom.wtc

instance : 𝗘𝗤 ℒ⌢ ⪯ WTCEditor := Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖) inferInstance inferInstance

namespace WTCEditor

/-- Every axiom holds in all but finitely many of the structures `Pairing N`. -/
lemma eventually_models {σ : Sentence ℒ⌢} (hσ : σ ∈ WTCEditor) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧ σ := by
  rcases hσ with ⟨_, hσ⟩ | _
  swap
  · exact .of_forall fun N ↦ by
      simpa [models_iff] using fun (a b c d : Pairing N) ↦ Pairing.editor
  cases hσ
  case equal h =>
    have (N : ℕ) : (Pairing N)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact .of_forall fun N ↦ models_theory_iff.mp (this N) _ h
  case concatAssoc u =>
    filter_upwards [Filter.eventually_ge_atTop u.length] with N hN
    have hu : u.length ≤ N + 1 := by omega
    simpa [models_iff, Pairing.ofFreeSemigroup_eq hu] using
      fun (a b c : Pairing N) ↦ Pairing.append_assoc_of_isSubstring hu
  case editor u =>
    exact .of_forall fun N ↦ by
      simpa [models_iff] using fun (a b c d : Pairing N) h _ ↦ Pairing.editor h
  case concatNeZero =>
    exact .of_forall fun N ↦ by
      simpa [models_iff, Pairing.zero_eq] using
        fun (a b : Pairing N) ↦ Pairing.append_ne_string rfl _
  case concatNeOne =>
    exact .of_forall fun N ↦ by
      simpa [models_iff, Pairing.one_eq] using
        fun (a b : Pairing N) ↦ Pairing.append_ne_string rfl _
  case zeroNeOne => exact .of_forall fun N ↦ by simpa [models_iff] using Pairing.zero_ne_one

/--
Every finite part of $\mathsf{WTC}$ with the editor axiom holds in all but finitely many of the
structures `Pairing N`.
-/
theorem eventually_models_of_finite {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor) (hfin : F.Finite) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧* F :=
  ((Filter.eventually_all_finite hfin).mpr fun _ hσ ↦ eventually_models (hF hσ)).mono
    fun _ h ↦ models_theory_iff.mpr h

/-- No finite part of $\mathsf{WTC}$ with the editor axiom is essentially undecidable. -/
theorem not_essentiallyUndecidable_of_finite {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor)
    (hfin : F.Finite) : ¬F.EssentiallyUndecidable :=
  let ⟨N, _⟩ := (eventually_models_of_finite hF hfin).exists
  Theory.not_essentiallyUndecidable_of_models (Pairing N) (decidable_theory_pairing N)

/--
$\mathsf{WTC}$ with the editor axiom does not interpret $\mathsf{TC}$.
- [HH14, Question 1]
-/
theorem notInterprets_TC : WTCEditor ⋫ 𝗧𝗖 :=
  DirectInterpretation.notInterprets_of_forall_finite_not_essentiallyUndecidable
    finiteAxiomatizable_TC fun _ ↦ not_essentiallyUndecidable_of_finite

end WTCEditor

end FFL.FirstOrder.Concatenation

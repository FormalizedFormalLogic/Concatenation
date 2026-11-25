module

public import Concatenation.D.LeftCancellation
public import Concatenation.TC.Basic
public import Concatenation.TC.Empty
public import Concatenation.ToFoundation.Arithmetic.IQ
public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.Relative
public import Concatenation.WTC.Basic
import Concatenation.OpenProblem

/-!
# Open problems on interpretability between theories of concatenation
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation

/--
Axioms of $\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
inductive IsWTCEmptyEditorAxiom : Sentence ℒ⌢ₑ → Prop
  | wtcEmpty : ∀ φ ∈ 𝗪𝗧𝗖ₑ, IsWTCEmptyEditorAxiom φ
  | editor : IsWTCEmptyEditorAxiom “∀ x y s t, x ⌢ y = s ⌢ t →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”

/--
$\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
abbrev WTCEmptyEditor : Theory ℒ⌢ₑ := Set.ofPred IsWTCEmptyEditorAxiom

instance : 𝗪𝗧𝗖ₑ ⪯ WTCEmptyEditor := Entailment.WeakerThan.ofSubset IsWTCEmptyEditorAxiom.wtcEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ WTCEmptyEditor :=
  Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖ₑ) inferInstance inferInstance

/--
Does $\mathsf{WTC} + \mathrm{TC3}$, with the empty string, interpret $\mathsf{TC}$?
- [HH14, Question 1]
-/
open_problem WTCEmptyEditor_interprets_TCEmpty := Nonempty (WTCEmptyEditor ⊳ 𝗧𝗖ₑ)

/--
Is $\overline{\mathsf{ID}}$ interpretable in $\mathsf{ID}$?
- [Mur24, Open Problem 10]
-/
open_problem ID_interprets_IDLeft := RelativelyInterprets 𝗜𝗗 𝗜𝗗ₗ

/--
Is $\mathsf{IQ}$ interpretable in $\overline{\mathsf{ID}}$?
- [Mur24, Open Problem 15]
-/
open_problem IDLeft_interprets_IQ := RelativelyInterprets 𝗜𝗗ₗ 𝗜𝗤

end Concatenation

/--
A consistent, essentially undecidable, computably enumerable theory with equality.
- [Mur23, §1.1]
-/
structure Theory.IsREEssentiallyUndecidable {L : Language.{0}} [L.Encodable] [L.Primcodable] [L.Eq]
    (T : Theory L) : Prop where
  equal : 𝗘𝗤 L ⪯ T
  re : REPred fun σ : Sentence L ↦ σ ∈ T
  consistent : Entailment.Consistent T
  essentiallyUndecidable : T.EssentiallyUndecidable

/--
Is the lattice of degrees of computable interpretability of the computably enumerable essentially
undecidable theories densely ordered?
- [Mur23, §1.1]
-/
open_problem essentiallyUndecidable_degrees_dense :=
  ∀ (L₁ L₂ : Language.{0}) [L₁.Encodable] [L₁.Primcodable] [L₁.Eq] [L₂.Encodable] [L₂.Primcodable]
    [L₂.Eq] (T : Theory L₁) (U : Theory L₂),
    T.IsREEssentiallyUndecidable → U.IsREEssentiallyUndecidable →
    ComputablyInterprets U T → ¬ComputablyInterprets T U →
    ∃ (L : Language.{0}) (_ : L.Encodable) (_ : L.Primcodable) (_ : L.Eq) (V : Theory L),
      V.IsREEssentiallyUndecidable ∧
      ComputablyInterprets V T ∧ ¬ComputablyInterprets T V ∧
      ComputablyInterprets U V ∧ ¬ComputablyInterprets V U

end FFL.FirstOrder

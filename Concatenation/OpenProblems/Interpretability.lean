module

public import Concatenation.D.LeftCancellation
public import Concatenation.TC.Basic
public import Concatenation.TC.GrowingComma
public import Concatenation.ToFoundation.Arithmetic.IQ
public import Concatenation.ToFoundation.Arithmetic.PeanoMinusSmullyan
public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Concatenation.ToFoundation.Interpretability.Relative
public import Concatenation.ToFoundation.Interpretability.Unrelativized
public import Concatenation.WTC.Basic
import Concatenation.OpenProblem

/-!
# Open problems on interpretability
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

/--
Does $\mathsf{WTC} + \mathrm{TC3}$, with the empty string, interpret $\mathsf{ID}$? The two
theories are those of the cited places.
- [HH14, Definition 1, Question 1]
- [Mur24, §1]
-/
open_problem WTCEmptyEditor_interprets_ID := RelativelyInterprets WTCEmptyEditor 𝗜𝗗

/--
Does $\mathsf{ID}$ interpret $\mathsf{WTC} + \mathrm{TC3}$ with the empty string? The two
theories are those of the cited places.
- [HH14, Definition 1, Question 1]
- [Mur24, §1]
-/
open_problem ID_interprets_WTCEmptyEditor := RelativelyInterprets 𝗜𝗗 WTCEmptyEditor

end Concatenation

/--
Does $\mathsf{PA}^-_{\mathsf{smu}}$ directly interpret the theory of concatenation with growing
commas?
- [Vis24, Open Question 7.1]
-/
open_problem PeanoMinusSmullyan_interprets_TCGrowingComma :=
  UnrelativizedInterprets Arithmetic.PeanoMinusSmullyan Concatenation.TCGrowingComma

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

/--
A computably enumerable theory with equality that has no finite models.
- [KV23, Problem 8.14]
-/
structure Theory.IsREWithoutFiniteModels {L : Language.{0}} [L.Encodable] [L.Primcodable] [L.Eq]
    (T : Theory L) : Prop where
  equal : 𝗘𝗤 L ⪯ T
  re : REPred fun σ : Sentence L ↦ σ ∈ T
  not_hasFiniteModel : ¬T.HasFiniteModel

/--
Are the degrees of interpretability of the computably enumerable theories without finite models
densely ordered?
- [KV23, Problem 8.14]
-/
open_problem noFiniteModel_degrees_dense :=
  ∀ (L₁ L₂ : Language.{0}) [L₁.Finite] [L₁.Encodable] [L₁.Primcodable] [L₁.Eq]
    [L₂.Finite] [L₂.Encodable] [L₂.Primcodable] [L₂.Eq] (T : Theory L₁) (U : Theory L₂),
    T.IsREWithoutFiniteModels → U.IsREWithoutFiniteModels →
    RelativelyInterprets U T → ¬RelativelyInterprets T U →
    ∃ (L : Language.{0}) (_ : L.Finite) (_ : L.Encodable) (_ : L.Primcodable) (_ : L.Eq)
      (V : Theory L), V.IsREWithoutFiniteModels ∧
      RelativelyInterprets V T ∧ ¬RelativelyInterprets T V ∧
      RelativelyInterprets U V ∧ ¬RelativelyInterprets V U

end FFL.FirstOrder

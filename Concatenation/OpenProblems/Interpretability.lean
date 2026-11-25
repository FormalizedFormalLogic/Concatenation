module

public import Concatenation.D.LeftCancellation
public import Concatenation.TC.Basic
public import Concatenation.TC.GrowingComma
public import Concatenation.ToFoundation.Arithmetic.IQ
public import Concatenation.ToFoundation.Arithmetic.PeanoMinusSmullyan
public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.Interpretability.Relative
public import Concatenation.ToFoundation.Interpretability.Unrelativized
import Concatenation.OpenProblem

/-!
# Open problems on interpretability
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation

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

end FFL.FirstOrder

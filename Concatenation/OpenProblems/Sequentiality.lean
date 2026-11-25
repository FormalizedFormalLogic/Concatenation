module

public import Concatenation.SetTheory.Sequential
public import Concatenation.ToFoundation.Interpretability.Relative
public import Foundation.FirstOrder.Arithmetic.Q.Basic
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
import Concatenation.OpenProblem

/-!
# Open problems on sequential theories
-/

@[expose] public section

namespace FFL.FirstOrder

/--
A computably enumerable theory in the language of arithmetic that extends $\mathsf{Q}$.
- [Vis08, §2, §3.3.1]
-/
structure ArithmeticTheory.IsREExtensionOfQ (T : ArithmeticTheory) : Prop where
  weakerThan : 𝗤 ⪯ T
  re : REPred fun σ : ArithmeticSentence ↦ σ ∈ T

/--
Is there a sequential arithmetical theory that is minimal with respect to direct interpretability?
- [Vis08, Question 1]
-/
open_problem exists_minimal_sequential_arithmetical :=
  ∃ (T : ArithmeticTheory) (_ : 𝗘𝗤 ℒₒᵣ ⪯ T), T.IsREExtensionOfQ ∧ T.Sequential ∧
    ∀ (U : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ U], U.IsREExtensionOfQ → U.Sequential →
      UnrelativizedInterprets T U → UnrelativizedInterprets U T

/--
`U` is relatively interpretable in `T` in one dimension, possibly with a nonabsolute equality.
- [Vis08, §2.1]
-/
def OneDimensionallyInterprets {L₁ L₂ : Language.{0}} [L₁.Eq] [L₂.Eq] (T : Theory L₁)
    (U : Theory L₂) : Prop := ∃ τ : RelativeTranslation L₁ L₂, τ.dim = 1 ∧ τ.Interprets T U

/--
Is every sequential theory mutually interpretable with an arithmetical theory?
- [Vis08, Question 2]
-/
open_problem exists_arithmetical_mutuallyInterpretable_of_sequential :=
  ∀ (L : Language.{0}) [L.Finite] [L.Encodable] [L.Primcodable] [L.Eq] (T : Theory L) [𝗘𝗤 L ⪯ T],
    REPred (fun σ : Sentence L ↦ σ ∈ T) → T.Sequential →
    ∃ U : ArithmeticTheory, U.IsREExtensionOfQ ∧
      OneDimensionallyInterprets T U ∧ OneDimensionallyInterprets U T

end FFL.FirstOrder

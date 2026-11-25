module

public import Concatenation.ToFoundation.TuringPersistence
public import Foundation.FirstOrder.LK.Eq
import Concatenation.OpenProblem

/-!
# An open problem on Turing-persistent theories
-/

@[expose] public section

open scoped Computability

namespace FFL.FirstOrder

/--
Are there undecidable essentially Turing-persistent theories of a Turing degree other than
$\mathbf{0}'$?
- [PMV23, Open Question 4.11]
- [Mur23, Open Problem 226]
-/
open_problem exists_essentiallyTuringPersistent_incomplete :=
  ∃ (L : Language.{0}) (_ : L.Finite) (_ : L.Encodable) (_ : L.Primcodable) (_ : L.Eq)
    (T : Theory L), 𝗘𝗤 L ⪯ T ∧ T.EssentiallyTuringPersistent ∧ Entailment.Undecidable T ∧
      ∃ p : ℕ → Prop, REPred p ∧ ¬oracle p ≤ᵀ T.oracle

end FFL.FirstOrder

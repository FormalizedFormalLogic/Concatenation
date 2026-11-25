module

public import Concatenation.OpenProblems.NotationInduction
import Concatenation.OpenProblem

/-!
# An open problem on completions of restricted complexity
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Arithmetic

/--
Is there a consistent completion of $\mathsf{I}\Delta_0$ axiomatized by $\Sigma_n$ sentences for
some $n$?
- [ELV25, Open Question 8.1]
-/
open_problem exists_restricted_completion_IDelta0 :=
  ∃ (n : ℕ) (A : Set ArithmeticSentence), (∀ σ ∈ A, ℬ[<, ℒₒᵣ].BlockHierarchy 𝚺 n σ) ∧
    𝗜𝚺₀ ⪯ 𝗘𝗤 ℒₒᵣ ∪ A ∧ Entailment.Consistent (𝗘𝗤 ℒₒᵣ ∪ A) ∧ Entailment.Complete (𝗘𝗤 ℒₒᵣ ∪ A)

end Arithmetic

end FFL.FirstOrder

module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Sequence.Basic
public import Foundation.FirstOrder.Arithmetic.R0.Basic
import Concatenation.OpenProblem

/-!
# Open problems on theories of sequences
-/

@[expose] public section

namespace FFL.FirstOrder

/--
`T` is sequential: it defines a membership relation satisfying the axioms of adjunctive set theory
on its whole domain.
- [KM24, §1, §3]
-/
def Theory.Sequential {L : Language} [L.Eq] (T : Theory L) : Prop :=
  ∃ φ : Semisentence L 2,
    T ⊢ “∃ y, ∀ x, ¬!φ x y” ∧ T ⊢ “∀ x y, ∃ z, ∀ u, !φ u z ↔ !φ u x ∨ u = y”

namespace Sequence

/--
Is $\mathsf{WSeq}$ mutually interpretable with $\mathsf{R}_0$?
- [KM24, §2]
-/
open_problem WSeq_mutuallyInterpretable_R0 := Nonempty (𝗪𝗦𝗲𝗾 ⋈ 𝗥₀)

/--
Is $\mathsf{Seq}^*$ sequential?
- [KM24, §4.2, Problem 10]
-/
open_problem SeqStar_sequential := Theory.Sequential 𝗦𝗲𝗾⋆

end Sequence

end FFL.FirstOrder

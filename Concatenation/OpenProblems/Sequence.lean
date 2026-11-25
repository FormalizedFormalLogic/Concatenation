module

public import Concatenation.Seq.Editor
import Concatenation.OpenProblem

/-!
# An open problem on theories of sequences
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
Is $\mathsf{Seq}^*$ sequential?
- [KM24, §4.2, Problem 10]
-/
open_problem SeqStar_sequential := Theory.Sequential 𝗦𝗲𝗾⋆

end Sequence

end FFL.FirstOrder

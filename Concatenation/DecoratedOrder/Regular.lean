module

public import Concatenation.DecoratedOrder.Basic
import Concatenation.OpenProblem

/-!
# Regular concrete representations
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Does every concatenation structure that has a concrete representation also have a regular one?
- [CPRUV10, §6]
-/
open_problem exists_regular_representation :=
  ∀ (M : Type) [Monoid M], IsConcatenationMonoid M →
    (∃ (A : Type) (ρ : M → DecoratedOrder A), IsRepresentation ρ) →
    ∃ (A : Type) (ρ : M → DecoratedOrder A), IsRepresentation ρ ∧ IsRegular ρ

end FFL.FirstOrder.Concatenation

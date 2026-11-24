module

public import Concatenation.Language
public import Concatenation.ToMathlib.FreeSemigroup

/-!
# Canonical terms for binary strings
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {L : Language} [L.Zero] [L.One] [L.Concat] {ξ : Type*} {n : ℕ}

/-- The constant denoting a letter: `false` is $0$ and `true` is $1$. -/
def letter : Bool → Semiterm L ξ n
  | false => ‘!!(op(0).const)’
  | true => ‘!!(op(1).const)’

/--
The canonical term of a nonempty binary string, associated to the left.
- [Mur22, §2]
-/
def biteral (α : FreeSemigroup Bool) : Semiterm L ξ n :=
  α.tail.foldl (fun t b ↦ ‘!!t ⌢ !!(letter b)’) (letter α.head)

/--
The canonical term of a possibly empty binary string.
- [HH14, §2]
-/
def biteralEmpty [L.Star] : List Bool → Semiterm L ξ n
  | [] => ‘⋆’
  | b :: l => biteral ⟨b, l⟩

variable [L.Eq]

/-- `x` is one of the strings in the list. -/
def isOneOf (l : List (FreeSemigroup Bool)) : Semisentence L 1 :=
  l.disj' fun γ ↦ “x. x = !!(biteral γ)”

/--
`x` is a substring of `y`.
- [HH14, §2]
- [Mur22, §1]
-/
def isSubstring : Semisentence L 2 :=
  “x y. x = y ∨ ∃ k l, k ⌢ x = y ∨ x ⌢ l = y ∨ (k ⌢ x) ⌢ l = y ∨ k ⌢ (x ⌢ l) = y”

end FFL.FirstOrder.Concatenation

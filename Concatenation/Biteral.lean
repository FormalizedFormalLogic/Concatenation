module

public import Concatenation.Language
public import Concatenation.ToMathlib.FreeSemigroup
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# Canonical terms for strings
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {L : Language} [L.Concat] {α ξ : Type*} {n : ℕ}

/-- The term of a nonempty string whose letters are denoted by `f`, associated to the left. -/
def stringTerm (f : α → Semiterm L ξ n) (x : FreeSemigroup α) : Semiterm L ξ n :=
  x.tail.foldl (fun t a ↦ ‘!!t ⌢ !!(f a)’) (f x.head)

variable [L.Zero] [L.One]

/-- The constant denoting a letter: `false` is $0$ and `true` is $1$. -/
def letter : Bool → Semiterm L ξ n
  | false => ‘!!(op(0).const)’
  | true => ‘!!(op(1).const)’

/--
The canonical term of a nonempty binary string, associated to the left.
- [Mur22, §2]
-/
def biteral (x : FreeSemigroup Bool) : Semiterm L ξ n := stringTerm letter x

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

/-- The substring relation as an operator. -/
def substringOperator (L : Language) [L.Eq] [L.Concat] : Semiformula.Operator L 2 := ⟨isSubstring⟩

/--
Quantifiers bounded by the substring relation. `ℬ[⊑, L].PrenexHierarchy 𝚺 0` is the class
of $\Sigma_0$ formulas, and `ℬ[⊑, L].PrenexHierarchy 𝚺 1` the class of $\Sigma_1$ formulas.
- [Hor11, §3]
- [Hor12, §3]
-/
def substringBounding (L : Language) [L.Eq] [L.Concat] : Bounding L := ⟨{substringOperator L}⟩

@[inherit_doc]
scoped notation "ℬ[⊑, " L "]" => substringBounding L

omit [L.Zero] [L.One] in
@[simp]
lemma mem_substringBounding_iff {R : Semiformula.Operator L 2} :
    R ∈ ℬ[⊑, L] ↔ R = substringOperator L := Iff.rfl

end FFL.FirstOrder.Concatenation

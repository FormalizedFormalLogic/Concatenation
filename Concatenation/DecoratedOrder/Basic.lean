module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Decorated linear orders

Representations of monoids by decorated linear orders with concatenation.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
An `A`-decorated linear order, possibly empty.
- [CPRUV10, §1]
-/
structure DecoratedOrder (A : Type) where
  carrier : Type
  [linearOrder : LinearOrder carrier]
  decoration : carrier → A

namespace DecoratedOrder

attribute [instance] linearOrder

variable {A : Type}

/--
`X` and `Y` have the same decorated order type.
- [CPRUV10, §1]
-/
def Isomorphic (X Y : DecoratedOrder A) : Prop :=
  ∃ e : X.carrier ≃o Y.carrier, ∀ x, Y.decoration (e x) = X.decoration x

/--
The concatenation of decorated linear orders.
- [CPRUV10, §1]
-/
def concat (X Y : DecoratedOrder A) : DecoratedOrder A where
  carrier := X.carrier ⊕ₗ Y.carrier
  decoration x := Sum.elim X.decoration Y.decoration (ofLex x)

/-- The restriction of a decorated linear order. -/
def restrict (X : DecoratedOrder A) (s : Set X.carrier) : DecoratedOrder A where
  carrier := s
  decoration x := X.decoration x

end DecoratedOrder

/--
Monoids satisfying the editor axiom and the axiom that $xyz = y$ only if $x$ and $z$ are the unit.
- [CPRUV10, §6]
-/
structure IsConcatenationMonoid (M : Type) [Monoid M] : Prop where
  editor (x y u v : M) : x * y = u * v → ∃ w, (x * w = u ∧ y = w * v) ∨ (x = u * w ∧ w * y = v)
  eq_one_of_mul_mul_eq (x y z : M) : x * y * z = y → x = 1 ∧ z = 1

section

variable {M : Type} [Monoid M] {A : Type}

/--
`ρ` is a concrete representation: up to isomorphism, it embeds the monoid into the decorated linear
orders with concatenation.
- [CPRUV10, §1, §6]
-/
structure IsRepresentation (ρ : M → DecoratedOrder A) : Prop where
  map_mul (x y : M) : (ρ (x * y)).Isomorphic ((ρ x).concat (ρ y))
  injective (x y : M) : (ρ x).Isomorphic (ρ y) → x = y

/--
`ρ` is regular: a decorated linear order that represents $xy$ splits in exactly one way into parts
isomorphic to those that represent $x$ and $y$.
- [CPRUV10, Definition 6.4]
-/
def IsRegular (ρ : M → DecoratedOrder A) : Prop :=
  ∀ x y : M, ∃! I : LowerSet (ρ (x * y)).carrier,
    ((ρ (x * y)).restrict I).Isomorphic (ρ x) ∧ ((ρ (x * y)).restrict (I : Set _)ᶜ).Isomorphic (ρ y)

end

end FFL.FirstOrder.Concatenation

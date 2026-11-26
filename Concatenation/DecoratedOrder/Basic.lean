module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Decorated linear orders

Decorated linear orders and their isomorphism types under concatenation, and representations of
monoids by decorated linear orders.
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

variable {X Y Z W : DecoratedOrder A}

lemma Isomorphic.refl (X : DecoratedOrder A) : X.Isomorphic X := ⟨.refl _, fun _ ↦ rfl⟩

lemma Isomorphic.symm : X.Isomorphic Y → Y.Isomorphic X
  | ⟨e, h⟩ => ⟨e.symm, fun y ↦ by simp [← h]⟩

lemma Isomorphic.trans : X.Isomorphic Y → Y.Isomorphic Z → X.Isomorphic Z
  | ⟨e, h⟩, ⟨e', h'⟩ => ⟨e.trans e', fun x ↦ by simp [h, h']⟩

lemma Isomorphic.concat : X.Isomorphic Y → Z.Isomorphic W → (X.concat Z).Isomorphic (Y.concat W)
  | ⟨e, h⟩, ⟨e', h'⟩ => ⟨e.sumLexCongr e', by rintro (x | x); exacts [h x, h' x]⟩

instance setoid (A : Type) : Setoid (DecoratedOrder A) where
  r := Isomorphic
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

/-- The empty decorated linear order. -/
abbrev empty (A : Type) : DecoratedOrder A where
  carrier := Empty
  decoration := Empty.elim

/-- The order `X` with every point decorated by `a`. -/
abbrev const (a : A) (X : Type) [LinearOrder X] : DecoratedOrder A where
  carrier := X
  decoration _ := a

lemma const_isomorphic (a : A) {X Y : Type} [LinearOrder X] [LinearOrder Y] (e : X ≃o Y) :
    (const a X).Isomorphic (const a Y) := ⟨e, fun _ ↦ rfl⟩

lemma const_sum (a : A) (X Y : Type) [LinearOrder X] [LinearOrder Y] :
    (const a (X ⊕ₗ Y)).Isomorphic ((const a X).concat (const a Y)) :=
  ⟨.refl _, by rintro (x | x) <;> rfl⟩

lemma isomorphic_empty_iff : X.Isomorphic (empty A) ↔ IsEmpty X.carrier :=
  ⟨fun ⟨e, _⟩ ↦ e.toEquiv.isEmpty, fun _ ↦ ⟨.ofIsEmpty _ _, isEmptyElim⟩⟩

end DecoratedOrder

/--
The isomorphism classes of `A`-decorated linear orders.
- [Vis09, Note 2]
- [CPRUV10, §1]
-/
def DecoratedOrderType (A : Type) : Type 1 := Quotient (DecoratedOrder.setoid A)

namespace DecoratedOrderType

open DecoratedOrder

variable {A : Type} {X Y : DecoratedOrder A} {x : DecoratedOrderType A} {a b : A}

/-- The type of a decorated linear order. -/
def mk (X : DecoratedOrder A) : DecoratedOrderType A := Quotient.mk _ X

lemma mk_eq_mk : mk X = mk Y ↔ X.Isomorphic Y := Quotient.eq

lemma mk_surjective : Function.Surjective (mk (A := A)) := Quotient.mk_surjective

/-- Concatenation of decorated linear order types. -/
instance : Monoid (DecoratedOrderType A) where
  one := mk (empty A)
  mul := Quotient.map₂ concat fun _ _ h _ _ h' ↦ h.concat h'
  mul_assoc := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact mk_eq_mk.mpr ⟨.sumLexAssoc _ _ _, by rintro ((x | x) | x) <;> rfl⟩
  one_mul := by
    rintro ⟨X⟩
    exact mk_eq_mk.mpr ⟨.emptySumLex (β := Empty), by rintro (x | x); exacts [x.elim, rfl]⟩
  mul_one := by
    rintro ⟨X⟩
    exact mk_eq_mk.mpr ⟨.sumLexEmpty (β := Empty), by rintro (x | x); exacts [rfl, x.elim]⟩

lemma mk_mul_mk : mk X * mk Y = mk (X.concat Y) := rfl

lemma mk_eq_one_iff : mk X = 1 ↔ IsEmpty X.carrier := mk_eq_mk.trans isomorphic_empty_iff

end DecoratedOrderType

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

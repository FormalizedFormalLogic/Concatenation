module

public import Concatenation.DecoratedOrder.Basic
public import Concatenation.ToMathlib.NonemptyLowerSet
public import Mathlib.Order.Hom.Lex

/-!
# Tally length functions on decorated linear order types

Decorated linear order types with concatenation have several tally length functions.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section

variable {M : Type*} [Monoid M]

/--
`x` is an atom: it is not the unit, and is not the product of two elements other than the unit.
- [Vis09, §3]
-/
structure IsAtomic (x : M) : Prop where
  ne_one : x ≠ 1
  eq_one_or_eq_one {y z : M} : x = y * z → y = 1 ∨ z = 1

/--
`f` is a tally length function for `a`.
- [Vis09, Remark 4.2]
-/
structure IsTallyLength (a : M) (f : M → M) : Prop where
  map_one : f 1 = 1
  map_atom {x : M} : IsAtomic x → f x = a
  map_mul (x y : M) : f (x * y) = f x * f y

end

namespace DecoratedOrderType

open DecoratedOrder

variable {A : Type} {X Y : DecoratedOrder A} {x : DecoratedOrderType A} {a b : A}

/-- The one-point type decorated by `a`. -/
def atom (a : A) : DecoratedOrderType A := mk (const a Unit)

lemma isAtomic_atom : IsAtomic (atom a) where
  ne_one h := (mk_eq_one_iff.mp h).elim ()
  eq_one_or_eq_one {y z} h := by
    obtain ⟨Y, rfl⟩ := mk_surjective y
    obtain ⟨Z, rfl⟩ := mk_surjective z
    obtain ⟨e, _⟩ := mk_eq_mk.mp h
    simp only [mk_eq_one_iff]
    by_contra! hn
    obtain ⟨⟨y⟩, ⟨z⟩⟩ := hn
    have h₁ := e.symm.injective (a₁ := toLex (.inl y)) (a₂ := toLex (.inr z)) rfl
    cases h₁

lemma exists_eq_atom (hx : IsAtomic x) : ∃ a, x = atom a := by
  obtain ⟨X, rfl⟩ := mk_surjective x
  obtain ⟨p⟩ : Nonempty X.carrier := not_isEmpty_iff.mp <| mk_eq_one_iff.not.mp hx.ne_one
  have hmax (q : X.carrier) : IsEmpty (Set.Ioi q) := by
    have h₁ : mk X = mk (X.restrict (Set.Iic q)) * mk (X.restrict (Set.Ioi q)) :=
      (mk_eq_mk.mpr ⟨.sumLexIicIoi q, by rintro (x | x) <;> rfl⟩).symm
    exact mk_eq_one_iff.mp <| (hx.eq_one_or_eq_one h₁).resolve_left fun h ↦
      (mk_eq_one_iff.mp h).elim ⟨q, le_refl q⟩
  have hle (q r : X.carrier) : q ≤ r := le_of_not_gt fun h ↦ (hmax r).elim ⟨q, h⟩
  have : Unique X.carrier := ⟨⟨p⟩, fun q ↦ le_antisymm (hle _ _) (hle _ _)⟩
  use X.decoration p
  exact mk_eq_mk.mpr ⟨.ofUnique _ _, fun q ↦ congrArg _ <| le_antisymm (hle p q) (hle q p)⟩

/-- The atoms are the one-point types. -/
lemma isAtomic_iff : IsAtomic x ↔ ∃ a, x = atom a :=
  ⟨exists_eq_atom, by rintro ⟨a, rfl⟩; exact isAtomic_atom⟩

/--
The standard tally length function: every decoration is replaced by `a`.
- [Vis09, Remark 4.2]
-/
def recolor (a : A) : DecoratedOrderType A → DecoratedOrderType A :=
  Quotient.map (fun X ↦ const a X.carrier) fun _ _ ⟨e, _⟩ ↦ const_isomorphic a e

lemma recolor_mk : recolor a (mk X) = mk (const a X.carrier) := rfl

/--
The type of the nonempty lower sets, all decorated by `a`. A nonempty lower set is either
$\{y \mid y \le x\}$ for a point $x$ or has no greatest element, so that this recolours every point
by `a` and inserts a further point at each cut whose lower part is nonempty and has no greatest
element.
-/
noncomputable def lowerSets (a : A) : DecoratedOrderType A → DecoratedOrderType A :=
  Quotient.map (fun X ↦ const a (NonemptyLowerSet X.carrier)) fun _ _ ⟨e, _⟩ ↦
    const_isomorphic a (NonemptyLowerSet.congr e)

lemma lowerSets_mk : lowerSets a (mk X) = mk (const a (NonemptyLowerSet X.carrier)) := rfl

/--
Replacing every decoration by `a` is a tally length function.
- [Vis09, Remark 4.2]
-/
theorem isTallyLength_recolor (a : A) : IsTallyLength (atom a) (recolor a) where
  map_one := mk_eq_one_iff.mpr (inferInstanceAs (IsEmpty Empty))
  map_atom hx := by
    obtain ⟨b, rfl⟩ := exists_eq_atom hx
    rfl
  map_mul := by
    rintro ⟨X⟩ ⟨Y⟩
    exact mk_eq_mk.mpr <| const_sum a X.carrier Y.carrier

/-- `lowerSets a` is a tally length function. -/
theorem isTallyLength_lowerSets (a : A) : IsTallyLength (atom a) (lowerSets a) where
  map_one := mk_eq_one_iff.mpr (inferInstanceAs (IsEmpty (NonemptyLowerSet Empty)))
  map_atom hx := by
    obtain ⟨b, rfl⟩ := exists_eq_atom hx
    have : Unique (NonemptyLowerSet Unit) :=
      ⟨⟨Classical.arbitrary _⟩, fun _ ↦ Subsingleton.elim _ _⟩
    exact mk_eq_mk.mpr <| const_isomorphic a (.ofUnique _ _)
  map_mul := by
    rintro ⟨X⟩ ⟨Y⟩
    exact mk_eq_mk.mpr <| (const_isomorphic a NonemptyLowerSet.sumLex.symm).trans <|
      const_sum a (NonemptyLowerSet X.carrier) (NonemptyLowerSet Y.carrier)

/-- The two tally length functions differ at $\omega$. -/
lemma recolor_ne_lowerSets (a : A) : recolor a ≠ lowerSets a := by
  intro h
  obtain ⟨e, _⟩ := mk_eq_mk.mp <| congrFun h (mk (const a ℕ))
  let n : ℕ := e.symm (⟨⊤, Set.univ_nonempty⟩ : NonemptyLowerSet ℕ)
  have h₁ : e (n + 1 : ℕ) ≤ e n := (le_top : _ ≤ (⊤ : LowerSet ℕ)).trans_eq (by simp [n])
  exact absurd (e.le_iff_le.mp h₁) (Nat.not_succ_le_self n)

/--
The tally length function on decorated linear order types is not unique, which answers a question
of Visser.
- [Vis09, Remark 4.2]
-/
theorem exists_isTallyLength_ne (a : A) : ∃ f g : DecoratedOrderType A → DecoratedOrderType A,
    IsTallyLength (atom a) f ∧ IsTallyLength (atom a) g ∧ f ≠ g :=
  ⟨recolor a, lowerSets a, isTallyLength_recolor a, isTallyLength_lowerSets a,
    recolor_ne_lowerSets a⟩

end DecoratedOrderType

end FFL.FirstOrder.Concatenation

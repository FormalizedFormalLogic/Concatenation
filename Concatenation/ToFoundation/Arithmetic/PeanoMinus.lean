module

public import AlphaCentauri.Interpretability.Basic
public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Mathlib.Tactic.Ring

/-!
# The theory $\mathsf{PA}^-$

An injective pairing in $\mathsf{PA}^-$, and the interpretation of $\mathsf{PA}^-$ in $\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {x y x' y' z : V}

/-- The pair $(x + y)^2 + x$ of `x` and `y`. -/
def squarePair (x y : V) : V := (x + y) * (x + y) + x

/-- `z` is the pair $(x + y)^2 + x$ of `x` and `y`. -/
def squarePairDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “z x y. z = (x + y) * (x + y) + x”

instance squarePair_defined : 𝚺ᴬ₀-Function₂[V] squarePair via squarePairDef := .mk fun v ↦ by
  simp [squarePairDef, squarePair]

instance squarePair_definable : 𝚺ᴬ₀-Function₂[V] squarePair := squarePair_defined.to_definable

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

private lemma squarePair_lt (h : x + y < x' + y') : squarePair x y < squarePair x' y' := by
  have h₁ : x + y + 1 ≤ x' + y' := by
    obtain ⟨z, hz, h₂⟩ := lt_iff_exists_add.mp h
    rw [h₂]
    gcongr
    exact one_le_of_zero_lt z hz
  calc
    squarePair x y ≤ (x + y) * (x + y) + (x + y) := by simp [squarePair]
    _ < (x + y + 1) * (x + y + 1) := by
      have : (x + y + 1) * (x + y + 1) = (x + y) * (x + y) + (x + y) + (x + y + 1) := by ring
      rw [this]
      exact lt_add_of_pos_right _ <| by simp
    _ ≤ (x' + y') * (x' + y') := by gcongr
    _ ≤ squarePair x' y' := by simp [squarePair]

@[simp, grind =]
lemma squarePair_inj : squarePair x y = squarePair x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    rcases lt_trichotomy (x + y) (x' + y') with h₁ | h₁ | h₁
    · exact absurd h (squarePair_lt h₁).ne
    · obtain rfl : x = x' := by simpa [squarePair, h₁] using h
      exact ⟨rfl, by simpa using h₁⟩
    · exact absurd h (squarePair_lt h₁).ne'
  · rintro ⟨rfl, rfl⟩
    rfl

end FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {a b c d x y z : V}

/--
Addition of `x` on the right is associative, commutes with the successor on the left, has `0` as
a left unit, and is cancellable.
- [Mur24, §6, Theorem 24]
-/
@[mk_iff]
structure IsPreadditive (x : V) : Prop where
  add_assoc : ∀ u v, u + v + x = u + (v + x)
  zero_add : 0 + x = x
  add_one_add : ∀ u, u + 1 + x = u + x + 1
  add_right_cancel : ∀ u v, u + x = v + x → u = v

/--
Addition of `x` on the right is associative, commutes with the successor on the left, has `0` as
a left unit, and is cancellable.
- [Mur24, §6, Theorem 24]
-/
def isPreadditiveDef : 𝚷ᴬ₁.Semisentence 1 := .mkPi
  “x. (∀ u v, u + v + x = u + (v + x)) ∧ 0 + x = x ∧ (∀ u, u + 1 + x = u + x + 1) ∧
    (∀ u v, u + x = v + x → u = v)”

instance isPreadditive_defined : 𝚷ᴬ₁-Predicate[V] IsPreadditive via isPreadditiveDef :=
  .mk fun v ↦ by simp [isPreadditiveDef, isPreadditive_iff]

instance isPreadditive_definable : 𝚷ᴬ₁-Predicate[V] IsPreadditive :=
  isPreadditive_defined.to_definable

/--
`x` is preadditive, and commutes and is comparable with every preadditive element.
- [Mur24, §6, Theorem 24]
-/
@[mk_iff]
structure IsAdditive (x : V) : Prop extends IsPreadditive x where
  add_comm : ∀ u, IsPreadditive u → u + x = x + u
  comparable : ∀ u, IsPreadditive u → ∃ z, z + x = u ∨ z + u = x

/--
`x` is preadditive, and commutes and is comparable with every preadditive element.
- [Mur24, §6, Theorem 24]
-/
def isAdditiveDef : ArithmeticSemisentence 1 :=
  “x. !isPreadditiveDef x ∧ (∀ u, !isPreadditiveDef u → u + x = x + u) ∧
    (∀ u, !isPreadditiveDef u → ∃ z, z + x = u ∨ z + u = x)”

instance isAdditive_defined : ℒₒᵣ-predicate[V] IsAdditive via isAdditiveDef :=
  ⟨fun v ↦ by simp [isAdditiveDef, isAdditive_iff]⟩

instance isAdditive_definable : ℒₒᵣ-predicate[V] IsAdditive := isAdditive_defined.to_definable

/--
`x` is additive, and multiplication by `x` on the right preserves the additive elements,
distributes over their sums from both sides, and has `0` and `1` as a left zero and a left unit.
- [Mur24, §6, Theorem 24]
-/
@[mk_iff]
structure IsPremultiplicative (x : V) : Prop extends IsAdditive x where
  isAdditive_mul : ∀ u, IsAdditive u → IsAdditive (u * x)
  mul_add : ∀ u v, IsAdditive u → u * (v + x) = u * v + u * x
  add_mul : ∀ u v, IsAdditive u → IsAdditive v → (u + v) * x = u * x + v * x
  zero_mul : 0 * x = 0
  one_mul : 1 * x = x

/--
`x` is additive, and multiplication by `x` on the right preserves the additive elements,
distributes over their sums from both sides, and has `0` and `1` as a left zero and a left unit.
- [Mur24, §6, Theorem 24]
-/
def isPremultiplicativeDef : ArithmeticSemisentence 1 :=
  “x. !isAdditiveDef x ∧ (∀ u, !isAdditiveDef u → !isAdditiveDef (u * x)) ∧
    (∀ u v, !isAdditiveDef u → u * (v + x) = u * v + u * x) ∧
    (∀ u v, !isAdditiveDef u → !isAdditiveDef v → (u + v) * x = u * x + v * x) ∧
    0 * x = 0 ∧ 1 * x = x”

instance isPremultiplicative_defined : ℒₒᵣ-predicate[V] IsPremultiplicative
    via isPremultiplicativeDef :=
  ⟨fun v ↦ by simp [isPremultiplicativeDef, isPremultiplicative_iff]⟩

instance isPremultiplicative_definable : ℒₒᵣ-predicate[V] IsPremultiplicative :=
  isPremultiplicative_defined.to_definable

/--
Multiplication by `x` on the right is associative.
- [Mur24, §6, Theorem 24]
-/
def IsMulAssoc (x : V) : Prop :=
  ∀ u v, IsAdditive u → IsPremultiplicative v → u * v * x = u * (v * x)

/--
Multiplication by `x` on the right is associative.
- [Mur24, §6, Theorem 24]
-/
def isMulAssocDef : ArithmeticSemisentence 1 :=
  “x. ∀ u v, !isAdditiveDef u → !isPremultiplicativeDef v → u * v * x = u * (v * x)”

instance isMulAssoc_defined : ℒₒᵣ-predicate[V] IsMulAssoc via isMulAssocDef :=
  ⟨fun v ↦ by simp [isMulAssocDef, IsMulAssoc]⟩

instance isMulAssoc_definable : ℒₒᵣ-predicate[V] IsMulAssoc := isMulAssoc_defined.to_definable

/--
`x` is premultiplicative, and multiplication by `x` on the right is associative and commutative,
and preserves the premultiplicative elements.
- [Mur24, §6, Theorem 24]
-/
@[mk_iff]
structure IsMultiplicative (x : V) : Prop extends IsPremultiplicative x where
  mul_assoc : IsMulAssoc x
  mul_comm : ∀ u, IsPremultiplicative u → IsMulAssoc u → u * x = x * u
  isPremultiplicative_mul : ∀ u, IsPremultiplicative u → IsPremultiplicative (u * x)

/--
`x` is premultiplicative, and multiplication by `x` on the right is associative and commutative,
and preserves the premultiplicative elements.
- [Mur24, §6, Theorem 24]
-/
def isMultiplicativeDef : ArithmeticSemisentence 1 :=
  “x. !isPremultiplicativeDef x ∧ !isMulAssocDef x ∧
    (∀ u, !isPremultiplicativeDef u → !isMulAssocDef u → u * x = x * u) ∧
    (∀ u, !isPremultiplicativeDef u → !isPremultiplicativeDef (u * x))”

instance isMultiplicative_defined : ℒₒᵣ-predicate[V] IsMultiplicative via isMultiplicativeDef :=
  ⟨fun v ↦ by simp [isMultiplicativeDef, isMultiplicative_iff]⟩

instance isMultiplicative_definable : ℒₒᵣ-predicate[V] IsMultiplicative :=
  isMultiplicative_defined.to_definable

/--
`y` is the sum of a successor and `x`.
- [Mur24, §6, Theorem 24]
-/
def LeftLT (x y : V) : Prop := ∃ z, z + 1 + x = y

/--
`y` is the sum of a successor and `x`.
- [Mur24, §6, Theorem 24]
-/
def leftLTDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “x y. ∃ z, z + 1 + x = y”

instance leftLT_defined : 𝚺ᴬ₁-Relation[V] LeftLT via leftLTDef := .mk fun v ↦ by
  simp [leftLTDef, LeftLT]

instance leftLT_definable : 𝚺ᴬ₁-Relation[V] LeftLT := leftLT_defined.to_definable

namespace IsPreadditive

protected lemma add (hx : IsPreadditive x) (hy : IsPreadditive y) : IsPreadditive (x + y) where
  add_assoc u v := by simp only [← hy.add_assoc, hx.add_assoc]
  zero_add := by rw [← hy.add_assoc, hx.zero_add]
  add_one_add u := by simp only [← hy.add_assoc, hx.add_one_add, hy.add_one_add]
  add_right_cancel u v h := by
    rw [← hy.add_assoc, ← hy.add_assoc] at h
    exact hx.add_right_cancel _ _ <| hy.add_right_cancel _ _ h

lemma of_add (hx : IsPreadditive x) (h : IsPreadditive (z + x)) : IsPreadditive z where
  add_assoc u v := hx.add_right_cancel _ _ <| by
    simp only [hx.add_assoc]
    rw [← hx.add_assoc v z, hx.add_assoc, h.add_assoc]
  zero_add := hx.add_right_cancel _ _ <| by rw [hx.add_assoc, h.zero_add]
  add_one_add u := hx.add_right_cancel _ _ <| by
    rw [hx.add_assoc, h.add_one_add, hx.add_one_add, hx.add_assoc]
  add_right_cancel u v huv := h.add_right_cancel _ _ <| by
    rw [← hx.add_assoc, ← hx.add_assoc, huv]

end IsPreadditive

namespace IsAdditive

protected lemma add (hx : IsAdditive x) (hy : IsAdditive y) : IsAdditive (x + y) where
  toIsPreadditive := hx.toIsPreadditive.add hy.toIsPreadditive
  add_comm u hu := by
    rw [← hy.add_assoc, hx.add_comm u hu, hy.add_assoc, hy.add_comm u hu, hu.add_assoc]
  comparable u hu := by
    obtain ⟨w, rfl | rfl⟩ := hy.comparable u hu
    · obtain ⟨v, rfl | rfl⟩ := hx.comparable w <| hy.toIsPreadditive.of_add hu <;>
        use v <;> simp [hy.add_assoc]
    · use x + w
      simp [hu.add_assoc]

lemma of_add (hx : IsAdditive x) (h : IsAdditive (z + x)) : IsAdditive z where
  toIsPreadditive := hx.toIsPreadditive.of_add h.toIsPreadditive
  add_comm u hu := hx.add_right_cancel _ _ <| by
    rw [hx.add_assoc, hx.add_assoc, hx.add_comm u hu, ← hu.add_assoc, h.add_comm u hu]
  comparable u hu := by
    obtain ⟨w, hw | hw⟩ := h.comparable (u + x) (hu.add hx.toIsPreadditive)
    · use w
      exact Or.inl <| hx.add_right_cancel _ _ <| by rw [hx.add_assoc, hw]
    · use w
      exact Or.inr <| hx.add_right_cancel _ _ <| by rw [hx.add_assoc, hw]

lemma add_add_add_comm (hb : IsPreadditive b) (hc : IsAdditive c) (hd : IsPreadditive d) (a : V) :
    a + b + (c + d) = a + c + (b + d) := by
  rw [← hd.add_assoc, hc.add_assoc, hc.add_comm b hb, ← hb.add_assoc, hd.add_assoc]

end IsAdditive

protected lemma IsMultiplicative.mul (hx : IsMultiplicative x) (hy : IsMultiplicative y) :
    IsMultiplicative (x * y) where
  toIsPremultiplicative := hy.isPremultiplicative_mul x hx.toIsPremultiplicative
  mul_assoc u v hu hv := by
    rw [← hy.mul_assoc _ x (hv.isAdditive_mul u hu) hx.toIsPremultiplicative,
      hx.mul_assoc u v hu hv, hy.mul_assoc u _ hu (hx.isPremultiplicative_mul v hv),
      hy.mul_assoc v x hv.toIsAdditive hx.toIsPremultiplicative]
  mul_comm u hu hu' := by
    rw [← hy.mul_assoc u x hu.toIsAdditive hx.toIsPremultiplicative, hx.mul_comm u hu hu',
      hy.mul_assoc x u hx.toIsAdditive hu, hy.mul_comm u hu hu',
      hu' x y hx.toIsAdditive hy.toIsPremultiplicative]
  isPremultiplicative_mul u hu := by
    rw [← hy.mul_assoc u x hu.toIsAdditive hx.toIsPremultiplicative]
    exact hy.isPremultiplicative_mul _ <| hx.isPremultiplicative_mul u hu

section

variable [V↓[ℒₒᵣ] ⊧* 𝗤]

namespace IsPreadditive

protected lemma zero : IsPreadditive (0 : V) := by constructor <;> simp

protected lemma one : IsPreadditive (1 : V) where
  add_assoc u v := (Arithmetic.add_succ u v).symm
  zero_add := zero_add_one
  add_one_add _ := rfl
  add_right_cancel _ _ := succ_inj

end IsPreadditive

namespace IsAdditive

protected lemma zero : IsAdditive (0 : V) where
  toIsPreadditive := .zero
  add_comm u hu := by rw [hu.zero_add, Arithmetic.add_zero]
  comparable u _ := by
    use u
    simp

protected lemma one : IsAdditive (1 : V) where
  toIsPreadditive := .one
  add_comm u hu := by
    nth_rw 2 [← zero_add_one]
    rw [hu.add_one_add, hu.zero_add]
  comparable u _ := by
    rcases zero_or_succ u with rfl | ⟨z, rfl⟩
    · use 1
      simp
    · use z, .inl rfl

end IsAdditive

lemma mul_one_of_zero_add (hx : 0 + x = x) : x * 1 = x := by
  rw [← zero_add_one, Arithmetic.mul_succ, Arithmetic.mul_zero, hx]

namespace IsPremultiplicative

protected lemma zero : IsPremultiplicative (0 : V) where
  toIsAdditive := .zero
  isAdditive_mul u _ := by simpa using IsAdditive.zero
  mul_add u v _ := by simp
  add_mul u v _ _ := by simp
  zero_mul := by simp
  one_mul := by simp

protected lemma one : IsPremultiplicative (1 : V) where
  toIsAdditive := .one
  isAdditive_mul u hu := by rwa [mul_one_of_zero_add hu.zero_add]
  mul_add u v hu := by rw [mul_one_of_zero_add hu.zero_add, Arithmetic.mul_succ]
  add_mul u v hu hv := by simp only [mul_one_of_zero_add, (hu.add hv).zero_add, hu.zero_add,
    hv.zero_add]
  zero_mul := by simp
  one_mul := by simp

protected lemma add (hx : IsPremultiplicative x) (hy : IsPremultiplicative y) :
    IsPremultiplicative (x + y) where
  toIsAdditive := hx.toIsAdditive.add hy.toIsAdditive
  isAdditive_mul u hu := by
    rw [hy.mul_add u x hu]
    exact (hx.isAdditive_mul u hu).add <| hy.isAdditive_mul u hu
  mul_add u v hu := by
    rw [← hy.add_assoc, hy.mul_add u _ hu, hx.mul_add u v hu, hy.mul_add u x hu,
      (hy.isAdditive_mul u hu).add_assoc]
  add_mul u v hu hv := by
    rw [hy.mul_add _ x (hu.add hv), hy.mul_add u x hu, hy.mul_add v x hv, hx.add_mul u v hu hv,
      hy.add_mul u v hu hv, IsAdditive.add_add_add_comm (hx.isAdditive_mul v hv).toIsPreadditive
        (hy.isAdditive_mul u hu) (hy.isAdditive_mul v hv).toIsPreadditive]
  zero_mul := by rw [hy.mul_add 0 x .zero, hx.zero_mul, hy.zero_mul, Arithmetic.add_zero]
  one_mul := by rw [hy.mul_add 1 x .one, hx.one_mul, hy.one_mul]

lemma of_add (hx : IsPremultiplicative x) (h : IsPremultiplicative (z + x)) :
    IsPremultiplicative z := by
  have hz (u) (hu : IsAdditive u) : IsAdditive (u * z) :=
    (hx.isAdditive_mul u hu).of_add <| by
      rw [← hx.mul_add u z hu]
      exact h.isAdditive_mul u hu
  constructor
  · exact hx.toIsAdditive.of_add h.toIsAdditive
  · exact hz
  · intro u v hu
    apply (hx.isAdditive_mul u hu).add_right_cancel
    rw [← hx.mul_add u _ hu, hx.add_assoc, h.mul_add u v hu, hx.mul_add u z hu,
      (hx.isAdditive_mul u hu).add_assoc]
  · intro u v hu hv
    apply (hx.isAdditive_mul _ (hu.add hv)).add_right_cancel
    rw [← hx.mul_add _ z (hu.add hv), h.add_mul u v hu hv, hx.mul_add u z hu, hx.mul_add v z hv,
      hx.add_mul u v hu hv, IsAdditive.add_add_add_comm (hx.isAdditive_mul u hu).toIsPreadditive
        (hz v hv) (hx.isAdditive_mul v hv).toIsPreadditive]
  · have h₁ := hx.mul_add 0 z .zero
    rwa [h.zero_mul, hx.zero_mul, Arithmetic.add_zero, eq_comm] at h₁
  · apply hx.add_right_cancel
    have h₁ := hx.mul_add 1 z .one
    rwa [h.one_mul, hx.one_mul, eq_comm] at h₁

end IsPremultiplicative

namespace IsMultiplicative

protected lemma zero : IsMultiplicative (0 : V) where
  toIsPremultiplicative := .zero
  mul_assoc u v _ _ := by simp
  mul_comm u hu _ := by simp [hu.zero_mul]
  isPremultiplicative_mul u _ := by simpa using IsPremultiplicative.zero

protected lemma one : IsMultiplicative (1 : V) where
  toIsPremultiplicative := .one
  mul_assoc u v hu hv := by
    rw [mul_one_of_zero_add hv.zero_add, mul_one_of_zero_add (hv.isAdditive_mul u hu).zero_add]
  mul_comm u hu _ := by rw [mul_one_of_zero_add hu.zero_add, hu.one_mul]
  isPremultiplicative_mul u hu := by rwa [mul_one_of_zero_add hu.zero_add]

protected lemma add (hx : IsMultiplicative x) (hy : IsMultiplicative y) :
    IsMultiplicative (x + y) where
  toIsPremultiplicative := hx.toIsPremultiplicative.add hy.toIsPremultiplicative
  mul_assoc u v hu hv := by
    rw [hy.mul_add _ x (hv.isAdditive_mul u hu), hy.mul_add v x hv.toIsAdditive,
      (hy.isPremultiplicative_mul v hv).mul_add u _ hu, hx.mul_assoc u v hu hv,
      hy.mul_assoc u v hu hv]
  mul_comm u hu hu' := by
    rw [hy.mul_add u x hu.toIsAdditive, hu.add_mul x y hx.toIsAdditive hy.toIsAdditive,
      hx.mul_comm u hu hu', hy.mul_comm u hu hu']
  isPremultiplicative_mul u hu := by
    rw [hy.mul_add u x hu.toIsAdditive]
    exact (hx.isPremultiplicative_mul u hu).add <| hy.isPremultiplicative_mul u hu

lemma of_add (hx : IsMultiplicative x) (h : IsMultiplicative (z + x)) : IsMultiplicative z where
  toIsPremultiplicative := hx.toIsPremultiplicative.of_add h.toIsPremultiplicative
  mul_assoc u v hu hv := by
    apply (hx.isAdditive_mul _ (hv.isAdditive_mul u hu)).add_right_cancel
    rw [← hx.mul_add _ z (hv.isAdditive_mul u hu), h.mul_assoc u v hu hv,
      hx.mul_add v z hv.toIsAdditive, (hx.isPremultiplicative_mul v hv).mul_add u _ hu,
      hx.mul_assoc u v hu hv]
  mul_comm u hu hu' := by
    apply (hx.isAdditive_mul u hu.toIsAdditive).add_right_cancel
    rw [← hx.mul_add u z hu.toIsAdditive, h.mul_comm u hu hu', hx.mul_comm u hu hu',
      hu.add_mul z x (hx.toIsAdditive.of_add h.toIsAdditive) hx.toIsAdditive]
  isPremultiplicative_mul u hu := by
    apply (hx.isPremultiplicative_mul u hu).of_add
    rw [← hx.mul_add u z hu.toIsAdditive]
    exact h.isPremultiplicative_mul u hu

end IsMultiplicative

end

namespace RobinsonQ

open DirectTranslation

/--
The translation of the language of arithmetic into $\mathsf{Q}$ on the multiplicative elements:
`0`, `1`, `+` and `*` are unchanged, and `<` is `LeftLT`.
- [Mur24, §6, Theorem 24]
-/
def multiplicativeTranslation : DirectTranslation 𝗤 ℒₒᵣ where
  domain := ⟨isMultiplicativeDef⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨leftLTDef⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using IsMultiplicative.zero
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsMultiplicative (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : V, IsMultiplicative y ∧ y = 0 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 0
      simp [IsMultiplicative.zero]
    · suffices ∃! y : V, IsMultiplicative y ∧ y = 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 1
      simp [IsMultiplicative.one]
    · suffices ∃! y : V, IsMultiplicative y ∧ y = e 0 + e 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use e 0 + e 1
      simp [(he 0).add (he 1)]
    · suffices ∃! y : V, IsMultiplicative y ∧ y = e 0 * e 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use e 0 * e 1
      simp [(he 0).mul (he 1)]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma multiplicativeTranslation_dom_iff : multiplicativeTranslation.Dom x ↔ IsMultiplicative x := by
  simp [dom_iff, multiplicativeTranslation, Semiformula.Operator.val]

lemma multiplicativeTranslation.isMultiplicative_val (a : multiplicativeTranslation.Model V) :
    IsMultiplicative (a : V) := multiplicativeTranslation_dom_iff.mp a.dom

section model

variable [V↓[ℒₒᵣ] ⊧* 𝗤]

namespace multiplicativeTranslation

/-- The operations of `V` and `LeftLT` restricted to the multiplicative elements. -/
abbrev oRingStructure : ORingStructure (multiplicativeTranslation.Model V) where
  zero := ⟨0, by simpa using IsMultiplicative.zero⟩
  one := ⟨1, by simpa using IsMultiplicative.one⟩
  add a b := ⟨a + b, by simpa using (isMultiplicative_val a).add (isMultiplicative_val b)⟩
  mul a b := ⟨a * b, by simpa using (isMultiplicative_val a).mul (isMultiplicative_val b)⟩
  lt a b := LeftLT (a : V) b

/-- The structure of the model of `multiplicativeTranslation` is the one of `oRingStructure`. -/
lemma struc_eq : Model.struc multiplicativeTranslation V = @standardModel _ oRingStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;>
        simp [multiplicativeTranslation, Semiformula.Operator.val,
          Semiformula.Operator.Eq.sentence_eq] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      · exact propext <| Model.eq_iff v
      · change (multiplicativeTranslation.rel .lt).val (fun i ↦ (v i : V)) =
          LeftLT (v 0 : V) (v 1)
        rw [Matrix.fun_eq_vec_two (fun i ↦ (v i : V))]
        simp [multiplicativeTranslation, Semiformula.Operator.val])

section

attribute [local instance] oRingStructure

variable (a b c : multiplicativeTranslation.Model V)

protected lemma add_zero : a + 0 = a := Model.ext Arithmetic.add_zero

protected lemma zero_add : 0 + a = a := Model.ext (isMultiplicative_val a).zero_add

protected lemma add_assoc : a + b + c = a + (b + c) :=
  Model.ext <| (isMultiplicative_val c).add_assoc a b

protected lemma add_comm : a + b = b + a :=
  Model.ext <| (isMultiplicative_val b).add_comm a (isMultiplicative_val a).toIsPreadditive

protected lemma mul_zero : a * 0 = 0 := Model.ext <| Arithmetic.mul_zero (a : V)

protected lemma mul_one : a * 1 = a :=
  Model.ext <| mul_one_of_zero_add (isMultiplicative_val a).zero_add

protected lemma mul_assoc : a * b * c = a * (b * c) :=
  Model.ext <| (isMultiplicative_val c).mul_assoc a b (isMultiplicative_val a).toIsAdditive
    (isMultiplicative_val b).toIsPremultiplicative

protected lemma mul_comm : a * b = b * a :=
  Model.ext <| (isMultiplicative_val b).mul_comm a (isMultiplicative_val a).toIsPremultiplicative
    (isMultiplicative_val a).mul_assoc

protected lemma mul_add : a * (b + c) = a * b + a * c :=
  Model.ext <| (isMultiplicative_val c).mul_add a b (isMultiplicative_val a).toIsAdditive

protected lemma add_mul : (a + b) * c = a * c + b * c :=
  Model.ext <| (isMultiplicative_val c).add_mul a b (isMultiplicative_val a).toIsAdditive
    (isMultiplicative_val b).toIsAdditive

variable {a b c}

/-- An element of `V` is in the model if its sum with an element of the model is. -/
lemma exists_val_eq {z : V} (h : z + a = b) : ∃ c : multiplicativeTranslation.Model V, c = z := by
  use ⟨z, multiplicativeTranslation_dom_iff.mpr <| (isMultiplicative_val a).of_add <|
    h ▸ isMultiplicative_val b⟩

lemma eq_zero_or_exists_eq_add_one (a : multiplicativeTranslation.Model V) :
    a = 0 ∨ ∃ b, a = b + 1 := by
  rcases zero_or_succ (a : V) with h | ⟨z, h⟩
  · exact Or.inl <| Model.ext h
  · obtain ⟨b, rfl⟩ := exists_val_eq (a := 1) h.symm
    right
    use b
    exact Model.ext h

lemma lt_iff : a < b ↔ ∃ c, c + 1 + a = b := by
  constructor
  · rintro ⟨z, h⟩
    obtain ⟨d, hd⟩ := exists_val_eq h
    obtain ⟨c, rfl⟩ := exists_val_eq (a := 1) hd.symm
    use c
    exact Model.ext h
  · rintro ⟨c, rfl⟩
    use c
    rfl

lemma eq_or_lt_of_add_eq (h : c + a = b) : a = b ∨ a < b := by
  rcases eq_zero_or_exists_eq_add_one c with rfl | ⟨c, rfl⟩
  · exact Or.inl <| by rw [← h, multiplicativeTranslation.zero_add]
  · exact Or.inr <| lt_iff.mpr ⟨c, h⟩

lemma exists_add_eq_of_lt (h : a < b) : ∃ c < b + 1, a + c = b := by
  obtain ⟨c, rfl⟩ := lt_iff.mp h
  use c + 1
  and_intros
  · apply lt_iff.mpr
    use a
    rw [multiplicativeTranslation.add_assoc, multiplicativeTranslation.add_comm 1,
      ← multiplicativeTranslation.add_assoc, multiplicativeTranslation.add_comm a]
  · exact multiplicativeTranslation.add_comm _ _

lemma one_le_of_zero_lt (h : 0 < a) : 1 = a ∨ 1 < a := by
  obtain ⟨c, hc⟩ := lt_iff.mp h
  rw [multiplicativeTranslation.add_zero] at hc
  exact eq_or_lt_of_add_eq hc

lemma add_lt_add (h : a < b) (c : multiplicativeTranslation.Model V) : a + c < b + c := by
  obtain ⟨d, rfl⟩ := lt_iff.mp h
  apply lt_iff.mpr
  use d
  rw [multiplicativeTranslation.add_assoc (d + 1)]

lemma mul_lt_mul (h : a < b) (hc : 0 < c) : a * c < b * c := by
  obtain ⟨d, rfl⟩ := lt_iff.mp h
  obtain ⟨e, rfl⟩ := lt_iff.mp hc
  apply lt_iff.mpr
  use (d + 1) * e + d
  rw [multiplicativeTranslation.add_zero, multiplicativeTranslation.add_mul _ a,
    multiplicativeTranslation.mul_add (d + 1), multiplicativeTranslation.mul_one,
    multiplicativeTranslation.add_assoc _ d]

lemma lt_irrefl (a : multiplicativeTranslation.Model V) : ¬a < a := by
  rintro ⟨z, h⟩
  exact Arithmetic.succ_ne_zero z <| (isMultiplicative_val a).add_right_cancel _ _ <|
    h.trans (isMultiplicative_val a).zero_add.symm

lemma lt_trans (hab : a < b) (hbc : b < c) : a < c := by
  obtain ⟨d, rfl⟩ := lt_iff.mp hab
  obtain ⟨e, rfl⟩ := lt_iff.mp hbc
  apply lt_iff.mpr
  use e + 1 + d
  rw [multiplicativeTranslation.add_assoc (e + 1) d, multiplicativeTranslation.add_assoc]

lemma lt_tri (a b : multiplicativeTranslation.Model V) : a < b ∨ a = b ∨ b < a := by
  obtain ⟨z, h | h⟩ :=
    (isMultiplicative_val a).comparable b (isMultiplicative_val b).toIsPreadditive
  all_goals
    obtain ⟨c, rfl⟩ := exists_val_eq h
    have := eq_or_lt_of_add_eq (Model.ext h)
    tauto

end

/--
The multiplicative elements of a model of $\mathsf{Q}$ form a model of $\mathsf{PA}^-$.
- [Mur24, §6, Theorem 24]
-/
instance : (multiplicativeTranslation.Model V)↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
  rw [struc_eq]
  let := oRingStructure (V := V)
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case addZero => simpa [models_iff] using multiplicativeTranslation.add_zero (V := V)
  case addAssoc => simpa [models_iff] using multiplicativeTranslation.add_assoc (V := V)
  case addComm => simpa [models_iff] using multiplicativeTranslation.add_comm (V := V)
  case addEqOfLt =>
    simpa [models_iff, Semiformula.eval_bexsLTSucc] using
      fun a b ↦ exists_add_eq_of_lt (V := V) (a := a) (b := b)
  case zeroLe =>
    simpa [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq] using
      fun a : multiplicativeTranslation.Model V ↦
        eq_or_lt_of_add_eq (multiplicativeTranslation.add_zero a)
  case zeroLtOne =>
    simpa [models_iff] using
      lt_iff.mpr ⟨0, Model.ext <| Arithmetic.add_zero.trans <| zero_add_one (M := V)⟩
  case oneLeOfZeroLt =>
    simpa [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq] using
      fun a ↦ one_le_of_zero_lt (V := V) (a := a)
  case addLtAdd =>
    simpa [models_iff] using fun a b c h ↦ add_lt_add (V := V) (a := a) (b := b) h c
  case mulZero => simpa [models_iff] using multiplicativeTranslation.mul_zero (V := V)
  case mulOne => simpa [models_iff] using multiplicativeTranslation.mul_one (V := V)
  case mulAssoc => simpa [models_iff] using multiplicativeTranslation.mul_assoc (V := V)
  case mulComm => simpa [models_iff] using multiplicativeTranslation.mul_comm (V := V)
  case mulLtMul =>
    simpa [models_iff] using fun a b c ↦ mul_lt_mul (V := V) (a := a) (b := b) (c := c)
  case distr => simpa [models_iff] using multiplicativeTranslation.mul_add (V := V)
  case ltIrrefl => simpa [models_iff] using lt_irrefl (V := V)
  case ltTrans =>
    simpa [models_iff] using fun a b c ↦ lt_trans (V := V) (a := a) (b := b) (c := c)
  case ltTri => simpa [models_iff] using lt_tri (V := V)

end multiplicativeTranslation

end model

/--
$\mathsf{Q}$ interprets $\mathsf{PA}^-$.
- [Mur24, §6, Theorem 24]
-/
instance : 𝗤 ⊳ 𝗣𝗔⁻ where
  trln := multiplicativeTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end RobinsonQ

end FFL.FirstOrder.Arithmetic

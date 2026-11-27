module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Semantics.Basic

/-!
# Relativization to a class closed under concatenation

The translation of the language with the empty string into a theory in it that restricts the
quantifiers to a definable class containing the letters and the empty string and closed under
concatenation.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

section relativization

/-- `D` contains the letters and the empty string and is closed under concatenation. -/
structure IsConcatenationClosed {V : Type*} [ConcatenationEmptyStructure V] (D : V → Prop) :
    Prop where
  zero : D 0
  one : D 1
  empty : D ∅
  append {x y : V} : D x → D y → D (x ++ y)

variable (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (δ : Semisentence ℒ⌢ₑ 1)
  (H : ∀ (V : Type) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* T],
    IsConcatenationClosed fun x : V ↦ V ⊧/![x] δ)

/-- The translation that restricts the quantifiers to `δ` and leaves the symbols unchanged. -/
def relativization : DirectTranslation T ℒ⌢ₑ where
  domain := ⟨δ⟩
  rel R := ⟨Semiformula.rel R (#·)⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using (H V).zero
  func_defined f := completeEmpty.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : V ⊧/![e i] δ := by simpa [Semiformula.Operator.val] using he i
    suffices ∃! y : V, V ⊧/![y] δ ∧ y = Tarski.Structure.func f e by
      simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    use Tarski.Structure.func f e
    simp only [and_true, and_imp, imp_self, implies_true]
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    exacts [(H V).zero, (H V).one, (H V).append (he 0) (he 1), (H V).empty]
  preserve_eq := completeEmpty.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val]

namespace relativization

variable {V : Type} [ConcatenationEmptyStructure V] {x : V}

@[simp]
lemma dom_iff : (relativization T δ H).Dom x ↔ V ⊧/![x] δ := by
  simp [DirectTranslation.dom_iff, relativization, Semiformula.Operator.val]

variable [V↓[ℒ⌢ₑ] ⊧* T]

/-- The letters, the empty string and the concatenation of `V` restricted to `δ`. -/
abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure ((relativization T δ H).Model V) where
  zero := ⟨0, (dom_iff T δ H).mpr (H V).zero⟩
  one := ⟨1, (dom_iff T δ H).mpr (H V).one⟩
  emptyCollection := ⟨∅, (dom_iff T δ H).mpr (H V).empty⟩
  append x y := ⟨x ++ y, (dom_iff T δ H).mpr <|
    (H V).append ((dom_iff T δ H).mp x.dom) ((dom_iff T δ H).mp y.dom)⟩

/--
The structure of the model of `relativization` is the standard one of the letters, the empty string
and the concatenation restricted to `δ`.
-/
lemma struc_eq : Model.struc (relativization T δ H) V =
    @standardModelEmpty _ (concatenationEmptyStructure T δ H) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;>
        simp [relativization, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationEmptyStructure

variable {y : V} {hx : (relativization T δ H).Dom x} {hy : (relativization T δ H).Dom y}

@[simp]
lemma zero_eq_mk : (0 : (relativization T δ H).Model V) = ⟨0, (dom_iff T δ H).mpr (H V).zero⟩ :=
  rfl

@[simp]
lemma one_eq_mk : (1 : (relativization T δ H).Model V) = ⟨1, (dom_iff T δ H).mpr (H V).one⟩ := rfl

@[simp]
lemma empty_eq_mk : (∅ : (relativization T δ H).Model V) = ⟨∅, (dom_iff T δ H).mpr (H V).empty⟩ :=
  rfl

@[simp]
lemma mk_append_mk : (⟨x, hx⟩ ++ ⟨y, hy⟩ : (relativization T δ H).Model V) =
    ⟨x ++ y, (dom_iff T δ H).mpr <| (H V).append ((dom_iff T δ H).mp hx) ((dom_iff T δ H).mp hy)⟩ :=
  rfl

end

end relativization

end relativization

end FFL.FirstOrder.Concatenation

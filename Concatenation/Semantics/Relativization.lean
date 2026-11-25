module

public import Concatenation.Semantics.Empty
public import AlphaCentauri.Interpretability.Basic

/-!
# Relativization of the language of concatenation with the empty string
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

/-- `D` contains the letters and the empty string and is closed under concatenation. -/
structure IsConcatenationClosed {M : Type*} [ConcatenationEmptyStructure M] (D : M → Prop) :
    Prop where
  zero : D 0
  one : D 1
  empty : D ∅
  append {x y : M} : D x → D y → D (x ++ y)

variable (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (δ : Semisentence ℒ⌢ₑ 1)
  (H : ∀ (M : Type) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T],
    IsConcatenationClosed fun x : M ↦ M ⊧/![x] δ)

/-- The translation that restricts the quantifiers to `δ` and leaves the symbols unchanged. -/
def relativization : DirectTranslation T ℒ⌢ₑ where
  domain := ⟨δ⟩
  rel R := ⟨Semiformula.rel R (#·)⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using (H M).zero
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : M ⊧/![e i] δ := by simpa [Semiformula.Operator.val] using he i
    suffices ∃! y : M, M ⊧/![y] δ ∧ y = Tarski.Structure.func f e by
      simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    use Tarski.Structure.func f e
    simp only [and_true, and_imp, imp_self, implies_true]
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · exact (H M).zero
    · exact (H M).one
    · exact (H M).append (he 0) (he 1)
    · exact (H M).empty
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val]

namespace relativization

variable {M : Type} [ConcatenationEmptyStructure M] {x : M}

@[simp]
lemma dom_iff : (relativization T δ H).Dom x ↔ M ⊧/![x] δ := by
  simp [DirectTranslation.dom_iff, relativization, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* T]

/-- The letters, the empty string and the concatenation of `M` restricted to `δ`. -/
abbrev concatenationStructure : ConcatenationEmptyStructure ((relativization T δ H).Model M) where
  zero := ⟨0, (dom_iff T δ H).mpr (H M).zero⟩
  one := ⟨1, (dom_iff T δ H).mpr (H M).one⟩
  emptyCollection := ⟨∅, (dom_iff T δ H).mpr (H M).empty⟩
  append x y := ⟨x ++ y, (dom_iff T δ H).mpr <|
    (H M).append ((dom_iff T δ H).mp x.dom) ((dom_iff T δ H).mp y.dom)⟩

/--
The structure of the model of `relativization` is the standard one of the letters, the empty string
and the concatenation restricted to `δ`.
-/
lemma struc_eq : Model.struc (relativization T δ H) M =
    @standardModelEmpty _ (concatenationStructure T δ H) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;>
        simp [relativization, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)


end relativization

end FFL.FirstOrder.Concatenation

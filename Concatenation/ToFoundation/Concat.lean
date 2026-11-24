module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation

/-!
# Concatenation symbol

Languages with a binary function symbol for concatenation, and the term notation `t ⌢ u`.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- Languages with a symbol for concatenation. -/
protected class Language.Concat (L : Language) where
  concat : L.Func 2

attribute [match_pattern] Language.Concat.concat

variable {L : Language} {ξ : Type*} {n : ℕ}

namespace Semiterm

namespace Operator

protected class Concat (L : Language) where
  concat : Semiterm.Operator L 2

notation "op(⌢)" => Concat.concat

notation "op(⌢)[" L "]" => Concat.concat (L := L)

instance [L.Concat] : Operator.Concat L := ⟨⟨Semiterm.func Language.Concat.concat Semiterm.bvar⟩⟩

lemma Concat.term_eq [L.Concat] :
    (@Concat.concat L _).term = Semiterm.func Language.Concat.concat Semiterm.bvar := rfl

@[simp]
lemma Concat.positive_iff [L.Concat] (t u : Semiterm L ξ (n + 1)) :
    (Concat.concat.operator ![t, u]).Positive ↔ t.Positive ∧ u.Positive := by
  simp [positive_operator_iff, Concat.term_eq, bv_func]

end Operator

@[simp]
lemma complexity_concat [L.Concat] (t u : Semiterm L ξ n) :
    (Operator.Concat.concat.operator ![t, u]).complexity =
      max t.complexity u.complexity + 1 := by
  simp [Operator.operator, Operator.Concat.term_eq, complexity_func, Rew.func,
    Fin.univ_succ]

end Semiterm

instance (L S : Language) [L.Concat] : (L.add S).Concat := ⟨Sum.inl Language.Concat.concat⟩

syntax:50 first_order_term:50 " ⌢ " first_order_term:51 : first_order_term

macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ ⌢ $e₂ ]) =>
    `(Semiterm.Operator.Concat.concat.operator
      ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])

end FFL.FirstOrder

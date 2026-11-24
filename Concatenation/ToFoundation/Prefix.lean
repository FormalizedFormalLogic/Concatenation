module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation

/-!
# Prefix symbol

Languages with a binary relation symbol for prefixes, and the formula notation `t ≼ u`.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- Languages with a symbol for the prefix relation. -/
protected class Language.Prefix (L : Language) where
  pref : L.Rel 2

attribute [match_pattern] Language.Prefix.pref

namespace Semiformula.Operator

protected class Prefix (L : Language) where
  pref : Semiformula.Operator L 2

notation "op(≼)" => Prefix.pref

notation "op(≼)[" L "]" => Prefix.pref (L := L)

variable {L : Language}

instance [L.Prefix] : Operator.Prefix L :=
  ⟨⟨Semiformula.rel Language.Prefix.pref Semiterm.bvar⟩⟩

lemma Prefix.sentence_eq [L.Prefix] :
    (@Prefix.pref L _).sentence = Semiformula.rel Language.Prefix.pref Semiterm.bvar := rfl

end Semiformula.Operator

syntax:45 first_order_term:45 " ≼ " first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≼ $u:first_order_term ]) =>
    `(Semiformula.Operator.operator Semiformula.Operator.Prefix.pref
      ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])

end FFL.FirstOrder

module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.FirstOrder.Tarski.Operator

/-!
# Prefix symbol

Languages with a binary relation symbol for prefixes, the formula notation `t ⊑ u`, and structures
interpreting the symbol as a given order.
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

notation "op(⊑)" => Prefix.pref

notation "op(⊑)[" L "]" => Prefix.pref (L := L)

variable {L : Language}

instance [L.Prefix] : Operator.Prefix L :=
  ⟨⟨Semiformula.rel Language.Prefix.pref Semiterm.bvar⟩⟩

lemma Prefix.sentence_eq [L.Prefix] :
    (@Prefix.pref L _).sentence = Semiformula.rel Language.Prefix.pref Semiterm.bvar := rfl

end Semiformula.Operator

syntax:45 first_order_term:45 " ⊑ " first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ⊑ $u:first_order_term ]) =>
    `(Semiformula.Operator.operator Semiformula.Operator.Prefix.pref
      ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])

namespace Tarski.Structure

variable (L : Language) (M : Type*) [Tarski.Structure L M]

/-- The operator of prefixes is interpreted as `≤`. -/
protected class Prefix [Semiformula.Operator.Prefix L] [LE M] : Prop where
  pref : ∀ a b : M, (@Semiformula.Operator.Prefix.pref L _).val ![a, b] ↔ a ≤ b

attribute [simp] Prefix.pref

end Tarski.Structure

@[simp]
lemma Semiformula.Operator.pref_iff_le {L : Language} {M : Type*} [Tarski.Structure L M]
    [Operator.Prefix L] [LE M] [Tarski.Structure.Prefix L M] {v : Fin 2 → M} :
    (@Operator.Prefix.pref L _).val v ↔ v 0 ≤ v 1 := by
  rw [Matrix.fun_eq_vec_two (v := v)]
  simp

end FFL.FirstOrder

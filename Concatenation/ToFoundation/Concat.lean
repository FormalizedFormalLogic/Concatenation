module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.FirstOrder.Tarski.Operator

/-!
# Concatenation and prefix symbols

Languages with a binary function symbol for concatenation, written `t ⌢ u`, or with a binary
relation symbol for prefixes, written `t ⊑ u`.
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

namespace Tarski.Structure

variable (L) (V : Type*) [Tarski.Structure L V]

/-- The operator of concatenation is interpreted as `++`. -/
protected class Concat [Semiterm.Operator.Concat L] [Append V] : Prop where
  concat : ∀ a b : V, (@Semiterm.Operator.Concat.concat L _).val ![a, b] = a ++ b

attribute [simp] Concat.concat

variable {L V}

@[simp]
lemma concat_eq_of_lang [L.Concat] [Append V] [Tarski.Structure.Concat L V] {v : Fin 2 → V} :
    Tarski.Structure.func (L := L) Language.Concat.concat v = v 0 ++ v 1 := by
  have h := Tarski.Structure.Concat.concat (L := L) (v 0) (v 1)
  simp only [← Matrix.fun_eq_vec_two] at h
  exact h

end Tarski.Structure

variable {V : Type*} [Tarski.Structure L V] [Append V]

@[simp]
lemma Semiterm.val_concat [Semiterm.Operator.Concat L] [Tarski.Structure.Concat L V]
    {e : Fin n → V} {ε : ξ → V} (t u : Semiterm L ξ n) :
    (Operator.Concat.concat.operator ![t, u]).val e ε = t.val e ε ++ u.val e ε := by
  simp

end FFL.FirstOrder

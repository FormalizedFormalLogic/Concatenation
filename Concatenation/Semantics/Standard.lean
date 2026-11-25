module

public import Concatenation.Semantics.Basic

/-!
# The standard model of concatenation

The free semigroup on two letters, the nonempty binary strings, is a model of $\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
The nonempty binary strings under concatenation.
- [GZ08, §1]
- [Vis09, §2]
-/
instance : ConcatenationStructure (FreeSemigroup Bool) where
  zero := FreeSemigroup.of false
  one := FreeSemigroup.of true
  append := (· * ·)

lemma zero_eq_of_false : (0 : FreeSemigroup Bool) = FreeSemigroup.of false := rfl

lemma one_eq_of_true : (1 : FreeSemigroup Bool) = FreeSemigroup.of true := rfl

@[simp]
lemma append_eq_mul (x y : FreeSemigroup Bool) : x ++ y = x * y := rfl

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simp [models_iff, mul_assoc]
  case editor => simpa [models_iff] using fun x y z w ↦ FreeSemigroup.mul_eq_mul_iff.mp
  case zeroNeConcat => simpa [models_iff, zero_eq_of_false] using FreeSemigroup.of_ne_mul false
  case oneNeConcat => simpa [models_iff, one_eq_of_true] using FreeSemigroup.of_ne_mul true
  case zeroNeOne => simp [models_iff, zero_eq_of_false, one_eq_of_true, FreeSemigroup.of]⟩

instance : Entailment.Consistent 𝗧𝗖 :=
  let : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

end FFL.FirstOrder.Concatenation

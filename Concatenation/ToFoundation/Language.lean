module

public import Foundation.Syntax.Predicate.Language
public import Mathlib.Logic.Encodable.Basic

/-!
# Decidable equality and codes of symbols of constant and summed languages
-/

@[expose] public section

namespace FFL.FirstOrder.Language

instance (C : Type*) [DecidableEq C] (k : ℕ) : DecidableEq (Constant.Func C k)
  | .const c, .const d => decidable_of_iff (c = d) (by simp)

instance (C : Type*) [Encodable C] (k : ℕ) : Encodable (Constant.Func C k) where
  encode | .const c => Encodable.encode c
  decode e :=
    match k with
    | 0 => (Encodable.decode e).map .const
    | _ + 1 => none
  encodek | .const c => by simp

instance (C : Type*) [DecidableEq C] (k : ℕ) : DecidableEq ((constant C).Func k) :=
  inferInstanceAs (DecidableEq (Constant.Func C k))

instance (C : Type*) (k : ℕ) : DecidableEq ((constant C).Rel k) :=
  inferInstanceAs (DecidableEq PEmpty)

instance (C : Type*) [Encodable C] (k : ℕ) : Encodable ((constant C).Func k) :=
  inferInstanceAs (Encodable (Constant.Func C k))

instance (C : Type*) (k : ℕ) : Encodable ((constant C).Rel k) := inferInstanceAs (Encodable PEmpty)

variable (L₁ L₂ : Language) (k : ℕ)

instance [∀ k, DecidableEq (L₁.Func k)] [∀ k, DecidableEq (L₂.Func k)] :
    DecidableEq ((L₁.add L₂).Func k) :=
  inferInstanceAs (DecidableEq (L₁.Func k ⊕ L₂.Func k))

instance [∀ k, DecidableEq (L₁.Rel k)] [∀ k, DecidableEq (L₂.Rel k)] :
    DecidableEq ((L₁.add L₂).Rel k) :=
  inferInstanceAs (DecidableEq (L₁.Rel k ⊕ L₂.Rel k))

instance [∀ k, Encodable (L₁.Func k)] [∀ k, Encodable (L₂.Func k)] :
    Encodable ((L₁.add L₂).Func k) :=
  inferInstanceAs (Encodable (L₁.Func k ⊕ L₂.Func k))

instance [∀ k, Encodable (L₁.Rel k)] [∀ k, Encodable (L₂.Rel k)] :
    Encodable ((L₁.add L₂).Rel k) :=
  inferInstanceAs (Encodable (L₁.Rel k ⊕ L₂.Rel k))

end FFL.FirstOrder.Language

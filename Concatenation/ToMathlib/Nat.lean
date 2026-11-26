module

public import Mathlib.Order.WellFounded

/-!
# Strong recursion on the natural numbers
-/

@[expose] public section

namespace Nat

variable {S : Type*} [Nonempty S]

lemma exists_strongRec (g : ℕ → (ℕ → S) → S) :
    ∃ val : ℕ → S, ∀ e, ∃ u : ℕ → S, (∀ i < e, u i = val i) ∧ val e = g e u := by
  classical
  have a : S := Classical.arbitrary S
  let val : ℕ → S := Nat.lt_wfRel.wf.fix fun e ih ↦ g e fun i ↦ if h : i < e then ih i h else a
  use val
  intro e
  use fun i ↦ if i < e then val i else a
  constructor
  · intro i hi
    simp [hi]
  · exact Nat.lt_wfRel.wf.fix_eq _ e

end Nat

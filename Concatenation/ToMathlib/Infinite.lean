module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Dedekind-infinite types

A type with an injective map into itself that misses a point is infinite.
-/

@[expose] public section

lemma Infinite.of_injective_of_forall_ne {α : Type*} {f : α → α} (hf : f.Injective) {a : α}
    (ha : ∀ x, f x ≠ a) : Infinite α :=
  not_finite_iff_infinite.mp fun _ ↦
    let ⟨x, hx⟩ := Finite.surjective_of_injective hf a
    ha x hx

module

public import Concatenation.Semantics.Basic

/-!
# Semantics of the language of concatenation with prefixes

Structures with two letters, a concatenation and an order, read as structures for `ℒ⌢⊑`.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Language

variable (M : Type*) [LE M]

instance prefixRelStructure : Tarski.Structure prefixRel M where
  func := fun _ f ↦ f.elim
  rel := fun _ r ↦
    match r with
    | PrefixRel.pref => fun v ↦ v 0 ≤ v 1

variable [ConcatenationStructure M]

instance : Tarski.Structure.Eq ℒ⌢⊑ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢⊑ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢⊑ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢⊑ M := ⟨fun _ _ ↦ rfl⟩

instance : Tarski.Structure.Prefix ℒ⌢⊑ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

end FFL.FirstOrder.Concatenation

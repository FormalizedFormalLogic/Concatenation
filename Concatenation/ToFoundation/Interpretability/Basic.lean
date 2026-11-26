module

public import Foundation.FirstOrder.LK.Interpretation

/-!
# Non-interpretability

The negation of direct interpretability, and its transfer along interpretations; interpretations
that are not relativized.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- `T` does not directly interpret `U`. -/
abbrev NotInterprets {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T]
    (U : Theory L₂) : Prop := IsEmpty (T ⊳ U)

@[inherit_doc]
infix:50 " ⋫ " => NotInterprets

variable {L₁ L₂ L₃ : Language} [L₁.Eq] [L₂.Eq] [L₃.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

lemma notInterprets_iff : T ⋫ U ↔ ¬Nonempty (T ⊳ U) := not_nonempty_iff.symm

namespace NotInterprets

variable [𝗘𝗤 _ ⪯ U] {V : Theory L₃}

/-- A theory interpreted in `T` does not interpret what `T` does not interpret. -/
lemma of_left (h : T ⋫ V) (π : T ⊳ U) : U ⋫ V := ⟨fun ρ ↦ h.false (ρ.comp π)⟩

/-- `T` does not interpret a theory that interprets what `T` does not interpret. -/
lemma of_right (h : T ⋫ V) (π : U ⊳ V) : T ⋫ U := ⟨fun ρ ↦ h.false (π.comp ρ)⟩

end NotInterprets

/--
`T` interprets `U` on its whole universe, preserving equality.
- [Mur23, Definition 198]
-/
def UnrelativizedInterprets (T : Theory L₁) [𝗘𝗤 _ ⪯ T] (U : Theory L₂) : Prop :=
  ∃ π : T ⊳ U, T ⊢ “∀ x, %(π.trln.domain) x”

end FFL.FirstOrder

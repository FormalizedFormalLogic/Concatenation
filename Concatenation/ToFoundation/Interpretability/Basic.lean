module

public import Foundation.FirstOrder.LK.Interpretation

/-!
# Non-interpretability

The negation of direct interpretability, and its transfer along interpretations.
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

variable [𝗘𝗤 _ ⪯ U] {S : Theory L₃}

/-- A theory interpreted in `T` does not interpret what `T` does not interpret. -/
lemma of_left (h : T ⋫ S) (π : T ⊳ U) : U ⋫ S := ⟨fun ρ ↦ h.false (ρ.comp π)⟩

/-- `T` does not interpret a theory that interprets what `T` does not interpret. -/
lemma of_right (h : T ⋫ S) (π : U ⊳ S) : T ⋫ U := ⟨fun ρ ↦ h.false (π.comp ρ)⟩

end NotInterprets

end FFL.FirstOrder

module

public import AlphaCentauri.Interpretability.Basic

/-!
# Unrelativized interpretations

Interpretations whose domain is the whole universe.
-/

@[expose] public section

namespace FFL.FirstOrder

/--
`T` interprets `U` on its whole universe, preserving equality.
- [Mur23, Definition 198]
-/
def UnrelativizedInterprets {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T]
    (U : Theory L₂) : Prop := ∃ π : T ⊳ U, T ⊢ “∀ x, %(π.trln.domain) x”

end FFL.FirstOrder

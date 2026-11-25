module

public import AlphaCentauri.Interpretability.Basic

/-!
# Bi-interpretability
-/

@[expose] public section

namespace FFL.FirstOrder

/--
A self-interpretation of `T` is isomorphic to the identity if a formula defines, in every model, an
isomorphism onto the model interpreted in it.
- [Mur24a, §5]
-/
def DirectInterpretation.IsIsomorphicToId {L : Language.{0}} [L.Eq] {T : Theory L} [𝗘𝗤 _ ⪯ T]
    (π : T ⊳ T) : Prop :=
  ∃ F : Semisentence L 2, ∀ (M : Type) [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M]
    [M↓[L] ⊧* T], ∃ e : M ≃ₛ[L] π.Model M, ∀ x y : M, M ⊧/![x, y] F ↔ (e x : M) = y

/--
A bi-interpretation of `T` and `U`: interpretations in both directions whose two composites are
definably isomorphic to the identity.
- [Mur24a, §5]
-/
structure BiInterpretation {L₁ L₂ : Language.{0}} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T]
    (U : Theory L₂) [𝗘𝗤 _ ⪯ U] extends T ⋈ U where
  isIsomorphicToId_left : (l.comp r).IsIsomorphicToId
  isIsomorphicToId_right : (r.comp l).IsIsomorphicToId

end FFL.FirstOrder

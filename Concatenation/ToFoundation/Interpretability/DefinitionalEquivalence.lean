module

public import AlphaCentauri.Interpretability.Basic

/-!
# Definitional equivalence
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq]

/--
A definitional equivalence of `T` and `U`: interpretations in both directions with the whole domain,
inverse to each other up to provable equivalence.
- [Vis09, §1.4]
-/
structure DefinitionalEquivalence (T : Theory L₁) [𝗘𝗤 L₁ ⪯ T] (U : Theory L₂) [𝗘𝗤 L₂ ⪯ U] where
  r : T ⊳ U
  l : U ⊳ T
  domain_r : T ⊢ “∀ x, %r.trln.domain x”
  domain_l : U ⊢ “∀ x, %l.trln.domain x”
  rel_r {k} (R : L₁.Rel k) :
    T ⊢ ∀¹* (r.trln.translate (l.trln.rel R).sentence 🡘 Semiformula.rel R (#·))
  rel_l {k} (R : L₂.Rel k) :
    U ⊢ ∀¹* (l.trln.translate (r.trln.rel R).sentence 🡘 Semiformula.rel R (#·))
  func_r {k} (F : L₁.Func k) :
    T ⊢ ∀¹* (r.trln.translate (l.trln.func F).sentence 🡘 “z. z = !!(Semiterm.func F (#·.succ))”)
  func_l {k} (F : L₂.Func k) :
    U ⊢ ∀¹* (l.trln.translate (r.trln.func F).sentence 🡘 “z. z = !!(Semiterm.func F (#·.succ))”)

end FFL.FirstOrder

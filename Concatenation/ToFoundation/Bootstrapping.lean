module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Quotation of substitution

The internal substitution of a closed term into a formula agrees with the code of the substituted
sentence.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L : Language} [L.Encodable]
  [L.LORDefinable]

lemma substs1_app_quote (σ : Semisentence L 1) (t : ClosedSemiterm L 0) :
    substs1 L (⌜t⌝ : V) ⌜σ⌝ = ⌜(σ/[t] : Sentence L)⌝ := by
  simp [substs1, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]
  rfl

end FFL.FirstOrder.Arithmetic.Bootstrapping

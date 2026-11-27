module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Numerals in models of $\mathsf{R}_0$

The successor of a numeral is a numeral, and a $\Delta_0$ formula has at numerals the value it has
in `ℕ`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure
open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗥₀]

@[simp, grind =]
lemma numeral_add_one_of_R0 (n : ℕ) : (numeral n : V) + 1 = numeral (n + 1) := by
  simpa using numeral_add_numeral (M := V) n 1

lemma eval_numeral_iff_nat {k : ℕ} (φ : 𝚺ᴬ₀.Semisentence k) (v : Fin k → ℕ) :
    V ⊧/(numeral ∘ v) φ.val ↔ ℕ ⊧/v φ.val := by
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := V) (σ := ∼φ.val) (by simp) (bv := v)
      (by simpa using h')
    exact absurd h (by simpa using this)
  · exact bold_sigma_one_completeness' φ.sigma_prop.of_zero

end FFL.FirstOrder.Arithmetic

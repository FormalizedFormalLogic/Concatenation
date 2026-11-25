module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# $\mathsf{PA}^-$ with powers of two
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/-- `x` divides `y`. -/
def divides : ArithmeticSemisentence 2 := “x y. ∃ z, z * x = y”

/--
`x` is a power of two in the sense of Smullyan.
- [Vis24, §3.1]
-/
def isPowerOfTwo : ArithmeticSemisentence 1 :=
  “x. ∀ y, !divides y x → y = 1 ∨ !divides (1 + 1) y”

/--
Axioms of $\mathsf{PA}^-_{\mathsf{smu}}$.
- [Vis24, §3.1]
-/
inductive IsPeanoMinusSmullyanAxiom : ArithmeticSentence → Prop
  | peanoMinus : ∀ φ ∈ 𝗣𝗔⁻, IsPeanoMinusSmullyanAxiom φ
  | existsPower : IsPeanoMinusSmullyanAxiom
      “∀ x, ∃ y, !isPowerOfTwo y ∧ y ≤ x + 1 ∧ x + 1 < (1 + 1) * y”
  | powerDvd : IsPeanoMinusSmullyanAxiom
      “∀ x y, !isPowerOfTwo x → !isPowerOfTwo y → x ≤ y → !divides x y”

/--
The theory $\mathsf{PA}^-_{\mathsf{smu}}$: $\mathsf{PA}^-$, the existence of powers of two and the
division of powers of two.
- [Vis24, §3.1]
-/
abbrev PeanoMinusSmullyan : ArithmeticTheory := Set.ofPred IsPeanoMinusSmullyanAxiom

instance : 𝗣𝗔⁻ ⪯ PeanoMinusSmullyan :=
  Entailment.WeakerThan.ofSubset IsPeanoMinusSmullyanAxiom.peanoMinus

instance : 𝗘𝗤 ℒₒᵣ ⪯ PeanoMinusSmullyan :=
  Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance

end FFL.FirstOrder.Arithmetic

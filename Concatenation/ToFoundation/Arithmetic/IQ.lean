module

public import Foundation.FirstOrder.Arithmetic.Q.Basic

/-!
# The theory $\mathsf{IQ}$
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

/--
Axioms of the theory $\mathsf{IQ}$: those of $\mathsf{Q}$ where a description of the elements below
each numeral replaces the axiom that every nonzero element is a successor. The successor of $x$ is
$x + 1$, and $1$ is the successor of $0$.
- [Mur24, §1]
-/
inductive IsIQAxiom : ArithmeticSentence → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₒᵣ, IsIQAxiom φ
  | zeroSucc : IsIQAxiom “0 + 1 = 1”
  | succInj : IsIQAxiom “∀ x y, x ≠ y → x + 1 ≠ y + 1”
  | succNeZero : IsIQAxiom “∀ x, x + 1 ≠ 0”
  | leNumeral (n : ℕ) : IsIQAxiom “∀ x, x ≤ ↑n ↔ ⋁ k < n + 1, x = ↑k”
  | addZero : IsIQAxiom “∀ x, x + 0 = x”
  | addSucc : IsIQAxiom “∀ x y, x + (y + 1) = (x + y) + 1”
  | mulZero : IsIQAxiom “∀ x, x * 0 = 0”
  | mulSucc : IsIQAxiom “∀ x y, x * (y + 1) = x * y + x”

/--
The theory $\mathsf{IQ}$.
- [Mur24, §1]
-/
abbrev IQ : ArithmeticTheory := Set.ofPred IsIQAxiom

@[inherit_doc]
notation "𝗜𝗤" => IQ

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗤 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsIQAxiom.equal φ hφ

end FFL.FirstOrder.Arithmetic

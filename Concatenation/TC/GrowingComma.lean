module

public import Concatenation.TC.Empty

/-!
# $\mathsf{TC}$ with growing commas
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
`x` is a substring of `y`.
- [Vis24, §4.1]
-/
def isPartOf : Semisentence ℒ⌢ₑ 2 := “x y. ∃ u v, y = (u ⌢ x) ⌢ v”

/--
`x` is a string of letters $0$: the letter $1$ is not a substring of it.
- [Vis24, §4.3]
-/
def isZeroString : Semisentence ℒ⌢ₑ 1 := “x. ¬!isPartOf (!!(op(1).const)) x”

/--
Axioms of $\mathsf{TC}$ with growing commas.
- [Vis24, §4.1, Open Question 7.1]
-/
inductive IsTCGrowingCommaAxiom : Sentence ℒ⌢ₑ → Prop
  | tcEmpty : ∀ φ ∈ 𝗧𝗖ₑ, IsTCGrowingCommaAxiom φ
  | eqEmpty : IsTCGrowingCommaAxiom “∀ x y, x ⌢ y = ⋆ → x = ⋆ ∧ y = ⋆”
  | atom : IsTCGrowingCommaAxiom
      “∀ x, x ≠ ⋆ → (∀ y z, y ⌢ z = x → y = ⋆ ∨ z = ⋆) →
        x = !!(op(0).const) ∨ x = !!(op(1).const)”
  | comma : IsTCGrowingCommaAxiom
      “∀ x, ∃ y, !isZeroString y ∧
        ∀ u, !isPartOf u x → !isZeroString u → !isPartOf u y ∧ ¬!isPartOf y u”

/--
The theory of concatenation with the empty string whose only atoms are $0$ and $1$, and where for
each string $x$ a string of letters $0$ contains all such strings contained in $x$ and is contained
in none of them.
- [Vis24, §4.1, Open Question 7.1]
-/
abbrev TCGrowingComma : Theory ℒ⌢ₑ := Set.ofPred IsTCGrowingCommaAxiom

instance : 𝗧𝗖ₑ ⪯ TCGrowingComma := Entailment.WeakerThan.ofSubset IsTCGrowingCommaAxiom.tcEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ TCGrowingComma :=
  Entailment.WeakerThan.trans (𝓣 := 𝗧𝗖ₑ) inferInstance inferInstance

end FFL.FirstOrder.Concatenation

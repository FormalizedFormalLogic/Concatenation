module

public import Concatenation.BuildingBlocks.Basic
public import Concatenation.SetTheory.Sequential
public import Concatenation.ToFoundation.Interpretability.BiInterpretation
public import Concatenation.ToFoundation.Interpretability.DefinitionalEquivalence
public import Concatenation.ToFoundation.Interpretability.Relative
public import Concatenation.Tree.Basic
import Concatenation.OpenProblem

/-!
# Open problems on theories of building blocks, sets and trees
-/

@[expose] public section

namespace FFL.FirstOrder

namespace BuildingBlocks

/--
Is $\mathsf{BB}^-$, with the axioms that there are $n$ distinct atoms for each $n$, mutually
interpretable with $\mathsf{BB}$?
- [Mur24a, §5]
-/
open_problem BBMinus_mutuallyInterpretable_BB :=
  RelativelyInterprets 𝗕𝗕⁻ 𝗕𝗕 ∧ RelativelyInterprets 𝗕𝗕 𝗕𝗕⁻

/--
Is $\mathsf{BB}^-$, with the axioms that there are $n$ distinct atoms for each $n$, mutually
interpretable with the theory that has instead the axiom that there are three distinct atoms?
- [Mur24a, §5]
-/
open_problem BBMinus_mutuallyInterpretable_BBAtoms_three :=
  RelativelyInterprets 𝗕𝗕⁻ (BBAtoms 3) ∧ RelativelyInterprets (BBAtoms 3) 𝗕𝗕⁻

/--
The theories $\mathsf{AS}$, $\mathsf{AS}^+$, $\mathsf{BB}$, $\mathsf{BB}'$ and $\mathsf{BT}$, which
are mutually directly interpretable.
- [Mur24a, Theorem 4.6]
-/
inductive SetCoding
  | AS | ASPlus | BB | BBDisjoint | unorderedTree

namespace SetCoding

/-- The language of the theory. -/
abbrev language : SetCoding → Language.{0}
  | AS | ASPlus => ℒₛₑₜ
  | BB | BBDisjoint => ℒ⊑
  | unorderedTree => Language.unorderedTree

instance : ∀ i : SetCoding, i.language.Eq
  | AS | ASPlus => inferInstanceAs (Language.Eq ℒₛₑₜ)
  | BB | BBDisjoint => inferInstanceAs (Language.Eq ℒ⊑)
  | unorderedTree => inferInstanceAs (Language.Eq Language.unorderedTree)

/-- The theory. -/
abbrev theory : (i : SetCoding) → Theory i.language
  | AS => 𝗔𝗦
  | ASPlus => 𝗔𝗦⁺
  | BB => 𝗕𝗕
  | BBDisjoint => BuildingBlocks.BBDisjoint
  | unorderedTree => Tree.UnorderedTreeTheory

instance : ∀ i : SetCoding, 𝗘𝗤 i.language ⪯ i.theory
  | AS => inferInstanceAs (𝗘𝗤 _ ⪯ 𝗔𝗦)
  | ASPlus => inferInstanceAs (𝗘𝗤 _ ⪯ 𝗔𝗦⁺)
  | BB => (inferInstance : 𝗘𝗤 ℒ⊑ ⪯ 𝗕𝗕)
  | BBDisjoint => (inferInstance : 𝗘𝗤 ℒ⊑ ⪯ BuildingBlocks.BBDisjoint)
  | unorderedTree => inferInstanceAs (𝗘𝗤 _ ⪯ Tree.UnorderedTreeTheory)

end SetCoding

/--
Which of the theories $\mathsf{AS}$, $\mathsf{AS}^+$, $\mathsf{BB}$, $\mathsf{BB}'$ and
$\mathsf{BT}$ are synonymous?
- [Mur24a, §5]
-/
open_problem setCoding_definitionallyEquivalent (i j : SetCoding) (_ : i ≠ j) :=
  Nonempty (DefinitionalEquivalence i.theory j.theory)

/--
Which of the theories $\mathsf{AS}$, $\mathsf{AS}^+$, $\mathsf{BB}$, $\mathsf{BB}'$ and
$\mathsf{BT}$ are bi-interpretable?
- [Mur24a, §5]
-/
open_problem setCoding_biInterpretable (i j : SetCoding) (_ : i ≠ j) :=
  Nonempty (BiInterpretation i.theory j.theory)

end BuildingBlocks

namespace Tree

/--
Does $\mathsf{T}^{(1)}$, the theory of full binary trees where no tree is a subtree of its left
immediate subtree, directly interpret adjunctive set theory?
- [Mur23, Open Problem 208]
-/
open_problem TreeTheoryLeft_sequential := TreeTheoryLeft.Sequential

end Tree

end FFL.FirstOrder

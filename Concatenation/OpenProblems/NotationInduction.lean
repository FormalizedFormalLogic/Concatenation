module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Biteral
public import Concatenation.TC.Empty
public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy
import Concatenation.OpenProblem

/-!
# An open problem on notation induction
-/

@[expose] public section

open scoped FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

/--
The formulas with at most `s` alternating blocks of quantifiers in front of a bounded formula.
- [HH14, Question 3]
-/
inductive Bounding.BlockHierarchy {L : Language} {ξ : Type*} (ℬ : Bounding L) :
    Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | bounded {Γ : Polarity} {s n : ℕ} {φ : Semiformula L ξ n} :
    ℬ.Closure φ → ℬ.BlockHierarchy Γ s φ
  | sigma {s n : ℕ} {φ : Semiformula L ξ n} :
    ℬ.BlockHierarchy 𝚷 s φ → ℬ.BlockHierarchy 𝚺 (s + 1) φ
  | pi {s n : ℕ} {φ : Semiformula L ξ n} :
    ℬ.BlockHierarchy 𝚺 s φ → ℬ.BlockHierarchy 𝚷 (s + 1) φ
  | exs {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.BlockHierarchy 𝚺 (s + 1) φ → ℬ.BlockHierarchy 𝚺 (s + 1) (∃¹ φ)
  | all {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.BlockHierarchy 𝚷 (s + 1) φ → ℬ.BlockHierarchy 𝚷 (s + 1) (∀¹ φ)

namespace Concatenation

/--
Quantifiers are bounded by the relation of being a substring.
- [HH14, Question 3]
-/
def substringBounding : Bounding ℒ⌢ₑ := ⟨{⟨isSubstring⟩}⟩

/--
Notation induction for `φ`.
- [HH14, Question 3]
-/
def notationInduction {ξ : Type*} (φ : Semiformula ℒ⌢ₑ ξ 1) : Formula ℒ⌢ₑ ξ :=
  “!φ ⋆ → (∀ x, !φ x → !φ (x ⌢ !!(op(0).const)) ∧ !φ (x ⌢ !!(op(1).const))) → ∀ x, !φ x”

/--
Axioms of the theory $\Sigma_n\text{-}\mathsf{TCI}$.
- [HH14, Question 3]
-/
inductive IsTCISigmaAxiom (n : ℕ) : Sentence ℒ⌢ₑ → Prop
  | tcEmpty : ∀ φ ∈ 𝗧𝗖ₑ, IsTCISigmaAxiom n φ
  | notationInduction (φ : Semiformula ℒ⌢ₑ ℕ 1) : substringBounding.BlockHierarchy 𝚺 n φ →
      IsTCISigmaAxiom n (notationInduction φ).univCl

/--
The theory $\Sigma_n\text{-}\mathsf{TCI}$: $\mathsf{TC}$ with the empty string and notation
induction for the $\Sigma_n$ formulas.
- [HH14, Question 3]
-/
abbrev TCISigma (n : ℕ) : Theory ℒ⌢ₑ := Set.ofPred (IsTCISigmaAxiom n)

variable {n : ℕ}

instance : 𝗧𝗖ₑ ⪯ TCISigma n := Entailment.WeakerThan.ofSubset IsTCISigmaAxiom.tcEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ TCISigma n :=
  Entailment.WeakerThan.trans (𝓣 := 𝗧𝗖ₑ) inferInstance inferInstance

/--
Are $\Sigma_n\text{-}\mathsf{TCI}$ and $\mathsf{I}\Sigma_n$ mutually interpretable for each $n$?
- [HH14, Question 3]
-/
open_problem TCISigma_mutuallyInterpretable_ISigma := ∀ n : ℕ, Nonempty (TCISigma n ⋈ 𝗜𝚺 n)

end Concatenation

end FFL.FirstOrder

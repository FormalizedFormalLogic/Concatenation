module

public import Concatenation.ToFoundation.Interpretability.Relative
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
import Concatenation.OpenProblem

/-!
# Open problems on Rosser theories
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

namespace Numeral

inductive Func : ℕ → Type
  | zero : Func 0
  | succ : Func 1

inductive Rel : ℕ → Type
  | eq : Rel 2

end Numeral

/--
The language of zero and the successor.
- [Che24, Definition 1.4]
-/
@[reducible]
def numeral : Language where
  Func := Numeral.Func
  Rel := Numeral.Rel

instance : Language.numeral.Eq := ⟨Numeral.Rel.eq⟩

end Language

namespace Numeral

/--
The term denoting a natural number.
- [Che24, Definition 1.4]
-/
def numeralTerm {ξ : Type*} {n : ℕ} : ℕ → Semiterm Language.numeral ξ n
  | 0 => .func Language.Numeral.Func.zero ![]
  | m + 1 => .func Language.Numeral.Func.succ ![numeralTerm m]

/--
Axioms of the theory $\mathsf{Num}$.
- [Che24, Definition 1.4]
-/
inductive IsNumAxiom : Sentence Language.numeral → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 Language.numeral, IsNumAxiom φ
  | ne {m n : ℕ} : m ≠ n → IsNumAxiom “!!(numeralTerm m) ≠ !!(numeralTerm n)”

/--
The theory $\mathsf{Num}$: distinct numbers have distinct numerals.
- [Che24, Definition 1.4]
-/
abbrev Num : Theory Language.numeral := Set.ofPred IsNumAxiom

end Numeral

open Numeral

variable {L : Language.{0}} [L.Eq] {n : ℕ}

namespace RelativeTranslation

/--
`T` proves `φ` of the numerals of `a` interpreted by `τ`: in every model of `T`, every tuple of
elements denoting them satisfies `φ`.
- [Che24, Definition 1.5]
-/
def ProvesAt (τ : RelativeTranslation L Language.numeral) (T : Theory L)
    (φ : Semisentence L (n * τ.dim)) (a : Fin n → ℕ) : Prop :=
  ∀ (M : Type) [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M], M↓[L] ⊧* T →
    ∀ (N : Type) [Tarski.Structure Language.numeral N] (f : τ.Dom M → N), τ.Represents f →
      ∀ w : Fin n → τ.Dom M,
        (∀ i, f (w i) = (numeralTerm (a i) : ClosedTerm Language.numeral).valb ![]) →
        M ⊧/(flatten fun i ↦ (w i).1) φ

/--
A one-dimensional interpretation of $\mathsf{Num}$ in `T`.
- [Che24, Definition 2.1]
-/
structure IsNumeralInterpretation (τ : RelativeTranslation L Language.numeral) (T : Theory L) :
    Prop where
  dim_eq : τ.dim = 1
  interprets : τ.Interprets T Num

end RelativeTranslation

namespace Theory

variable (n) (T : Theory L)

/--
`T` is $n$-Rosser.
- [Che24, Definition 1.6]
-/
def Rosser : Prop :=
  ∃ τ : RelativeTranslation L Language.numeral, τ.IsNumeralInterpretation T ∧
    ∀ R S : (Fin n → ℕ) → Prop, REPred R → REPred S → ∃ φ, ∀ a,
      (R a → ¬S a → τ.ProvesAt T φ a) ∧ (S a → ¬R a → τ.ProvesAt T (∼φ) a)

/--
`T` is exact $n$-Rosser.
- [Che24, Definition 1.6]
-/
def ExactRosser : Prop :=
  ∃ τ : RelativeTranslation L Language.numeral, τ.IsNumeralInterpretation T ∧
    ∀ R S : (Fin n → ℕ) → Prop, REPred R → REPred S → (∀ a, R a → ¬S a) → ∃ φ, ∀ a,
      (R a ↔ τ.ProvesAt T φ a) ∧ (S a ↔ τ.ProvesAt T (∼φ) a)

end Theory

/--
Does $1$-Rosser imply exact $1$-Rosser?
- [Che24, Question 7.6]
-/
open_problem exactRosser_one_of_rosser_one :=
  ∀ (L : Language.{0}) [L.Encodable] [L.Primcodable] [L.Eq] (T : Theory L), 𝗘𝗤 L ⪯ T →
    Entailment.Consistent T → REPred (fun σ : Sentence L ↦ σ ∈ T) → T.Rosser 1 → T.ExactRosser 1

/--
Does $n$-Rosser imply exact $n$-Rosser for each $n \geq 1$?
- [Che24, Question 7.6]
-/
open_problem exactRosser_of_rosser :=
  ∀ n ≥ 1, ∀ (L : Language.{0}) [L.Encodable] [L.Primcodable] [L.Eq] (T : Theory L), 𝗘𝗤 L ⪯ T →
    Entailment.Consistent T → REPred (fun σ : Sentence L ↦ σ ∈ T) → T.Rosser n → T.ExactRosser n

end FFL.FirstOrder

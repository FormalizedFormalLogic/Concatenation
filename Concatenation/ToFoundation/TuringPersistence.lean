module

public import Foundation.FirstOrder.LK.Basic
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
public import Foundation.Logic.Decidability
public import Mathlib.Computability.TuringDegree

/-!
# Turing-persistent theories
-/

@[expose] public section

open scoped Computability

namespace FFL.FirstOrder

open Classical in
/-- The characteristic function of `p`, as an oracle. -/
noncomputable def oracle (p : ℕ → Prop) : ℕ →. ℕ := fun n ↦ Part.some (if p n then 1 else 0)

namespace Theory

variable {L : Language} [L.Encodable] [L.Primcodable]

/-- The set of the codes of the theorems of `T`, as an oracle. -/
noncomputable def oracle (T : Theory L) : ℕ →. ℕ :=
  FirstOrder.oracle fun n ↦ ∃ σ : Sentence L, Encodable.encode σ = n ∧ T ⊢ σ

/--
`T` is computably enumerable and consistent, and computable in each computably enumerable
consistent extension of `T`.
- [PMV23, §4.3]
- [Mur23, §IX.4]
-/
structure TuringPersistent (T : Theory L) : Prop where
  re : REPred fun σ : Sentence L ↦ σ ∈ T
  consistent : Entailment.Consistent T
  turingReducible (U : Theory L) : T ⪯ U → (REPred fun σ : Sentence L ↦ σ ∈ U) →
    Entailment.Consistent U → T.oracle ≤ᵀ U.oracle

/--
Every computably enumerable consistent extension of `T` is Turing-persistent.
- [PMV23, Open Question 4.11]
- [Mur23, Open Problem 226]
-/
structure EssentiallyTuringPersistent (T : Theory L) : Prop where
  re : REPred fun σ : Sentence L ↦ σ ∈ T
  consistent : Entailment.Consistent T
  turingPersistent (U : Theory L) : T ⪯ U → (REPred fun σ : Sentence L ↦ σ ∈ U) →
    Entailment.Consistent U → U.TuringPersistent

end Theory

end FFL.FirstOrder

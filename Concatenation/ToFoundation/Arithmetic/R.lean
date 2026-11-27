module

public import Concatenation.ToFoundation.Arithmetic.R0.Basic

/-!
# The theory $\mathsf{R}$ of Tarski, Mostowski and Robinson

$\mathsf{R}$ extends $\mathsf{R}_0$ by the comparability of every element with every numeral.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure

/--
The axioms of $\mathsf{R}$: those of $\mathsf{R}_0$, and the comparability of every element with
every numeral.
- [Hor11, §3, Definition 3.1]
- [Sve08, §3.3]
-/
inductive IsRAxiom : ArithmeticSentence → Prop
  | r0 : ∀ φ ∈ 𝗥₀, IsRAxiom φ
  | Ω₅ (n : ℕ) : IsRAxiom “∀ x, x ≤ ↑n ∨ ↑n ≤ x”

/--
The theory $\mathsf{R}$ of Tarski, Mostowski and Robinson.
- [Hor11, §3, Definition 3.1]
- [Sve08, §3.3]
-/
abbrev R : ArithmeticTheory := Set.ofPred IsRAxiom

@[inherit_doc]
notation "𝗥" => R

namespace R

instance : 𝗥₀ ⪯ 𝗥 := Entailment.WeakerThan.ofSubset IsRAxiom.r0

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗥 := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance

section

variable {V : Type*} [ORingStructure V]

lemma models_iff_models_R0 : V↓[ℒₒᵣ] ⊧* 𝗥 ↔
    V↓[ℒₒᵣ] ⊧* 𝗥₀ ∧ ∀ (n : ℕ) (x : V), x = numeral n ∨ x < numeral n ∨ numeral n < x := by
  have hΩ (n : ℕ) : V↓[ℒₒᵣ] ⊧ (“∀ x, x ≤ ↑n ∨ ↑n ≤ x” : ArithmeticSentence) ↔
      ∀ x : V, x = numeral n ∨ x < numeral n ∨ numeral n < x := by
    simp [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]
    grind
  constructor
  · intro h
    and_intros
    · exact models_of_ss h IsRAxiom.r0
    · exact fun n ↦ (hΩ n).mp <| Theory.models V _ (IsRAxiom.Ω₅ n)
  · rintro ⟨h₀, h⟩
    constructor
    rintro σ (⟨_, hσ⟩ | n)
    · exact models_theory_iff.mp h₀ _ hσ
    · exact (hΩ n).mpr (h n)

instance [V↓[ℒₒᵣ] ⊧* 𝗥] : V↓[ℒₒᵣ] ⊧* 𝗥₀ := (models_iff_models_R0.mp inferInstance).1

end

instance : ℕ↓[ℒₒᵣ] ⊧* 𝗥 := by
  rw [models_iff_models_R0]
  and_intros
  · infer_instance
  · intro n x
    simpa using Nat.lt_trichotomy x n |>.elim (Or.inr ∘ Or.inl) (Or.imp_right Or.inr)

instance : Entailment.Consistent 𝗥 :=
  let : ℕ↓[ℒₒᵣ] ⊧* 𝗥 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

end R

end FFL.FirstOrder.Arithmetic

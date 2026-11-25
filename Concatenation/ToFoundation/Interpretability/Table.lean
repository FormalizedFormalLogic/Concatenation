module

public import AlphaCentauri.Bootstrapping.Interpretability.Translation
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Computability of direct translations

A direct translation of a finite language has a table, so it is computable on sentences.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic

namespace FFL.FirstOrder

namespace Arithmetic.Bootstrapping

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ι : ℕ → Type*}
  [∀ k, Encodable (ι k)] [Finite ((k : ℕ) × ι k)]

lemma exists_nth_pair_encode_eq (g : (k : ℕ) → ι k → V) :
    ∃ w : V, ∀ k (i : ι k), w.[⟪(k : V), (Encodable.encode i : V)⟫] = g k i := by
  let c : (k : ℕ) × ι k → ℕ := fun x ↦ Nat.pair x.1 (Encodable.encode x.2)
  have hc : Function.Injective c := by
    rintro ⟨k, i⟩ ⟨l, j⟩ h
    obtain ⟨rfl, h⟩ := Nat.pair_eq_pair.mp h
    simpa using h
  obtain ⟨N, hN⟩ := (Set.finite_range c).bddAbove
  let u : Fin (N + 1) → V := fun j ↦ Function.extend c (fun x ↦ g x.1 x.2) 0 j
  use matrixToVec u
  intro k i
  have h : c ⟨k, i⟩ < N + 1 := Nat.lt_succ_of_le <| hN <| Set.mem_range_self _
  rw [← coe_pair_eq_pair_coe]
  exact (matrixToVec_nth u ⟨c ⟨k, i⟩, h⟩).trans <| hc.extend_apply (fun x ↦ g x.1 x.2) 0 ⟨k, i⟩

end

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L₁ L₂ : Language} [L₁.Encodable]
  [L₁.LORDefinable] [L₁.Eq] [L₂.Encodable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

lemma exists_isTableOf (π : DirectTranslation T L₂) : ∃ tbl : V, IsTableOf π tbl := by
  have : Fintype ((k : ℕ) × L₂.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L₂.Rel k) := Language.Finite.rel
  obtain ⟨r, hr⟩ := exists_nth_pair_encode_eq fun k (R : L₂.Rel k) ↦ (⌜(π.rel R).sentence⌝ : V)
  obtain ⟨f, hf⟩ := exists_nth_pair_encode_eq fun k (f : L₂.Func k) ↦ (⌜(π.func f).sentence⌝ : V)
  have h₁ : (?[⌜π.domain.sentence⌝, r, f] : V).[1] = r := by simp
  have h₂ : (?[⌜π.domain.sentence⌝, r, f] : V).[2] = f := by simp [← one_add_one_eq_two]
  use ?[⌜π.domain.sentence⌝, r, f]
  constructor
  · simp [tableDomain]
  · intro k R
    rw [tableRel, h₁]
    exact hr k R
  · intro k F
    rw [tableFunc, h₂]
    exact hf k F

end Arithmetic.Bootstrapping

namespace DirectTranslation

open Arithmetic Arithmetic.Bootstrapping

variable {L₁ L₂ : Language} [L₁.Encodable] [L₁.Primcodable] [L₁.LORDefinable] [L₁.Eq]
  [L₂.Encodable] [L₂.Primcodable] [L₂.LORDefinable] [L₂.Eq] [L₂.Finite] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/-- Every direct translation of a finite language is computable on semisentences. -/
theorem computable_translate (π : DirectTranslation T L₂) {n : ℕ} :
    Computable fun σ : Semisentence L₂ n ↦ (π.translate σ : Semisentence L₁ n) := by
  obtain ⟨tbl, h⟩ := exists_isTableOf (V := ℕ) π
  apply computable_iff_sigma1_simulate (f := Bootstrapping.translate L₁ L₂ tbl) (by definability)
  intro σ
  rw [← Sentence.quote_eq_encode_nat, h.translate_quote_sentence, Sentence.quote_eq_encode_nat]

end DirectTranslation

end FFL.FirstOrder

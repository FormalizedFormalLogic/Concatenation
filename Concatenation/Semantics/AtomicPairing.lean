module

public import Concatenation.Semantics.Basic
public import Concatenation.ToMathlib.AtomicPairing

/-!
# Elementary equivalence of atomic pairings

Two concatenation structures that are atomic pairings with the same table of atoms satisfy the
same sentences.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open AtomicPairing

variable {S : Type*} {tbl : S → S → S → Prop} {M M' : Type*} [ConcatenationStructure M]
  [ConcatenationStructure M'] (F : AtomicPairing tbl M) (F' : AtomicPairing tbl M')
  (h₀ : ∃ s, (0 : M) = F.atom s ∧ (0 : M') = F'.atom s)
  (h₁ : ∃ s, (1 : M) = F.atom s ∧ (1 : M') = F'.atom s) {n : ℕ}

include h₀ h₁

lemma exists_similar_val (t : ClosedSemiterm ℒ⌢ n) :
    ∃ k, ∀ (d : ℕ) (ρ : Set (M × M')), ρ.Finite → F.Similar F' (d + k) ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) →
        ∃ ρ', ρ ⊆ ρ' ∧ ρ'.Finite ∧ F.Similar F' d ρ' ∧ (t.valb v, t.valb w) ∈ ρ' := by
  induction t with
  | bvar x => exact ⟨0, fun d ρ hρ h v w hvw ↦ ⟨ρ, subset_rfl, hρ, h, hvw x⟩⟩
  | fvar x => exact x.elim
  | func f t ih =>
    cases f with
    | zero =>
      obtain ⟨s, hs, hs'⟩ := h₀
      use 0
      intro d ρ hρ h v w _
      use insert (F.atom s, F'.atom s) ρ
      and_intros
      · exact Set.subset_insert _ _
      · exact hρ.insert _
      · exact h.insert_atom s
      · rw [← hs, ← hs']
        exact Set.mem_insert _ _
    | one =>
      obtain ⟨s, hs, hs'⟩ := h₁
      use 0
      intro d ρ hρ h v w _
      use insert (F.atom s, F'.atom s) ρ
      and_intros
      · exact Set.subset_insert _ _
      · exact hρ.insert _
      · exact h.insert_atom s
      · rw [← hs, ← hs']
        exact Set.mem_insert _ _
    | concat =>
      obtain ⟨k₁, hk₁⟩ := ih 0
      obtain ⟨k₂, hk₂⟩ := ih 1
      use k₁ + k₂ + 1
      intro d ρ hρ h v w hvw
      obtain ⟨ρ₁, hρρ₁, hρ₁, h', hm₁⟩ :=
        hk₁ (d + 1 + k₂) ρ hρ (h.mono (by omega) subset_rfl) v w hvw
      obtain ⟨ρ₂, hρ₁ρ₂, hρ₂, h'', hm₂⟩ := hk₂ (d + 1) ρ₁ hρ₁ h' v w fun i ↦ hρρ₁ (hvw i)
      use insert ((t 0).valb v ++ (t 1).valb v, (t 0).valb w ++ (t 1).valb w) ρ₂
      and_intros
      · exact (hρρ₁.trans hρ₁ρ₂).trans (Set.subset_insert _ _)
      · exact hρ₂.insert _
      · exact h''.insert_append (hρ₁ρ₂ hm₁) hm₂
      · exact Set.mem_insert _ _

lemma exists_similar_val_eq (t₁ t₂ : ClosedSemiterm ℒ⌢ n) :
    ∃ k, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' k ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) →
        (t₁.valb v = t₂.valb v ↔ t₁.valb w = t₂.valb w) := by
  obtain ⟨k₁, hk₁⟩ := exists_similar_val F F' h₀ h₁ t₁
  obtain ⟨k₂, hk₂⟩ := exists_similar_val F F' h₀ h₁ t₂
  use 0 + k₂ + k₁
  intro ρ hρ h v w hvw
  obtain ⟨ρ₁, hρρ₁, hρ₁, h', hm₁⟩ := hk₁ (0 + k₂) ρ hρ h v w hvw
  obtain ⟨ρ₂, hρ₁ρ₂, -, h'', hm₂⟩ := hk₂ 0 ρ₁ hρ₁ h' v w fun i ↦ hρρ₁ (hvw i)
  exact h''.eq_iff (hρ₁ρ₂ hm₁) hm₂

lemma exists_similar_eval (φ : Semisentence ℒ⌢ n) :
    ∃ k, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' k ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) → (M ⊧/v φ ↔ M' ⊧/w φ) := by
  induction φ using Semiformula.rec' with
  | hverum => exact ⟨0, fun _ _ _ _ _ _ ↦ by simp⟩
  | hfalsum => exact ⟨0, fun _ _ _ _ _ _ ↦ by simp⟩
  | hrel r t =>
    cases r
    obtain ⟨k, hk⟩ := exists_similar_val_eq F F' h₀ h₁ (t 0) (t 1)
    exact ⟨k, fun ρ hρ h v w hvw ↦ hk ρ hρ h v w hvw⟩
  | hnrel r t =>
    cases r
    obtain ⟨k, hk⟩ := exists_similar_val_eq F F' h₀ h₁ (t 0) (t 1)
    exact ⟨k, fun ρ hρ h v w hvw ↦ not_congr (hk ρ hρ h v w hvw)⟩
  | hand φ ψ ihφ ihψ =>
    obtain ⟨k₁, hk₁⟩ := ihφ
    obtain ⟨k₂, hk₂⟩ := ihψ
    use max k₁ k₂
    intro ρ hρ h v w hvw
    simpa using and_congr (hk₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) v w hvw)
      (hk₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) v w hvw)
  | hor φ ψ ihφ ihψ =>
    obtain ⟨k₁, hk₁⟩ := ihφ
    obtain ⟨k₂, hk₂⟩ := ihψ
    use max k₁ k₂
    intro ρ hρ h v w hvw
    simpa using or_congr (hk₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) v w hvw)
      (hk₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) v w hvw)
  | hall φ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨g₁, hg₁⟩ := F.exists_similar_insert F' k
    obtain ⟨g₂, hg₂⟩ := F.exists_similar_insert' F' k
    use max g₁ g₂
    intro ρ hρ h v w hvw
    have hc (a : M) (b : M') : ∀ i, ((a :> v) i, (b :> w) i) ∈ insert (a, b) ρ := by
      intro i
      cases i using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ i => exact Set.mem_insert_of_mem _ (hvw i)
    simp only [Semiformula.eval_all]
    constructor
    · intro ha b
      obtain ⟨a, hab⟩ := hg₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) b
      exact (hk _ (hρ.insert _) hab _ _ (hc a b)).mp (ha a)
    · intro hb a
      obtain ⟨b, hab⟩ := hg₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) a
      exact (hk _ (hρ.insert _) hab _ _ (hc a b)).mpr (hb b)
  | hexs φ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨g₁, hg₁⟩ := F.exists_similar_insert F' k
    obtain ⟨g₂, hg₂⟩ := F.exists_similar_insert' F' k
    use max g₁ g₂
    intro ρ hρ h v w hvw
    have hc (a : M) (b : M') : ∀ i, ((a :> v) i, (b :> w) i) ∈ insert (a, b) ρ := by
      intro i
      cases i using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ i => exact Set.mem_insert_of_mem _ (hvw i)
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hab⟩ := hg₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) a
      exact ⟨b, (hk _ (hρ.insert _) hab _ _ (hc a b)).mp ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, hab⟩ := hg₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) b
      exact ⟨a, (hk _ (hρ.insert _) hab _ _ (hc a b)).mpr hb⟩

/--
Two atomic pairings with the same table of atoms, in which each of the two letters is the same
atom, satisfy the same sentences.
-/
theorem models_iff_of_atomicPairing (σ : Sentence ℒ⌢) : M↓[ℒ⌢] ⊧ σ ↔ M'↓[ℒ⌢] ⊧ σ := by
  obtain ⟨k, hk⟩ := exists_similar_eval F F' h₀ h₁ σ
  exact hk ∅ Set.finite_empty (similar_empty k) ![] ![] fun i ↦ i.elim0

end FFL.FirstOrder.Concatenation

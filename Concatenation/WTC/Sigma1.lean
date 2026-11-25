module

public import Concatenation.WTC.Standard
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

/-!
# $\Sigma_1$-completeness of $\mathsf{WTC}$

The hierarchy of formulas of concatenation over quantifiers bounded by the substring relation, and
the $\Sigma_1$-completeness of $\mathsf{WTC}$ with respect to the nonempty binary strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {ξ : Type*} {n : ℕ}

/-- The substring relation as an operator. -/
def substringOperator : Semiformula.Operator ℒ⌢ 2 := ⟨isSubstring⟩

@[simp]
lemma val_substringOperator {v : Fin 2 → M} :
    substringOperator.val v ↔ IsSubstring (v 0) (v 1) := by
  rw [Matrix.fun_eq_vec_two (v := v)]
  exact eval_isSubstring

/--
Quantifiers bounded by the substring relation. `substringBounding.Hierarchy 𝚺 0` is the class of
$\Sigma_0$ formulas, and `substringBounding.Hierarchy 𝚺 1` the class of $\Sigma_1$ formulas.
- [Hor11, §3]
- [Hor12, §3]
-/
def substringBounding : Bounding ℒ⌢ := ⟨{substringOperator}⟩

@[inherit_doc]
scoped notation "ℬ[⊆]" => substringBounding

@[simp]
lemma mem_substringBounding_iff {R : Semiformula.Operator ℒ⌢ 2} :
    R ∈ ℬ[⊆] ↔ R = substringOperator := Iff.rfl

namespace WTC

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] {e : Fin n → FreeSemigroup Bool} {ε : ξ → FreeSemigroup Bool}
  {φ : Semiformula ℒ⌢ ξ n}

lemma val_ofFreeSemigroup (t : Semiterm ℒ⌢ ξ n) :
    t.val (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) = (ofFreeSemigroup (t.val e ε) : M) := by
  induction t with
  | bvar => simp
  | fvar => simp
  | @func k f v ih =>
    match k, f with
    | _, Language.Zero.zero => simp
    | _, Language.One.one => simp
    | _, Language.Concat.concat => simp [ih]

/-- $\Sigma_0$ formulas are absolute for the standard strings. -/
lemma eval_ofFreeSemigroup_iff_of_closure (hφ : ℬ[⊆].Closure φ) :
    φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) ↔ φ.Eval e ε := by
  induction hφ with
  | verum => simp
  | falsum => simp
  | @rel _ k r v =>
    match k, r with
    | _, Language.Eq.eq => simp [val_ofFreeSemigroup]
  | @nrel _ k r v =>
    match k, r with
    | _, Language.Eq.eq => simp [val_ofFreeSemigroup]
  | and _ _ ihφ ihψ => simp [ihφ, ihψ]
  | or _ _ ihφ ihψ => simp [ihφ, ihψ]
  | ball hR ht _ ih =>
    obtain rfl := mem_substringBounding_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    simp [val_ofFreeSemigroup, isSubstring_ofFreeSemigroup_iff, ← ih, Matrix.comp_vecCons'']
    grind
  | bexs hR ht _ ih =>
    obtain rfl := mem_substringBounding_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    simp [val_ofFreeSemigroup, isSubstring_ofFreeSemigroup_iff, ← ih, Matrix.comp_vecCons'']

/--
A $\Sigma_1$ formula true of some strings in the standard model is true of their values in every
model of $\mathsf{WTC}$.
- [Hor12, §3, Theorem 3.13]
-/
lemma eval_ofFreeSemigroup_of_hierarchy (hφ : ℬ[⊆].Hierarchy 𝚺 1 φ) (h : φ.Eval e ε) :
    φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) := by
  revert e
  apply Bounding.Hierarchy.sigma_succ_induction (s := 0) (P := fun n φ ↦ ∀ {e : Fin n → _},
    φ.Eval e ε → φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε))
  case a => exact hφ
  case hPi =>
    intro n φ hφ e
    exact (eval_ofFreeSemigroup_iff_of_closure <| Bounding.Hierarchy.zero_iff_bounded.mp hφ).mpr
  case hAnd => simp; grind
  case hOr => simp; grind
  case hBall =>
    rintro R rfl n t φ _ ih e h
    have h : ∀ v, IsSubstring v (t.val e ε) → φ.Eval (v :> e) ε := by simpa using h
    suffices ∀ x : M, IsSubstring x (ofFreeSemigroup (t.val e ε)) →
        φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by
      simpa [val_ofFreeSemigroup]
    intro x hx
    obtain ⟨v, rfl, hv⟩ := isSubstring_ofFreeSemigroup_iff.mp hx
    simpa [Matrix.comp_vecCons''] using ih <| h v hv
  case hBexs =>
    rintro R rfl n t φ _ ih e h
    obtain ⟨v, hv, h⟩ : ∃ v, IsSubstring v (t.val e ε) ∧ φ.Eval (v :> e) ε := by simpa using h
    suffices ∃ x : M, IsSubstring x (ofFreeSemigroup (t.val e ε)) ∧
        φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by
      simpa [val_ofFreeSemigroup]
    use ofFreeSemigroup v
    simpa [Matrix.comp_vecCons'', hv] using ih h
  case hExs =>
    intro n φ _ ih e h
    obtain ⟨v, h⟩ : ∃ v, φ.Eval (v :> e) ε := by simpa using h
    suffices ∃ x : M, φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by simpa
    use ofFreeSemigroup v
    simpa [Matrix.comp_vecCons''] using ih h

end WTC

/--
$\mathsf{WTC}$, and hence every extension of it, proves the $\Sigma_1$ sentences true of the
nonempty binary strings.
- [Hor11, §3, Theorem 3.8]
- [Hor12, §3, Theorem 3.13]
-/
theorem sigma1_completeness {T : ConcatenationTheory} [𝗪𝗧𝗖 ⪯ T] {σ : ConcatenationSentence}
    (hσ : ℬ[⊆].Hierarchy 𝚺 1 σ) (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : T ⊢ σ := by
  have : 𝗘𝗤 ℒ⌢ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖) inferInstance inferInstance
  apply complete.{0}
  intro M _ _
  have : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ModelsTheory.of_provably_subtheory M 𝗪𝗧𝗖 T inferInstance
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    WTC.eval_ofFreeSemigroup_of_hierarchy (M := M) hσ (models_iff.mp h)

end FFL.FirstOrder.Concatenation

module

public import Concatenation.TC.Substring
public import Concatenation.WTC.Basic

/-!
# Standard strings and $\Sigma_1$-completeness of $\mathsf{WTC}$

The standard strings form an initial part of every model of $\mathsf{WTC}$, so that $\mathsf{WTC}$
is $\Sigma_1$-complete.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

namespace WTC

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {a b c u v : FreeSemigroup Bool} {s t x y z : M}

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

lemma append_assoc (u : FreeSemigroup Bool) (h : IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
    IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u)) : x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCAxiom.concatAssoc u)
  exact this x y z h

lemma editor (u : FreeSemigroup Bool) (h : x ++ y = s ++ t)
    (hu : IsSubstring (x ++ y) (ofFreeSemigroup u)) : (x = s ∧ y = t) ∨
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCAxiom.editor u)
  exact this x y s t h hu

lemma append_ne_zero (x y : M) : x ++ y ≠ 0 := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCAxiom.concatNeZero
  exact this x y

lemma append_ne_one (x y : M) : x ++ y ≠ 1 := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCAxiom.concatNeOne
  exact this x y

protected lemma zero_ne_one : (0 : M) ≠ 1 := by
  simpa [models_iff] using Theory.models M _ IsWTCAxiom.zeroNeOne

lemma append_ne_ofFreeSemigroup (hc : IsAtom c) : x ++ y ≠ ofFreeSemigroup c := by
  rcases hc with rfl | rfl
  · exact append_ne_zero x y
  · exact append_ne_one x y

@[simp]
lemma ofFreeSemigroup_mul (u v : FreeSemigroup Bool) :
    (ofFreeSemigroup (u * v) : M) = ofFreeSemigroup u ++ ofFreeSemigroup v := by
  induction v using atom_append_induction with
  | atom c hc => exact ofFreeSemigroup_append_of_isAtom u hc
  | append v c hc ih =>
    have h := ofFreeSemigroup_append_of_isAtom (M := M) (u * v) hc
    rw [append_eq_mul, ih] at h
    rw [append_eq_mul, ← mul_assoc, h, ← append_eq_mul v, ofFreeSemigroup_append_of_isAtom v hc]
    apply append_assoc (u * v * c)
    left
    rw [h]

lemma ofFreeSemigroup_injective :
    Function.Injective (ofFreeSemigroup : FreeSemigroup Bool → M) := by
  intro u
  induction u using atom_append_induction with
  | atom c hc =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd =>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · rfl
      · exact absurd h WTC.zero_ne_one
      · exact absurd h.symm WTC.zero_ne_one
      · rfl
    | append v d hd => exact absurd (by simpa using h.symm) (append_ne_ofFreeSemigroup (M := M) hc)
  | append u c hc ih =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd => exact absurd (by simpa using h) (append_ne_ofFreeSemigroup (M := M) hd)
    | append v d hd =>
      simp only [append_eq_mul, ofFreeSemigroup_mul] at h
      rcases editor (u * c) h (by simp) with ⟨h₁, h₂⟩ | ⟨w, ⟨-, h⟩ | ⟨-, h⟩⟩
      · rw [ih h₁]
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · rfl
        · exact absurd h₂ WTC.zero_ne_one
        · exact absurd h₂.symm WTC.zero_ne_one
        · rfl
      · exact absurd h.symm (append_ne_ofFreeSemigroup hc)
      · exact absurd h (append_ne_ofFreeSemigroup hd)

@[simp]
lemma ofFreeSemigroup_inj : (ofFreeSemigroup u : M) = ofFreeSemigroup v ↔ u = v :=
  ofFreeSemigroup_injective.eq_iff

/--
If a concatenation is standard, then so are both parts.
- [Hor12, §3, Lemma 3.11]
-/
lemma exists_of_append_eq_ofFreeSemigroup (h : x ++ y = ofFreeSemigroup u) :
    ∃ a b, x = ofFreeSemigroup a ∧ y = ofFreeSemigroup b ∧ u = a * b := by
  induction u using atom_append_induction generalizing y with
  | atom c hc => exact absurd h (append_ne_ofFreeSemigroup hc)
  | append u c hc ih =>
    simp only [append_eq_mul, ofFreeSemigroup_mul] at h
    rcases editor (u * c) h (by simp [h]) with ⟨rfl, rfl⟩ | ⟨w, ⟨hw, rfl⟩ | ⟨-, hw⟩⟩
    · use u, c
      simp
    · obtain ⟨a, b, rfl, rfl, rfl⟩ := ih hw
      use a, b * c
      simp [mul_assoc]
    · exact absurd hw (append_ne_ofFreeSemigroup hc)

/--
The substrings of a standard string are the values of its substrings.
- [Hor12, §3, Lemma 3.11]
-/
lemma isSubstring_ofFreeSemigroup_iff :
    IsSubstring x (ofFreeSemigroup u) ↔ ∃ v, x = ofFreeSemigroup v ∧ IsSubstring v u := by
  constructor
  · intro h
    apply h.of_forall_append (P := fun x ↦ ∃ v, x = ofFreeSemigroup v ∧ IsSubstring v u) _
      ⟨u, rfl, .refl u⟩
    rintro x y ⟨v, h, hv⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h
    exact ⟨⟨a, rfl, (isSubstring_append_left a b).trans hv⟩,
      ⟨b, rfl, (isSubstring_append_right a b).trans hv⟩⟩
  · rintro ⟨v, rfl, h⟩
    rcases isSubstring_iff.mp h with rfl | ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, rfl⟩ <;> simp

@[simp]
lemma isSubstring_ofFreeSemigroup_ofFreeSemigroup_iff :
    IsSubstring (ofFreeSemigroup u : M) (ofFreeSemigroup v) ↔ IsSubstring u v := by
  simp [isSubstring_ofFreeSemigroup_iff]

@[simp]
lemma isAtom_ofFreeSemigroup_iff : IsAtom (ofFreeSemigroup u : M) ↔ IsAtom u := by
  rw [IsAtom, IsAtom, ← ofFreeSemigroup_zero, ← ofFreeSemigroup_one, ofFreeSemigroup_inj,
    ofFreeSemigroup_inj]

@[simp]
lemma isTally_ofFreeSemigroup_iff :
    IsTally (ofFreeSemigroup c : M) (ofFreeSemigroup u) ↔ IsTally c u := by
  constructor
  · intro h v hv hvu
    simpa using h (ofFreeSemigroup v) (by simpa) (by simpa)
  · intro h y hy hyu
    obtain ⟨v, rfl, hvu⟩ := isSubstring_ofFreeSemigroup_iff.mp hyu
    rw [h v (isAtom_ofFreeSemigroup_iff.mp hy) hvu]

end WTC

section sigma1

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {ξ : Type*} {n : ℕ}

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
lemma eval_ofFreeSemigroup_iff_of_closure (hφ : ℬ[⊑, ℒ⌢].Closure φ) :
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
lemma eval_ofFreeSemigroup_of_hierarchy (hφ : ℬ[⊑, ℒ⌢].Hierarchy 𝚺 1 φ) (h : φ.Eval e ε) :
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

lemma sigma1_completeness_of_hierarchy {T : ConcatenationTheory} [𝗪𝗧𝗖 ⪯ T]
    {σ : ConcatenationSentence}
    (hσ : ℬ[⊑, ℒ⌢].Hierarchy 𝚺 1 σ) (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : T ⊢ σ := by
  have : 𝗘𝗤 ℒ⌢ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖) inferInstance inferInstance
  apply complete.{0}
  intro M _ _
  have : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ModelsTheory.of_provably_subtheory M 𝗪𝗧𝗖 T inferInstance
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    WTC.eval_ofFreeSemigroup_of_hierarchy (M := M) hσ (models_iff.mp h)

/--
$\mathsf{WTC}$, and hence every extension of it, proves the $\Sigma_1$ sentences true of the
nonempty binary strings.
- [Hor11, §3, Theorem 3.8]
- [Hor12, §3, Theorem 3.13]
-/
theorem sigma1_completeness {T : ConcatenationTheory} [𝗪𝗧𝗖 ⪯ T] {σ : ConcatenationSentence}
    (hσ : ℬ[⊑, ℒ⌢].PrenexHierarchy 𝚺 1 σ) (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : T ⊢ σ :=
  sigma1_completeness_of_hierarchy hσ.hierarchy h

end sigma1

end FFL.FirstOrder.Concatenation

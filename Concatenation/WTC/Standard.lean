module

public import Concatenation.TC.Substring
public import Concatenation.WTC.Basic
public import Foundation.FirstOrder.Tarski.HierarchicalDefinability.Absoluteness

/-!
# Standard strings and $\Sigma_1$-completeness of $\mathsf{WTC}$

The standard strings form an initial part of every model of $\mathsf{WTC}$, so that $\mathsf{WTC}$
is $\Sigma_1$-complete.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

namespace WTC

open ConcatenationStructure

variable {V : Type*} [ConcatenationStructure V] {a b c u v : FreeSemigroup Bool} {s t x y z : V}

variable [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

lemma append_assoc (u : FreeSemigroup Bool) (h : IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
    IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u)) : x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models V _ (IsWTCAxiom.concatAssoc u)
  exact this x y z h

lemma editor (u : FreeSemigroup Bool) (h : x ++ y = s ++ t)
    (hu : IsSubstring (x ++ y) (ofFreeSemigroup u)) : (x = s ∧ y = t) ∨
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  have := by simpa [models_iff] using Theory.models V _ (IsWTCAxiom.editor u)
  exact this x y s t h hu

@[simp]
lemma append_ne_zero (x y : V) : x ++ y ≠ 0 := by
  have := by simpa [models_iff] using Theory.models V _ IsWTCAxiom.concatNeZero
  exact this x y

@[simp]
lemma append_ne_one (x y : V) : x ++ y ≠ 1 := by
  have := by simpa [models_iff] using Theory.models V _ IsWTCAxiom.concatNeOne
  exact this x y

@[simp]
protected lemma zero_ne_one : (0 : V) ≠ 1 := by
  simpa [models_iff] using Theory.models V _ IsWTCAxiom.zeroNeOne

@[simp]
protected lemma one_ne_zero : (1 : V) ≠ 0 := WTC.zero_ne_one.symm

lemma append_ne_ofFreeSemigroup (hc : IsAtom c) : x ++ y ≠ ofFreeSemigroup c := by
  rcases hc with rfl | rfl <;> simp

@[simp]
lemma ofFreeSemigroup_mul (u v : FreeSemigroup Bool) :
    (ofFreeSemigroup (u * v) : V) = ofFreeSemigroup u ++ ofFreeSemigroup v := by
  induction v using atom_append_induction with
  | atom c hc => exact ofFreeSemigroup_append_of_isAtom u hc
  | append v c hc ih =>
    have h := ofFreeSemigroup_append_of_isAtom (V := V) (u * v) hc
    rw [FreeSemigroup.append_eq_mul, ih] at h
    rw [FreeSemigroup.append_eq_mul, ← mul_assoc, h, ← FreeSemigroup.append_eq_mul v,
      ofFreeSemigroup_append_of_isAtom v hc]
    apply append_assoc (u * v * c)
    left
    rw [h]

lemma ofFreeSemigroup_injective :
    Function.Injective (ofFreeSemigroup : FreeSemigroup Bool → V) := by
  intro u
  induction u using atom_append_induction with
  | atom c hc =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd => rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
    | append v d hd => exact absurd (by simpa using h.symm) (append_ne_ofFreeSemigroup (V := V) hc)
  | append u c hc ih =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd => exact absurd (by simpa using h) (append_ne_ofFreeSemigroup (V := V) hd)
    | append v d hd =>
      simp only [FreeSemigroup.append_eq_mul, ofFreeSemigroup_mul] at h
      rcases editor (u * c) h (by simp) with ⟨h₁, h₂⟩ | ⟨w, ⟨-, h⟩ | ⟨-, h⟩⟩
      · rw [ih h₁]
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
      · exact absurd h.symm (append_ne_ofFreeSemigroup hc)
      · exact absurd h (append_ne_ofFreeSemigroup hd)

@[simp]
lemma ofFreeSemigroup_inj : (ofFreeSemigroup u : V) = ofFreeSemigroup v ↔ u = v :=
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
    simp only [FreeSemigroup.append_eq_mul, ofFreeSemigroup_mul] at h
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
    IsSubstring (ofFreeSemigroup u : V) (ofFreeSemigroup v) ↔ IsSubstring u v := by
  simp [isSubstring_ofFreeSemigroup_iff]

@[simp]
lemma isAtom_ofFreeSemigroup_iff : IsAtom (ofFreeSemigroup u : V) ↔ IsAtom u := by
  rw [IsAtom, IsAtom, ← ofFreeSemigroup_zero, ← ofFreeSemigroup_one, ofFreeSemigroup_inj,
    ofFreeSemigroup_inj]

@[simp]
lemma isTally_ofFreeSemigroup_iff :
    IsTally (ofFreeSemigroup c : V) (ofFreeSemigroup u) ↔ IsTally c u := by
  constructor
  · intro h v hv hvu
    simpa using h (ofFreeSemigroup v) (by simpa) (by simpa)
  · intro h y hy hyu
    obtain ⟨v, rfl, hvu⟩ := isSubstring_ofFreeSemigroup_iff.mp hyu
    rw [h v (isAtom_ofFreeSemigroup_iff.mp hy) hvu]

end WTC

section sigma1

open ConcatenationStructure Bounding

variable {V : Type*} [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

namespace WTC

/-- The values of the standard strings are an initial copy of the standard model. -/
def ofFreeSemigroupEmbedding (V : Type*) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] :
    (FreeSemigroup Bool) ↪ₛ[ℒ⌢] V where
  toFun := ofFreeSemigroup
  func' f v := by
    cases f
    · rfl
    · rfl
    · exact ofFreeSemigroup_mul (v 0) (v 1)
  rel' r v := by
    cases r
    exact congrArg ofFreeSemigroup
  toFun_inj := ofFreeSemigroup_injective
  rel_inv' r v := by
    cases r
    exact fun h ↦ ofFreeSemigroup_injective h

@[simp]
lemma ofFreeSemigroupEmbedding_apply (u : FreeSemigroup Bool) :
    ofFreeSemigroupEmbedding V u = ofFreeSemigroup u := rfl

instance : ℬ[⊑, ℒ⌢].IsInitial (ofFreeSemigroupEmbedding V) where
  operator_iff hR a b := by
    obtain rfl := mem_substringBounding_iff.mp hR
    simp
  initial hR a b h := by
    obtain rfl := mem_substringBounding_iff.mp hR
    obtain ⟨v, rfl, -⟩ := isSubstring_ofFreeSemigroup_iff.mp (by simpa using h)
    exact ⟨v, rfl⟩

end WTC

/--
$\mathsf{WTC}$ proves the $\Sigma_1$ sentences true of the nonempty binary strings.
- [Hor11, §3, Theorem 3.8]
- [Hor12, §3, Theorem 3.13]
-/
theorem sigma1_completeness {σ : ConcatenationSentence} (hσ : ℬ[⊑, ℒ⌢].Hierarchy 𝚺 1 σ)
    (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : 𝗪𝗧𝗖 ⊢ σ := by
  apply complete.{0}
  intro V _ _
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    sigma_one_upward (WTC.ofFreeSemigroupEmbedding V) hσ ![] Empty.elim (models_iff.mp h)

end sigma1

end FFL.FirstOrder.Concatenation

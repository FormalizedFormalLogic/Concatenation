module

public import Concatenation.Semantics.Standard
public import Concatenation.TC.Substring
public import Concatenation.WTC.Basic

/-!
# Standard strings in models of $\mathsf{WTC}$

The values of binary strings in a model of $\mathsf{WTC}$ form an isomorphic copy of the standard
model that is closed under substrings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

namespace WTC

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {a b c u v : FreeSemigroup Bool} {s t x y z : M}

@[simp]
lemma ofFreeSemigroup_zero : (ofFreeSemigroup (0 : FreeSemigroup Bool) : M) = 0 := rfl

@[simp]
lemma ofFreeSemigroup_one : (ofFreeSemigroup (1 : FreeSemigroup Bool) : M) = 1 := rfl

lemma ofFreeSemigroup_append_of_isAtom (u : FreeSemigroup Bool) (hc : IsAtom c) :
    (ofFreeSemigroup (u ++ c) : M) = ofFreeSemigroup u ++ ofFreeSemigroup c := by
  rcases hc with rfl | rfl <;>
    simp [ofFreeSemigroup, stringValue, HMul.hMul, Mul.mul, zero_eq_of_false, one_eq_of_true,
      FreeSemigroup.of]

/-- Induction on a nonempty binary string by its last letter. -/
@[elab_as_elim]
lemma atom_append_induction {motive : FreeSemigroup Bool → Prop} (u : FreeSemigroup Bool)
    (atom : ∀ c, IsAtom c → motive c)
    (append : ∀ u c, IsAtom c → motive u → motive (u ++ c)) : motive u := by
  have h (b : Bool) : IsAtom (FreeSemigroup.of b) := by
    cases b
    · exact isAtom_zero
    · exact isAtom_one
  rcases u with ⟨b, l⟩
  induction l using List.reverseRecOn with
  | nil => exact atom _ <| h b
  | append_singleton l d ih => exact append _ _ (h d) ih

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
  · rintro (rfl | ⟨s, h⟩ | ⟨t, h⟩ | ⟨s, t, h⟩ | ⟨s, t, h⟩)
    · use u
    · obtain ⟨a, b, -, rfl, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
      use b
      simp [← append_eq_mul]
    · obtain ⟨a, b, rfl, -, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
      use a
      simp [← append_eq_mul]
    · obtain ⟨a, b, ha, -, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
      obtain ⟨p, q, -, rfl, rfl⟩ := exists_of_append_eq_ofFreeSemigroup ha
      use q
      simp [← append_eq_mul]
    · obtain ⟨a, b, -, hb, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
      obtain ⟨p, q, rfl, -, rfl⟩ := exists_of_append_eq_ofFreeSemigroup hb
      use p
      simp [← append_eq_mul, ← Concatenation.append_assoc]
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

end FFL.FirstOrder.Concatenation

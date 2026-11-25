module

public import Concatenation.F.Basic
public import Concatenation.Semantics.Relativization

/-!
# Tame strings

$\mathsf{F}$ interprets $\mathsf{TC}$ with the empty string on the hereditarily tame strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section

variable {M : Type*} [ConcatenationEmptyStructure M] {x y z w : M}

/-- `x` is a suffix of `y`, in the language with the empty string. -/
def isSuffixEmpty : Semisentence ℒ⌢ₑ 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

@[simp]
lemma eval_isSuffixEmpty : M ⊧/![x, y] isSuffixEmpty ↔ y ◧ x := by
  simp [isSuffixEmpty, IsSuffix]

/--
`x` is tame: every suffix of a string that ends with `x` is comparable with `x`.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4, Lemma 8]
-/
def IsTame (x : M) : Prop := ∀ u y, u ++ x ◧ y → x ◧ y ∨ y ◧ x

/--
`x` is tame: every suffix of a string that ends with `x` is comparable with `x`.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4, Lemma 8]
-/
def isTame : Semisentence ℒ⌢ₑ 1 :=
  “x. ∀ u y, !isSuffixEmpty y (u ⌢ x) → !isSuffixEmpty y x ∨ !isSuffixEmpty x y”

@[simp]
lemma eval_isTame : M ⊧/![x] isTame ↔ IsTame x := by
  simp [isTame, IsTame]

/-- Every suffix of `x` is tame. -/
def IsHereditarilyTame (x : M) : Prop := ∀ y, x ◧ y → IsTame y

/-- Every suffix of `x` is tame. -/
def isHereditarilyTame : Semisentence ℒ⌢ₑ 1 := “x. ∀ y, !isSuffixEmpty y x → !isTame y”

@[simp]
lemma eval_isHereditarilyTame : M ⊧/![x] isHereditarilyTame ↔ IsHereditarilyTame x := by
  simp [isHereditarilyTame, IsHereditarilyTame]

lemma IsHereditarilyTame.isTame (hx : IsHereditarilyTame x) : IsTame x := hx x (IsSuffix.refl x)

end

namespace F

variable {M : Type*} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗙] {x y z w : M}

lemma isSuffix_iff : y ◧ x ↔ ∃ u, y = u ++ x := by
  constructor
  · rintro (rfl | h)
    · use ∅
      simp
    · exact h
  · exact Or.inr

lemma isSuffix_trans (hxy : z ◧ y) (hyx : y ◧ x) : z ◧ x := by
  obtain ⟨u, rfl⟩ := isSuffix_iff.mp hxy
  obtain ⟨v, rfl⟩ := isSuffix_iff.mp hyx
  simp [← F.append_assoc]

@[simp]
lemma isSuffix_empty (x : M) : x ◧ ∅ := isSuffix_iff.mpr ⟨x, by simp⟩

lemma isSuffix_append_right_iff : y ++ z ◧ x ++ z ↔ y ◧ x := by
  simp only [isSuffix_iff, ← F.append_assoc]
  exact exists_congr fun u ↦ ⟨F.append_right_cancel, congrArg (· ++ z)⟩

lemma isTame_empty : IsTame (∅ : M) := fun _ y _ ↦ Or.inr <| isSuffix_empty y

lemma isTame_of_isAtom (hx : IsAtom x) : IsTame x := by
  intro u y h
  rcases eq_empty_or_exists_eq_append y with rfl | ⟨v, c, hc, rfl⟩
  · simp
  · obtain ⟨w, hw⟩ := isSuffix_iff.mp h
    obtain rfl : x = c := (eq_of_append_eq_append hx hc <| hw.trans (F.append_assoc ..).symm).2
    simp

/--
The concatenation of tame strings is tame.
- [Gan09, §4, Lemma 8]
-/
lemma isTame_append (hx : IsTame x) (hy : IsTame y) : IsTame (x ++ y) := by
  intro u z hz
  rw [← F.append_assoc] at hz
  rcases hy (u ++ x) z hz with h | h
  · exact Or.inl <| isSuffix_trans (isSuffix_append x y) h
  · obtain ⟨v, rfl⟩ := isSuffix_iff.mp h
    simpa only [isSuffix_append_right_iff] using hx u v (isSuffix_append_right_iff.mp hz)

lemma isHereditarilyTame_of_isSuffix (hx : IsHereditarilyTame x) (h : x ◧ y) :
    IsHereditarilyTame y := fun z hz ↦ hx z <| isSuffix_trans h hz

lemma isHereditarilyTame_empty : IsHereditarilyTame (∅ : M) := by
  intro y hy
  obtain ⟨u, hu⟩ := isSuffix_iff.mp hy
  simpa [eq_empty_of_append_eq_empty hu.symm] using isTame_empty

lemma isHereditarilyTame_of_isAtom (hx : IsAtom x) : IsHereditarilyTame x := by
  intro y hy
  obtain ⟨u, rfl⟩ := isSuffix_iff.mp hy
  rcases eq_empty_of_append_isAtom hx with rfl | rfl
  · simpa using isTame_of_isAtom hx
  · exact isTame_empty

lemma isHereditarilyTame_append (hx : IsHereditarilyTame x) (hy : IsHereditarilyTame y) :
    IsHereditarilyTame (x ++ y) := by
  intro z hz
  rcases hy.isTame x z hz with h | h
  · exact hy z h
  · obtain ⟨v, rfl⟩ := isSuffix_iff.mp h
    exact isTame_append (hx v <| isSuffix_append_right_iff.mp hz) hy.isTame

lemma isConcatenationClosed_isHereditarilyTame :
    IsConcatenationClosed fun x : M ↦ M ⊧/![x] isHereditarilyTame where
  zero := by simpa using isHereditarilyTame_of_isAtom isAtom_zero
  one := by simpa using isHereditarilyTame_of_isAtom isAtom_one
  empty := by simpa using isHereditarilyTame_empty
  append hx hy := by simpa using isHereditarilyTame_append (by simpa using hx) (by simpa using hy)

/--
Editor axiom for tame strings.
- [Gan09, §4, Lemma 8]
-/
lemma exists_of_append_eq_append (hy : IsTame y) (h : x ++ y = z ++ w) :
    ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  rcases hy x w <| isSuffix_iff.mpr ⟨z, h⟩ with h' | h'
  · obtain ⟨u, rfl⟩ := isSuffix_iff.mp h'
    use u
    exact Or.inl ⟨F.append_right_cancel <| by rw [F.append_assoc, h], rfl⟩
  · obtain ⟨u, rfl⟩ := isSuffix_iff.mp h'
    use u
    exact Or.inr ⟨F.append_right_cancel <| by rw [F.append_assoc, h], rfl⟩

end F

/--
The translation of $\mathsf{TC}$ with the empty string into $\mathsf{F}$, relativized to the
hereditarily tame strings.
- [Gan09, §4, Lemma 8]
-/
abbrev tameTranslation : DirectTranslation 𝗙 ℒ⌢ₑ :=
  relativization 𝗙 isHereditarilyTame fun _ _ _ ↦ F.isConcatenationClosed_isHereditarilyTame

open DirectTranslation

/--
The hereditarily tame strings of a model of $\mathsf{F}$ form a model of $\mathsf{TC}$ with the
empty string.
- [Gan09, §4, Lemma 8]
-/
instance {M : Type} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗙] :
    (tameTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  rw [relativization.struc_eq]
  let := relativization.concatenationStructure 𝗙 isHereditarilyTame
    (fun _ _ _ ↦ F.isConcatenationClosed_isHereditarilyTame) (M := M)
  have tame (x : tameTranslation.Model M) : IsHereditarilyTame (x : M) := by
    simpa only [relativization.dom_iff, eval_isHereditarilyTame] using x.dom
  have dom {x : M} (h : IsHereditarilyTame x) : tameTranslation.Dom x := by simpa using h
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyConcat =>
    suffices ∀ x : tameTranslation.Model M, ∅ ++ x = x by simpa [models_iff]
    exact fun x ↦ Model.ext <| F.empty_append (x : M)
  case concatEmpty =>
    suffices ∀ x : tameTranslation.Model M, x ++ ∅ = x by simpa [models_iff]
    exact fun x ↦ Model.ext <| F.append_empty (x : M)
  case concatAssoc =>
    suffices ∀ x y z : tameTranslation.Model M, x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
    exact fun x y z ↦ Model.ext <| F.append_assoc (x : M) y z
  case editor =>
    suffices ∀ x y z w : tameTranslation.Model M, x ++ y = z ++ w →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    intro x y z w h
    obtain ⟨u, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ :=
      F.exists_of_append_eq_append (tame y).isTame (congrArg Model.val h)
    · use ⟨u, dom <| F.isHereditarilyTame_of_isSuffix (tame z) <| by simp [← h₁]⟩
      exact Or.inl ⟨Model.ext h₁, Model.ext h₂⟩
    · use ⟨u, dom <| F.isHereditarilyTame_of_isSuffix (tame x) <| by simp [h₁]⟩
      exact Or.inr ⟨Model.ext h₁, Model.ext h₂⟩
  case zeroNeEmpty =>
    suffices (0 : tameTranslation.Model M) ≠ ∅ by simpa [models_iff]
    exact fun h ↦ F.isAtom_ne_empty (M := M) isAtom_zero (congrArg Model.val h)
  case oneNeEmpty =>
    suffices (1 : tameTranslation.Model M) ≠ ∅ by simpa [models_iff]
    exact fun h ↦ F.isAtom_ne_empty (M := M) isAtom_one (congrArg Model.val h)
  case zeroAtom =>
    suffices ∀ x y : tameTranslation.Model M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ (F.eq_empty_of_append_isAtom <| Or.inl <| congrArg Model.val h).imp
      Model.ext Model.ext
  case oneAtom =>
    suffices ∀ x y : tameTranslation.Model M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    exact fun x y h ↦ (F.eq_empty_of_append_isAtom <| Or.inr <| congrArg Model.val h).imp
      Model.ext Model.ext
  case zeroNeOne =>
    suffices (0 : tameTranslation.Model M) ≠ 1 by simpa [models_iff]
    exact fun h ↦ F.zero_ne_one (M := M) (congrArg Model.val h)

/--
$\mathsf{F}$ interprets $\mathsf{TC}$ with the empty string on the hereditarily tame strings.
- [Gan09, §4, Lemma 8]
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⊳ 𝗧𝗖ₑ where
  trln := tameTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder.Concatenation

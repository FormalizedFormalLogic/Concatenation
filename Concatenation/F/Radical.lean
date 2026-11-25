module

public import Concatenation.F.Basic
public import Concatenation.Semantics.Relativization

/-!
# Radical strings

$\mathsf{TC}$ with the empty string interprets $\mathsf{F}$ on the hereditarily radical strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section

variable {M : Type*} [ConcatenationEmptyStructure M] {x : M}

/--
`x` can be cancelled on both sides.
- [Hor11, §2, Theorem 2.12]
-/
structure IsRadical (x : M) : Prop where
  right {y z : M} : y ++ x = z ++ x → y = z
  left {y z : M} : x ++ y = x ++ z → y = z

/--
`x` can be cancelled on both sides.
- [Hor11, §2, Theorem 2.12]
-/
def isRadical : Semisentence ℒ⌢ₑ 1 :=
  “x. (∀ y z, y ⌢ x = z ⌢ x → y = z) ∧ (∀ y z, x ⌢ y = x ⌢ z → y = z)”

@[simp]
lemma eval_isRadical : M ⊧/![x] isRadical ↔ IsRadical x := by
  suffices ((∀ y z, y ++ x = z ++ x → y = z) ∧ ∀ y z, x ++ y = x ++ z → y = z) ↔ IsRadical x by
    simpa [isRadical]
  exact ⟨fun h ↦ ⟨h.1 _ _, h.2 _ _⟩, fun h ↦ ⟨fun _ _ ↦ h.right, fun _ _ ↦ h.left⟩⟩

/--
`x` is empty or ends with a letter.
- [Hor11, §2, Theorem 2.12]
-/
def IsEmptyOrAppendAtom (x : M) : Prop := x = ∅ ∨ ∃ u, x = u ++ 0 ∨ x = u ++ 1

/--
`x` is empty or ends with a letter.
- [Hor11, §2, Theorem 2.12]
-/
def isEmptyOrAppendAtom : Semisentence ℒ⌢ₑ 1 :=
  “x. x = ⋆ ∨ ∃ u, x = u ⌢ !!(op(0).const) ∨ x = u ⌢ !!(op(1).const)”

@[simp]
lemma eval_isEmptyOrAppendAtom : M ⊧/![x] isEmptyOrAppendAtom ↔ IsEmptyOrAppendAtom x := by
  simp [isEmptyOrAppendAtom, IsEmptyOrAppendAtom]

/-- Every prefix of `x` is radical, and empty or ends with a letter. -/
def IsHereditarilyRadical (x : M) : Prop :=
  ∀ y z, x = y ++ z → IsRadical y ∧ IsEmptyOrAppendAtom y

/-- Every prefix of `x` is radical, and empty or ends with a letter. -/
def isHereditarilyRadical : Semisentence ℒ⌢ₑ 1 :=
  “x. ∀ y z, x = y ⌢ z → !isRadical y ∧ !isEmptyOrAppendAtom y”

@[simp]
lemma eval_isHereditarilyRadical : M ⊧/![x] isHereditarilyRadical ↔ IsHereditarilyRadical x := by
  simp [isHereditarilyRadical, IsHereditarilyRadical]

end

namespace TCEmpty

variable {M : Type*} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {x y z : M}

lemma isRadical_empty : IsRadical (∅ : M) where
  right := by simp
  left := by simp

lemma eq_empty_of_append_eq_right (hx : IsAtom x) (h : y ++ x = x) : y = ∅ :=
  (eq_empty_of_append_isAtom <| h.symm ▸ hx).resolve_right <| isAtom_ne_empty hx

lemma eq_empty_of_append_eq_left (hx : IsAtom x) (h : x ++ y = x) : y = ∅ :=
  (eq_empty_of_append_isAtom <| h.symm ▸ hx).resolve_left <| isAtom_ne_empty hx

lemma isRadical_of_isAtom (hx : IsAtom x) : IsRadical x where
  right h := by
    obtain ⟨u, ⟨rfl, h'⟩ | ⟨rfl, h'⟩⟩ := editor h
    · simp [eq_empty_of_append_eq_right hx h'.symm]
    · simp [eq_empty_of_append_eq_right hx h']
  left h := by
    obtain ⟨u, ⟨h', rfl⟩ | ⟨h', rfl⟩⟩ := editor h
    · simp [eq_empty_of_append_eq_left hx h']
    · simp [eq_empty_of_append_eq_left hx h'.symm]

lemma isRadical_append (hx : IsRadical x) (hy : IsRadical y) : IsRadical (x ++ y) where
  right h := hx.right <| hy.right <| by simpa [TCEmpty.append_assoc] using h
  left h := hy.left <| hx.left <| by simpa [TCEmpty.append_assoc] using h

lemma isEmptyOrAppendAtom_of_isAtom (hx : IsAtom x) : IsEmptyOrAppendAtom x := by
  right
  use ∅
  simpa [IsAtom] using hx

lemma isEmptyOrAppendAtom_append (hx : IsEmptyOrAppendAtom x) (hy : IsEmptyOrAppendAtom y) :
    IsEmptyOrAppendAtom (x ++ y) := by
  rcases hy with rfl | ⟨u, rfl | rfl⟩
  · simpa using hx
  · exact Or.inr ⟨x ++ u, by simp [TCEmpty.append_assoc]⟩
  · exact Or.inr ⟨x ++ u, by simp [TCEmpty.append_assoc]⟩

lemma isHereditarilyRadical_left (h : IsHereditarilyRadical (x ++ y)) : IsHereditarilyRadical x :=
  fun z w hw ↦ h z (w ++ y) <| by rw [hw, TCEmpty.append_assoc]

lemma isRadical (hx : IsHereditarilyRadical x) : IsRadical x := (hx x ∅ <| by simp).1

lemma isEmptyOrAppendAtom (hx : IsHereditarilyRadical x) : IsEmptyOrAppendAtom x :=
  (hx x ∅ <| by simp).2

lemma isHereditarilyRadical_empty : IsHereditarilyRadical (∅ : M) := by
  intro y z h
  obtain ⟨rfl, -⟩ := eq_empty_of_append_eq_empty h.symm
  exact ⟨isRadical_empty, Or.inl rfl⟩

lemma isHereditarilyRadical_of_isAtom (hx : IsAtom x) : IsHereditarilyRadical x := by
  rintro y z rfl
  rcases eq_empty_of_append_isAtom hx with rfl | rfl
  · exact ⟨isRadical_empty, Or.inl rfl⟩
  · rw [append_empty] at hx
    exact ⟨isRadical_of_isAtom hx, isEmptyOrAppendAtom_of_isAtom hx⟩

lemma isHereditarilyRadical_append (hx : IsHereditarilyRadical x) (hy : IsHereditarilyRadical y) :
    IsHereditarilyRadical (x ++ y) := by
  intro z w h
  obtain ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, -⟩⟩ := editor h
  · have hu := isHereditarilyRadical_left hy
    exact ⟨isRadical_append (isRadical hx) (isRadical hu),
      isEmptyOrAppendAtom_append (isEmptyOrAppendAtom hx) (isEmptyOrAppendAtom hu)⟩
  · have hz := isHereditarilyRadical_left hx
    exact ⟨isRadical hz, isEmptyOrAppendAtom hz⟩

lemma isConcatenationClosed_isHereditarilyRadical :
    IsConcatenationClosed fun x : M ↦ M ⊧/![x] isHereditarilyRadical where
  zero := by simpa using isHereditarilyRadical_of_isAtom isAtom_zero
  one := by simpa using isHereditarilyRadical_of_isAtom isAtom_one
  empty := by simpa using isHereditarilyRadical_empty
  append hx hy := by
    simpa using isHereditarilyRadical_append (by simpa using hx) (by simpa using hy)

lemma append_zero_ne_append_one (x y : M) : x ++ 0 ≠ y ++ 1 := by
  intro h
  obtain ⟨u, ⟨-, h⟩ | ⟨-, h⟩⟩ := editor h
  · rcases eq_empty_of_append_isAtom (h ▸ isAtom_zero) with rfl | h' <;> simp_all
  · rcases eq_empty_of_append_isAtom (h ▸ isAtom_one) with rfl | h' <;> simp_all

end TCEmpty

/--
The translation of $\mathsf{F}$ into $\mathsf{TC}$ with the empty string, relativized to the
hereditarily radical strings.
- [Hor11, §2, Theorem 2.12]
-/
abbrev radicalTranslation : DirectTranslation 𝗧𝗖ₑ ℒ⌢ₑ :=
  relativization 𝗧𝗖ₑ isHereditarilyRadical
    fun _ _ _ ↦ TCEmpty.isConcatenationClosed_isHereditarilyRadical

open DirectTranslation

/--
The hereditarily radical strings of a model of $\mathsf{TC}$ with the empty string form a model of
$\mathsf{F}$.
- [Hor11, §2, Theorem 2.12]
-/
instance {M : Type} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    (radicalTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗙 := by
  rw [relativization.struc_eq]
  let := relativization.concatenationStructure 𝗧𝗖ₑ isHereditarilyRadical
    (fun _ _ _ ↦ TCEmpty.isConcatenationClosed_isHereditarilyRadical) (M := M)
  have radical (x : radicalTranslation.Model M) : IsHereditarilyRadical (x : M) := by
    simpa only [relativization.dom_iff, eval_isHereditarilyRadical] using x.dom
  have dom {x : M} (h : IsHereditarilyRadical x) : radicalTranslation.Dom x := by simpa using h
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyConcat =>
    suffices ∀ x : radicalTranslation.Model M, ∅ ++ x = x by simpa [models_iff]
    exact fun x ↦ Model.ext <| TCEmpty.empty_append (x : M)
  case concatEmpty =>
    suffices ∀ x : radicalTranslation.Model M, x ++ ∅ = x by simpa [models_iff]
    exact fun x ↦ Model.ext <| TCEmpty.append_empty (x : M)
  case concatAssoc =>
    suffices ∀ x y z : radicalTranslation.Model M, x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    exact fun x y z ↦ Model.ext <| TCEmpty.append_assoc (x : M) y z
  case cancelRight =>
    suffices ∀ x y z : radicalTranslation.Model M, x ++ z = y ++ z → x = y by simpa [models_iff]
    exact fun x y z h ↦ Model.ext <| (TCEmpty.isRadical (radical z)).right <| congrArg Model.val h
  case cancelLeft =>
    suffices ∀ x y z : radicalTranslation.Model M, z ++ x = z ++ y → x = y by simpa [models_iff]
    exact fun x y z h ↦ Model.ext <| (TCEmpty.isRadical (radical z)).left <| congrArg Model.val h
  case concatZeroNeConcatOne =>
    suffices ∀ x y : radicalTranslation.Model M, x ++ 0 ≠ y ++ 1 by simpa [models_iff]
    exact fun x y h ↦ TCEmpty.append_zero_ne_append_one (x : M) y (congrArg Model.val h)
  case emptyOrConcatLetter =>
    suffices ∀ x : radicalTranslation.Model M, x ≠ ∅ → ∃ u, x = u ++ 0 ∨ x = u ++ 1 by
      simpa [models_iff]
    intro x hx
    rcases TCEmpty.isEmptyOrAppendAtom (radical x) with h | ⟨u, h⟩
    · exact (hx <| Model.ext h).elim
    · use ⟨u, dom <| by
        rcases h with h | h <;> exact TCEmpty.isHereditarilyRadical_left (h ▸ radical x)⟩
      exact h.imp Model.ext Model.ext

/--
$\mathsf{TC}$ with the empty string interprets $\mathsf{F}$ on the hereditarily radical strings.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗧𝗖ₑ ⊳ 𝗙 where
  trln := radicalTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder.Concatenation

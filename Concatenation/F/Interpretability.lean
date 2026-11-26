module

public import Concatenation.F.Basic
public import Concatenation.TC.Empty

/-!
# Mutual interpretability of $\mathsf{F}$ and $\mathsf{TC}$

$\mathsf{F}$ interprets $\mathsf{TC}$ with the empty string on the hereditarily tame strings, and is
interpreted in it on the hereditarily radical strings; hence $\mathsf{F}$ is essentially
undecidable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

section relativization

/-- `D` contains the letters and the empty string and is closed under concatenation. -/
structure IsConcatenationClosed {M : Type*} [ConcatenationEmptyStructure M] (D : M → Prop) :
    Prop where
  zero : D 0
  one : D 1
  empty : D ∅
  append {x y : M} : D x → D y → D (x ++ y)

variable (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (δ : Semisentence ℒ⌢ₑ 1)
  (H : ∀ (M : Type) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T],
    IsConcatenationClosed fun x : M ↦ M ⊧/![x] δ)

/-- The translation that restricts the quantifiers to `δ` and leaves the symbols unchanged. -/
def relativization : DirectTranslation T ℒ⌢ₑ where
  domain := ⟨δ⟩
  rel R := ⟨Semiformula.rel R (#·)⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using (H M).zero
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : M ⊧/![e i] δ := by simpa [Semiformula.Operator.val] using he i
    suffices ∃! y : M, M ⊧/![y] δ ∧ y = Tarski.Structure.func f e by
      simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    use Tarski.Structure.func f e
    simp only [and_true, and_imp, imp_self, implies_true]
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    exacts [(H M).zero, (H M).one, (H M).append (he 0) (he 1), (H M).empty]
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val]

namespace relativization

variable {M : Type} [ConcatenationEmptyStructure M] {x : M}

@[simp]
lemma dom_iff : (relativization T δ H).Dom x ↔ M ⊧/![x] δ := by
  simp [DirectTranslation.dom_iff, relativization, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* T]

/-- The letters, the empty string and the concatenation of `M` restricted to `δ`. -/
abbrev concatenationStructure : ConcatenationEmptyStructure ((relativization T δ H).Model M) where
  zero := ⟨0, (dom_iff T δ H).mpr (H M).zero⟩
  one := ⟨1, (dom_iff T δ H).mpr (H M).one⟩
  emptyCollection := ⟨∅, (dom_iff T δ H).mpr (H M).empty⟩
  append x y := ⟨x ++ y, (dom_iff T δ H).mpr <|
    (H M).append ((dom_iff T δ H).mp x.dom) ((dom_iff T δ H).mp y.dom)⟩

/--
The structure of the model of `relativization` is the standard one of the letters, the empty string
and the concatenation restricted to `δ`.
-/
lemma struc_eq : Model.struc (relativization T δ H) M =
    @standardModelEmpty _ (concatenationStructure T δ H) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;>
        simp [relativization, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationStructure

variable {y : M} {hx : (relativization T δ H).Dom x} {hy : (relativization T δ H).Dom y}

@[simp]
lemma zero_eq_mk : (0 : (relativization T δ H).Model M) = ⟨0, (dom_iff T δ H).mpr (H M).zero⟩ :=
  rfl

@[simp]
lemma one_eq_mk : (1 : (relativization T δ H).Model M) = ⟨1, (dom_iff T δ H).mpr (H M).one⟩ := rfl

@[simp]
lemma empty_eq_mk : (∅ : (relativization T δ H).Model M) = ⟨∅, (dom_iff T δ H).mpr (H M).empty⟩ :=
  rfl

@[simp]
lemma mk_append_mk : (⟨x, hx⟩ ++ ⟨y, hy⟩ : (relativization T δ H).Model M) =
    ⟨x ++ y, (dom_iff T δ H).mpr <| (H M).append ((dom_iff T δ H).mp hx) ((dom_iff T δ H).mp hy)⟩ :=
  rfl

end

end relativization

end relativization

section

variable {M : Type*} [ConcatenationEmptyStructure M] {x y z w : M}

/-- `x` is a suffix of `y`, in the language with the empty string. -/
def isSuffixEmpty : Semisentence ℒ⌢ₑ 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

instance isSuffixEmpty_defined : ℒ⌢ₑ-relation[M] IsSuffix via isSuffixEmpty :=
  ⟨fun v ↦ by simp [isSuffixEmpty, IsSuffix]⟩

instance isSuffixEmpty_definable : ℒ⌢ₑ-relation[M] IsSuffix := isSuffixEmpty_defined.to_definable

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

instance isTame_defined : ℒ⌢ₑ-predicate[M] IsTame via isTame := ⟨fun v ↦ by simp [isTame, IsTame]⟩

instance isTame_definable : ℒ⌢ₑ-predicate[M] IsTame := isTame_defined.to_definable

/-- Every suffix of `x` is tame. -/
def IsHereditarilyTame (x : M) : Prop := ∀ y, x ◧ y → IsTame y

/-- Every suffix of `x` is tame. -/
def isHereditarilyTame : Semisentence ℒ⌢ₑ 1 := “x. ∀ y, !isSuffixEmpty y x → !isTame y”

instance isHereditarilyTame_defined : ℒ⌢ₑ-predicate[M] IsHereditarilyTame via isHereditarilyTame :=
  ⟨fun v ↦ by simp [isHereditarilyTame, IsHereditarilyTame]⟩

instance isHereditarilyTame_definable : ℒ⌢ₑ-predicate[M] IsHereditarilyTame :=
  isHereditarilyTame_defined.to_definable

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
  rcases hy x w <| isSuffix_iff.mpr ⟨z, h⟩ with h' | h' <;>
    obtain ⟨u, rfl⟩ := isSuffix_iff.mp h' <;> use u
  · exact Or.inl ⟨F.append_right_cancel <| by rw [F.append_assoc, h], rfl⟩
  · exact Or.inr ⟨F.append_right_cancel <| by rw [F.append_assoc, h], rfl⟩

end F

/--
The translation of $\mathsf{TC}$ with the empty string into $\mathsf{F}$, relativized to the
hereditarily tame strings.
- [Gan09, §4, Lemma 8]
-/
abbrev tameTranslation : DirectTranslation 𝗙 ℒ⌢ₑ :=
  relativization 𝗙 isHereditarilyTame fun _ _ _ ↦ F.isConcatenationClosed_isHereditarilyTame

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
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case editor =>
    simpa [models_iff, Model.forall_iff, Model.exists_iff] using
      fun (x : M) (hx : IsHereditarilyTame x) (y : M) (hy : IsHereditarilyTame y) (z : M)
        (hz : IsHereditarilyTame z) (w : M) (_ : IsHereditarilyTame w) (h : x ++ y = z ++ w) ↦
      match F.exists_of_append_eq_append hy.isTame h with
      | ⟨u, .inl h'⟩ => ⟨u, F.isHereditarilyTame_of_isSuffix hz <| by simp [← h'.1], .inl h'⟩
      | ⟨u, .inr h'⟩ => ⟨u, F.isHereditarilyTame_of_isSuffix hx <| by simp [h'.1], .inr h'⟩
  case zeroAtom =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (_ : IsHereditarilyTame x) (y : M)
      (_ : IsHereditarilyTame y) (h : x ++ y = 0) ↦ F.eq_empty_of_append_isAtom (by simp [h])
  case oneAtom =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (_ : IsHereditarilyTame x) (y : M)
      (_ : IsHereditarilyTame y) (h : x ++ y = 1) ↦ F.eq_empty_of_append_isAtom (by simp [h])
  all_goals simp [models_iff, Model.forall_iff, F.append_assoc, F.isAtom_ne_empty]

/--
$\mathsf{F}$ interprets $\mathsf{TC}$ with the empty string on the hereditarily tame strings.
- [Gan09, §4, Lemma 8]
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⊳ 𝗧𝗖ₑ where
  trln := tameTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

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

instance isRadical_defined : ℒ⌢ₑ-predicate[M] IsRadical via isRadical := .mk fun v ↦ by
  suffices ((∀ y z, y ++ v 0 = z ++ v 0 → y = z) ∧ ∀ y z, v 0 ++ y = v 0 ++ z → y = z) ↔
      IsRadical (v 0) by simpa [isRadical]
  exact ⟨fun h ↦ ⟨h.1 _ _, h.2 _ _⟩, fun h ↦ ⟨fun _ _ ↦ h.right, fun _ _ ↦ h.left⟩⟩

instance isRadical_definable : ℒ⌢ₑ-predicate[M] IsRadical := isRadical_defined.to_definable

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

instance isEmptyOrAppendAtom_defined :
    ℒ⌢ₑ-predicate[M] IsEmptyOrAppendAtom via isEmptyOrAppendAtom :=
  ⟨fun v ↦ by simp [isEmptyOrAppendAtom, IsEmptyOrAppendAtom]⟩

instance isEmptyOrAppendAtom_definable : ℒ⌢ₑ-predicate[M] IsEmptyOrAppendAtom :=
  isEmptyOrAppendAtom_defined.to_definable

/-- Every prefix of `x` is radical, and empty or ends with a letter. -/
def IsHereditarilyRadical (x : M) : Prop :=
  ∀ y z, x = y ++ z → IsRadical y ∧ IsEmptyOrAppendAtom y

/-- Every prefix of `x` is radical, and empty or ends with a letter. -/
def isHereditarilyRadical : Semisentence ℒ⌢ₑ 1 :=
  “x. ∀ y z, x = y ⌢ z → !isRadical y ∧ !isEmptyOrAppendAtom y”

instance isHereditarilyRadical_defined :
    ℒ⌢ₑ-predicate[M] IsHereditarilyRadical via isHereditarilyRadical :=
  ⟨fun v ↦ by simp [isHereditarilyRadical, IsHereditarilyRadical]⟩

instance isHereditarilyRadical_definable : ℒ⌢ₑ-predicate[M] IsHereditarilyRadical :=
  isHereditarilyRadical_defined.to_definable

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
  all_goals exact Or.inr ⟨x ++ u, by simp [TCEmpty.append_assoc]⟩

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
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case cancelRight =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (_ : IsHereditarilyRadical x) (y : M)
      (_ : IsHereditarilyRadical y) (z : M) (hz : IsHereditarilyRadical z) ↦
      (TCEmpty.isRadical hz).right (y := x) (z := y)
  case cancelLeft =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (_ : IsHereditarilyRadical x) (y : M)
      (_ : IsHereditarilyRadical y) (z : M) (hz : IsHereditarilyRadical z) ↦
      (TCEmpty.isRadical hz).left (y := x) (z := y)
  case emptyOrConcatLetter =>
    simpa [models_iff, Model.forall_iff, Model.exists_iff] using
      fun (x : M) (hx : IsHereditarilyRadical x) (hx' : x ≠ ∅) ↦
      match TCEmpty.isEmptyOrAppendAtom hx with
      | .inl h => (hx' h).elim
      | .inr ⟨u, .inl h⟩ => ⟨u, TCEmpty.isHereditarilyRadical_left (h ▸ hx), .inl h⟩
      | .inr ⟨u, .inr h⟩ => ⟨u, TCEmpty.isHereditarilyRadical_left (h ▸ hx), .inr h⟩
  all_goals simp [models_iff, Model.forall_iff, TCEmpty.append_assoc,
    TCEmpty.append_zero_ne_append_one]

/--
$\mathsf{TC}$ with the empty string interprets $\mathsf{F}$ on the hereditarily radical strings.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗧𝗖ₑ ⊳ 𝗙 where
  trln := radicalTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{F}$ interprets $\mathsf{TC}$.
- [Gan09, §4, Lemma 8]
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⊳ 𝗧𝗖 :=
  DirectInterpretation.comp (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖) (inferInstance : 𝗙 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{TC}$ interprets $\mathsf{F}$.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗧𝗖 ⊳ 𝗙 :=
  DirectInterpretation.comp (inferInstance : 𝗧𝗖ₑ ⊳ 𝗙) (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{F}$ and $\mathsf{TC}$ with the empty string are mutually interpretable.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⋈ 𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{F}$ and $\mathsf{TC}$ are mutually interpretable.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4, Theorem 6]
-/
instance : 𝗙 ⋈ 𝗧𝗖 := ⟨inferInstance, inferInstance⟩

instance : Entailment.Consistent 𝗙 := DirectInterpretation.consistent (inferInstance : 𝗧𝗖 ⊳ 𝗙)

/--
$\mathsf{F}$ is essentially undecidable.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4]
-/
instance : 𝗙.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗙 ⊳ 𝗧𝗖)

end FFL.FirstOrder.Concatenation

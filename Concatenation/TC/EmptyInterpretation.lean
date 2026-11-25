module

public import Concatenation.Semantics.Empty
public import AlphaCentauri.Interpretability.Basic

/-!
# $\mathsf{TC}$ with and without the empty string

$\mathsf{TC}$ with the empty string and $\mathsf{TC}$ without it are mutually interpretable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

section nonempty

variable {M : Type} [ConcatenationEmptyStructure M] {x : M}

/-- `x` is not the empty string. -/
def isNonempty : Semisentence ℒ⌢ₑ 1 := “x. x ≠ ⋆”

@[simp]
lemma eval_isNonempty : M ⊧/![x] isNonempty ↔ x ≠ ∅ := by
  simp [isNonempty]

/--
The translation of $\mathsf{TC}$ into $\mathsf{TC}$ with the empty string, relativized to the
nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
def nonemptyTranslation : DirectTranslation 𝗧𝗖ₑ ℒ⌢ where
  domain := ⟨isNonempty⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. z = !!(op(0).const)”⟩
    | Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const)”⟩
    | Language.Concatenation.Func.concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val]
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : e i ≠ ∅ := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 0 by simpa [Semiformula.Operator.val]
      use 0
      simp
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 1 by simpa [Semiformula.Operator.val]
      use 1
      simp
    · suffices ∃! y : M, y ≠ ∅ ∧ y = e 0 ++ e 1 by simpa [Semiformula.Operator.val]
      use e 0 ++ e 1
      simpa using fun h ↦ he 0 (TCEmpty.eq_empty_of_append_eq_empty h).1
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace nonemptyTranslation

@[simp]
lemma dom_iff : nonemptyTranslation.Dom x ↔ x ≠ ∅ := by
  simp [DirectTranslation.dom_iff, nonemptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

/-- The letters and the concatenation of `M` restricted to the nonempty strings. -/
abbrev concatenationStructure : ConcatenationStructure (nonemptyTranslation.Model M) where
  zero := ⟨0, by simp⟩
  one := ⟨1, by simp⟩
  append x y := ⟨x ++ y, dom_iff.mpr fun h ↦
    dom_iff.mp x.dom (TCEmpty.eq_empty_of_append_eq_empty h).1⟩

/--
The structure of the model of `nonemptyTranslation` is the standard one of the letters and the
concatenation restricted to the nonempty strings.
-/
lemma struc_eq :
    Model.struc nonemptyTranslation M = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [nonemptyTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{TC}$ with the empty string form a model of
$\mathsf{TC}$.
- [Vis09, Appendix A]
-/
instance [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : (nonemptyTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure (M := M)
  have nonempty (x : nonemptyTranslation.Model M) : (x : M) ≠ ∅ :=
    nonemptyTranslation.dom_iff.mp x.dom
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case concatAssoc =>
    suffices ∀ x y z : nonemptyTranslation.Model M, x ++ (y ++ z) = x ++ y ++ z by
      simpa [models_iff]
    exact fun x y z ↦ Model.ext (TCEmpty.append_assoc (x : M) y z).symm
  case editor =>
    suffices ∀ x y z w : nonemptyTranslation.Model M, x ++ y = z ++ w →
        (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by
      simpa [models_iff]
    intro x y z w h
    obtain ⟨u, hu⟩ := TCEmpty.editor (congrArg Model.val h)
    rcases Classical.em (u = ∅) with rfl | hu'
    · left
      rcases hu with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨Model.ext <| by simpa using h₁, Model.ext <| by simpa using h₂⟩
      · exact ⟨Model.ext <| by simpa using h₁, Model.ext <| by simpa using h₂⟩
    · right
      use ⟨u, by simpa using hu'⟩
      exact hu.imp (And.imp Model.ext Model.ext) (And.imp Model.ext Model.ext)
  case zeroNeConcat =>
    suffices ∀ x y : nonemptyTranslation.Model M, 0 ≠ x ++ y by simpa [models_iff]
    exact fun x y h ↦ (TCEmpty.eq_empty_of_append_isAtom <| Or.inl (congrArg Model.val h).symm).elim
      (nonempty x) (nonempty y)
  case oneNeConcat =>
    suffices ∀ x y : nonemptyTranslation.Model M, 1 ≠ x ++ y by simpa [models_iff]
    exact fun x y h ↦ (TCEmpty.eq_empty_of_append_isAtom <| Or.inr (congrArg Model.val h).symm).elim
      (nonempty x) (nonempty y)
  case zeroNeOne =>
    suffices (0 : nonemptyTranslation.Model M) ≠ 1 by simpa [models_iff]
    exact fun h ↦ TCEmpty.zero_ne_one (M := M) (congrArg Model.val h)

/--
$\mathsf{TC}$ with the empty string interprets $\mathsf{TC}$ on the nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
instance : 𝗧𝗖ₑ ⊳ 𝗧𝗖 where
  trln := nonemptyTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end nonempty

section option

variable {M : Type*} [ConcatenationStructure M]

/-- The strings of `M` together with an empty string. -/
instance : ConcatenationEmptyStructure (Option M) where
  zero := some 0
  one := some 1
  append := Option.merge (· ++ ·)
  emptyCollection := none

lemma Option.zero_eq_some : (0 : Option M) = some 0 := rfl

lemma Option.one_eq_some : (1 : Option M) = some 1 := rfl

lemma Option.empty_eq_none : (∅ : Option M) = none := rfl

@[simp]
lemma Option.none_append (x : Option M) : none ++ x = x := by cases x <;> rfl

@[simp]
lemma Option.append_none (x : Option M) : x ++ none = x := by cases x <;> rfl

@[simp]
lemma Option.some_append_some (x y : M) : (some x ++ some y : Option M) = some (x ++ y) := rfl

/-- The editor axiom passes to the strings of `M` together with an empty string. -/
lemma Option.editor {x y z w : Option M}
    (H : ∀ x y z w : M, x ++ y = z ++ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w))
    (h : x ++ y = z ++ w) : ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  rcases x with _ | x <;> rcases z with _ | z
  · use none
    simpa using h
  · use some z
    exact Or.inl ⟨by simp, by simpa using h⟩
  · use some x
    exact Or.inr ⟨by simp, by simpa using h⟩
  rcases y with _ | y <;> rcases w with _ | w
  · use none
    simpa using h
  · use some w
    exact Or.inr ⟨by simpa using h, by simp⟩
  · use some y
    exact Or.inl ⟨by simpa using h, by simp⟩
  · rcases H _ _ _ _ (Option.some.inj h) with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · use none
      simp
    · use some u
      simp
    · use some u
      simp

/--
The strings of a model of $\mathsf{TC}$ together with an empty string form a model of $\mathsf{TC}$
with the empty string.
- [Vis09, Appendix A]
-/
instance [M↓[ℒ⌢] ⊧* 𝗧𝗖] : (Option M)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyConcat => simp [models_iff, Option.empty_eq_none]
  case concatEmpty => simp [models_iff, Option.empty_eq_none]
  case concatAssoc =>
    suffices ∀ x y z : Option M, x ++ y ++ z = x ++ (y ++ z) by simpa [models_iff]
    rintro (_ | x) (_ | y) (_ | z) <;> simp [Concatenation.append_assoc]
  case editor =>
    suffices ∀ x y z w : Option M, x ++ y = z ++ w →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ ↦ Option.editor fun _ _ _ _ ↦ Concatenation.editor
  case zeroNeEmpty => simp [models_iff, Option.empty_eq_none, Option.zero_eq_some]
  case oneNeEmpty => simp [models_iff, Option.empty_eq_none, Option.one_eq_some]
  case zeroAtom =>
    suffices ∀ x y : Option M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (zero_ne_append x y (Option.some.inj h).symm).elim
  case oneAtom =>
    suffices ∀ x y : Option M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (one_ne_append x y (Option.some.inj h).symm).elim
  case zeroNeOne => simp [models_iff, Option.zero_eq_some, Option.one_eq_some]

end option

section code

variable {M : Type} [ConcatenationStructure M] {x y z : M}

/--
`x` is the letter $1$ or begins with it.
- [HH14, Theorem 3]
-/
def IsEmptyCode (x : M) : Prop := 1 ◨ x

/--
`x` is the letter $1$ or begins with it.
- [HH14, Theorem 3]
-/
def isEmptyCode : Semisentence ℒ⌢ 1 := “x. !isPrefix !!(op(1).const) x”

@[simp]
lemma eval_isEmptyCode : M ⊧/![x] isEmptyCode ↔ IsEmptyCode x := by
  simp [isEmptyCode, IsEmptyCode]

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`.
- [HH14, Theorem 3]
-/
def IsCodeAppend (z x y : M) : Prop := (y = 1 ∧ z = x) ∨ ∃ w, y = 1 ++ w ∧ z = x ++ w

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`.
- [HH14, Theorem 3]
-/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(1).const) ∧ z = x) ∨ ∃ w, y = !!(op(1).const) ⌢ w ∧ z = x ⌢ w”

@[simp]
lemma eval_isCodeAppend : M ⊧/![z, x, y] isCodeAppend ↔ IsCodeAppend z x y := by
  simp [isCodeAppend, IsCodeAppend]

/-- The code of a string or of the empty string: the string itself after the letter $1$. -/
def emptyCode : Option M → M
  | none => 1
  | some x => 1 ++ x

@[simp]
lemma isEmptyCode_emptyCode (x : Option M) : IsEmptyCode (emptyCode x) := by
  cases x
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

lemma isEmptyCode_iff : IsEmptyCode x ↔ ∃ y, emptyCode y = x := by
  constructor
  · rintro (rfl | ⟨y, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some y, rfl⟩
  · rintro ⟨y, rfl⟩
    simp

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma one_append_cancel (h : 1 ++ x = 1 ++ y) : x = y := by
  rcases editor h with ⟨-, h⟩ | ⟨u, ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact h
  · exact (one_ne_append 1 u h.symm).elim
  · exact (one_ne_append 1 u h).elim

lemma emptyCode_injective : Function.Injective (emptyCode (M := M)) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (one_ne_append 1 y h).elim
  · exact (one_ne_append 1 x h.symm).elim
  · exact congrArg some <| one_append_cancel h

lemma isCodeAppend_emptyCode_iff {x y : Option M} :
    IsCodeAppend z (emptyCode x) (emptyCode y) ↔ z = emptyCode (x ++ y) := by
  rcases y with _ | y
  · simp [IsCodeAppend, emptyCode]
  · have h (w : M) : 1 ++ y = 1 ++ w ↔ y = w := ⟨one_append_cancel, congrArg _⟩
    rcases x with _ | x <;>
      simp [IsCodeAppend, emptyCode, (one_ne_append 1 y).symm, h, Concatenation.append_assoc]

end TC

/--
The translation of $\mathsf{TC}$ with the empty string into $\mathsf{TC}$ that codes a string by
the string itself after the letter $1$, and the empty string by the letter $1$.
- [HH14, Theorem 3]
- [Vis09, Appendix A]
-/
def emptyTranslation : DirectTranslation 𝗧𝗖 ℒ⌢ₑ where
  domain := ⟨isEmptyCode⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero =>
      ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one =>
      ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isCodeAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(1).const)”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use emptyCode none
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsEmptyCode (e i) := by simpa [Semiformula.Operator.val] using he i
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode (some 0) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 0)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode (some 1) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 1)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ IsCodeAppend y (e 0) (e 1) by
        simpa [Semiformula.Operator.val]
      obtain ⟨x, hx⟩ := isEmptyCode_iff.mp (he 0)
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp (he 1)
      simp only [← hx, ← hy, isCodeAppend_emptyCode_iff]
      use emptyCode (x ++ y)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode none by
        simpa [Semiformula.Operator.val]
      use emptyCode none
      simp
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

@[simp]
lemma dom_iff : emptyTranslation.Dom x ↔ IsEmptyCode x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

/-- The bijection of the strings of `M` and the empty string with their codes. -/
noncomputable def equiv : Option M ≃ emptyTranslation.Model M :=
  Equiv.ofBijective (fun x ↦ ⟨emptyCode x, by simp⟩) <| by
    constructor
    · exact fun x y h ↦ emptyCode_injective <| congrArg Model.val h
    · intro x
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp <| dom_iff.mp x.dom
      exact ⟨y, Model.ext hy⟩

@[simp]
lemma val_equiv (x : Option M) : (equiv x : M) = emptyCode x := rfl

lemma struc_eq : Model.struc emptyTranslation M = Tarski.Structure.ofEquiv equiv :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · have h : M ⊧/![emptyCode (v 0 ++ v 1), emptyCode (v 0), emptyCode (v 1)] isCodeAppend :=
          eval_isCodeAppend.mpr <| isCodeAppend_emptyCode_iff.mpr rfl
        change Semiformula.Evalb _ isCodeAppend
        convert h using 2
        funext i
        match i with
        | 0 =>
          change emptyCode (equiv.symm (equiv (v 0)) ++ equiv.symm (equiv (v 1))) = _
          simp
        | 1 | 2 => rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| (Model.eq_iff v).trans equiv.symm.apply_eq_iff_eq.symm)

end emptyTranslation

/--
The codes of the strings of a model of $\mathsf{TC}$ and of the empty string form a model of
$\mathsf{TC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance [M↓[ℒ⌢] ⊧* 𝗧𝗖] : (emptyTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  have : Option M ≡ₑ[ℒ⌢ₑ] emptyTranslation.Model M := by
    rw [emptyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv emptyTranslation.equiv
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option M)).mp inferInstance

/--
$\mathsf{TC}$ interprets $\mathsf{TC}$ with the empty string.
- [HH14, Theorem 3]
- [Vis09, Appendix A]
-/
instance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ where
  trln := emptyTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{TC}$ and $\mathsf{TC}$ with the empty string are mutually interpretable.
- [Vis09, Appendix A]
-/
instance : 𝗧𝗖 ⋈ 𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

end code

end FFL.FirstOrder.Concatenation

module

public import Concatenation.TC.Interpretability
public import Concatenation.ToFoundation.Interpretability.DefinitionalEquivalence

/-!
# $\mathsf{TC}$ with and without the empty string

The two theories are mutually interpretable, hence both essentially undecidable, and even
definitionally equivalent, by a definable bijection between all strings and the nonempty strings.
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
In the models of `T`, the letters are not empty, and the nonempty strings are closed under
concatenation.
-/
class NonemptyClosed (T : Theory ℒ⌢ₑ) : Prop where
  zero_ne_empty (M : Type) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T] : (0 : M) ≠ ∅
  one_ne_empty (M : Type) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T] : (1 : M) ≠ ∅
  append_ne_empty (M : Type) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T] {x y : M}
    (hx : x ≠ ∅) : x ++ y ≠ ∅

instance : NonemptyClosed 𝗧𝗖ₑ where
  zero_ne_empty _ := TCEmpty.zero_ne_empty
  one_ne_empty _ := TCEmpty.one_ne_empty
  append_ne_empty _ _ _ _ _ hx h := hx (TCEmpty.eq_empty_of_append_eq_empty h).1

variable (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] [NonemptyClosed T]

/--
The translation of the language without the empty string into a theory with the empty string,
relativized to the nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
def nonemptyTranslation : DirectTranslation T ℒ⌢ where
  domain := ⟨isNonempty⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. z = !!(op(0).const)”⟩
    | Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const)”⟩
    | Language.Concatenation.Func.concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using NonemptyClosed.zero_ne_empty T M
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : e i ≠ ∅ := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 0 by simpa [Semiformula.Operator.val]
      use 0
      simpa using NonemptyClosed.zero_ne_empty T M
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 1 by simpa [Semiformula.Operator.val]
      use 1
      simpa using NonemptyClosed.one_ne_empty T M
    · suffices ∃! y : M, y ≠ ∅ ∧ y = e 0 ++ e 1 by simpa [Semiformula.Operator.val]
      use e 0 ++ e 1
      simpa using NonemptyClosed.append_ne_empty (T := T) M (he 0)
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace nonemptyTranslation

variable {T}

@[simp]
lemma dom_iff : (nonemptyTranslation T).Dom x ↔ x ≠ ∅ := by
  simp [DirectTranslation.dom_iff, nonemptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* T]

variable (M T) in
/-- The letters and the concatenation of `M` restricted to the nonempty strings. -/
abbrev concatenationStructure : ConcatenationStructure ((nonemptyTranslation T).Model M) where
  zero := ⟨0, dom_iff.mpr <| NonemptyClosed.zero_ne_empty T M⟩
  one := ⟨1, dom_iff.mpr <| NonemptyClosed.one_ne_empty T M⟩
  append x y := ⟨x ++ y, dom_iff.mpr <|
    NonemptyClosed.append_ne_empty (T := T) M <| dom_iff.mp x.dom⟩

/--
The structure of the model of `nonemptyTranslation` is the standard one of the letters and the
concatenation restricted to the nonempty strings.
-/
lemma struc_eq :
    Model.struc (nonemptyTranslation T) M = @standardModel _ (concatenationStructure M T) :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [nonemptyTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationStructure

variable {x y : M} {hx : (nonemptyTranslation T).Dom x} {hy : (nonemptyTranslation T).Dom y}

@[simp]
lemma zero_eq_mk : (0 : (nonemptyTranslation T).Model M) =
    ⟨0, dom_iff.mpr <| NonemptyClosed.zero_ne_empty T M⟩ := rfl

@[simp]
lemma one_eq_mk : (1 : (nonemptyTranslation T).Model M) =
    ⟨1, dom_iff.mpr <| NonemptyClosed.one_ne_empty T M⟩ := rfl

@[simp]
lemma mk_append_mk : (⟨x, hx⟩ ++ ⟨y, hy⟩ : (nonemptyTranslation T).Model M) =
    ⟨x ++ y, dom_iff.mpr <| NonemptyClosed.append_ne_empty (T := T) M <| dom_iff.mp hx⟩ := rfl

end

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{TC}$ with the empty string form a model of
$\mathsf{TC}$.
- [Vis09, Appendix A]
-/
instance [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : ((nonemptyTranslation 𝗧𝗖ₑ).Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case editor =>
    suffices ∀ x y z w : M, x ++ y = z ++ w → (x = z ∧ y = w) ∨
        ∃ u, u ≠ ∅ ∧ ((x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w)) by
      simpa [models_iff, Model.forall_iff, Model.exists_iff] using
        fun x _ y _ z _ w _ ↦ this x y z w
    intro x y z w h
    obtain ⟨u, hu⟩ := TCEmpty.editor h
    rcases eq_or_ne u ∅ with rfl | hu'
    · exact .inl <| by simpa using hu
    · exact .inr ⟨u, hu', hu⟩
  case zeroNeConcat =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (hx : x ≠ ∅) (y : M) (hy : y ≠ ∅)
      (h : 0 = x ++ y) ↦ (TCEmpty.eq_empty_of_append_isAtom <| by simp [← h]).elim hx hy
  case oneNeConcat =>
    simpa [models_iff, Model.forall_iff] using fun (x : M) (hx : x ≠ ∅) (y : M) (hy : y ≠ ∅)
      (h : 1 = x ++ y) ↦ (TCEmpty.eq_empty_of_append_isAtom <| by simp [← h]).elim hx hy
  all_goals simp [models_iff, Model.forall_iff, TCEmpty.append_assoc]

/--
$\mathsf{TC}$ with the empty string interprets $\mathsf{TC}$ on the nonempty strings.
- [Vis09, Appendix A]
- [HH14, Theorem 3]
-/
instance : 𝗧𝗖ₑ ⊳ 𝗧𝗖 where
  trln := nonemptyTranslation 𝗧𝗖ₑ
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
    rintro (_ | x) y (_ | z) w h
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
    · rcases editor (Option.some.inj h) with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
        [use none; use some u; use some u] <;> simp
  case zeroNeEmpty => simp [models_iff, Option.empty_eq_none, Option.zero_eq_some]
  case oneNeEmpty => simp [models_iff, Option.empty_eq_none, Option.one_eq_some]
  case zeroAtom =>
    suffices ∀ x y : Option M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h <;> simp_all [Option.empty_eq_none, Option.zero_eq_some]
  case oneAtom =>
    suffices ∀ x y : Option M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h <;> simp_all [Option.empty_eq_none, Option.one_eq_some]
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
  cases x <;> simp [IsEmptyCode, emptyCode]

lemma isEmptyCode_iff : IsEmptyCode x ↔ ∃ y, emptyCode y = x := by
  constructor
  · rintro (rfl | ⟨y, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some y, rfl⟩
  · rintro ⟨y, rfl⟩
    simp

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma emptyCode_injective : Function.Injective (emptyCode (M := M)) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (one_ne_append 1 y h).elim
  · exact (one_ne_append 1 x h.symm).elim
  · exact congrArg some <| isAtom_one.append_left_cancel h

lemma isCodeAppend_emptyCode_iff {x y : Option M} :
    IsCodeAppend z (emptyCode x) (emptyCode y) ↔ z = emptyCode (x ++ y) := by
  rcases y with _ | y
  · simp [IsCodeAppend, emptyCode]
  · have h (w : M) : 1 ++ y = 1 ++ w ↔ y = w := ⟨isAtom_one.append_left_cancel, congrArg _⟩
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

instance : Entailment.Consistent 𝗧𝗖ₑ := DirectInterpretation.consistent (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{TC}$ with the empty string is essentially undecidable.
- [Hor11, §2]
-/
instance : 𝗧𝗖ₑ.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖)

end code

section empty

variable {M : Type*} [ConcatenationEmptyStructure M] {x y z : M}

/-- Every nonempty suffix of `x` begins with the letter $0$. -/
def NonemptySuffixesBeginWithZero (x : M) : Prop := ∀ u v, x = u ++ v → v = ∅ ∨ ∃ w, v = 0 ++ w

/-- Every nonempty suffix of `x` begins with the letter $0$. -/
def nonemptySuffixesBeginWithZero : Semisentence ℒ⌢ₑ 1 :=
  “x. ∀ u v, x = u ⌢ v → v = ⋆ ∨ ∃ w, v = !!(op(0).const) ⌢ w”

@[simp]
lemma eval_nonemptySuffixesBeginWithZero :
    M ⊧/![x] nonemptySuffixesBeginWithZero ↔ NonemptySuffixesBeginWithZero x := by
  simp [nonemptySuffixesBeginWithZero, NonemptySuffixesBeginWithZero]

open Classical in
/--
The string `0 ++ x` if every nonempty suffix of `x` begins with the letter $0$, and `x` otherwise.
-/
noncomputable def shift (x : M) : M := if NonemptySuffixesBeginWithZero x then 0 ++ x else x

/-- `y` is `shift x`. -/
def isShift : Semisentence ℒ⌢ₑ 2 :=
  “y x. (!nonemptySuffixesBeginWithZero x ∧ y = !!(op(0).const) ⌢ x) ∨
    (¬!nonemptySuffixesBeginWithZero x ∧ y = x)”

@[simp]
lemma eval_isShift : M ⊧/![y, x] isShift ↔ y = shift x := by
  by_cases h : NonemptySuffixesBeginWithZero x <;> simp [isShift, shift, h]

section map

variable {N : Type*} [ConcatenationEmptyStructure N] (g : M ≃ N) (zero : g 0 = 0)
    (append : ∀ x y, g (x ++ y) = g x ++ g y) (empty : g ∅ = ∅)

include zero append empty

lemma nonemptySuffixesBeginWithZero_map_iff :
    NonemptySuffixesBeginWithZero (g x) ↔ NonemptySuffixesBeginWithZero x := by
  simp [NonemptySuffixesBeginWithZero, g.surjective.forall, g.surjective.exists, ← zero,
    ← append, ← empty]

lemma shift_map (x : M) : shift (g x) = g (shift x) := by
  by_cases h : NonemptySuffixesBeginWithZero x <;>
    simp [shift, nonemptySuffixesBeginWithZero_map_iff g zero append empty, h, zero, append]

end map

section TCEmpty

variable [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

namespace TCEmpty

lemma zero_append_cancel (h : 0 ++ x = 0 ++ y) : x = y := by
  have hu {u : M} (hu : 0 ++ u = 0) : u = ∅ :=
    (eq_empty_of_append_isAtom <| hu.symm ▸ isAtom_zero).resolve_left zero_ne_empty
  obtain ⟨u, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := editor h
  · simpa [hu h₁] using h₂
  · simpa [hu h₁.symm] using h₂

end TCEmpty

lemma nonemptySuffixesBeginWithZero_empty : NonemptySuffixesBeginWithZero (∅ : M) :=
  fun _ _ h ↦ Or.inl (TCEmpty.eq_empty_of_append_eq_empty h.symm).2

lemma nonemptySuffixesBeginWithZero_zero_append_iff :
    NonemptySuffixesBeginWithZero (0 ++ x) ↔ NonemptySuffixesBeginWithZero x := by
  constructor
  · exact fun h u v hx ↦ h (0 ++ u) v <| by rw [hx, TCEmpty.append_assoc]
  · intro h u v hx
    obtain ⟨w, ⟨-, hw⟩ | ⟨hw, rfl⟩⟩ := TCEmpty.editor hx
    · exact h w v hw
    · rcases TCEmpty.eq_empty_of_append_isAtom (hw ▸ isAtom_zero) with rfl | rfl
      · right
        use x
        simp [show w = 0 by simpa using hw.symm]
      · simpa using h ∅ x (by simp)

lemma shift_injective : Function.Injective (shift (M := M)) := by
  intro x y h
  by_cases hx : NonemptySuffixesBeginWithZero x <;>
    by_cases hy : NonemptySuffixesBeginWithZero y <;>
    simp only [shift, hx, hy, ite_true, ite_false] at h
  · exact TCEmpty.zero_append_cancel h
  · exact (hy <| h ▸ nonemptySuffixesBeginWithZero_zero_append_iff.mpr hx).elim
  · exact (hx <| h ▸ nonemptySuffixesBeginWithZero_zero_append_iff.mpr hy).elim
  · exact h

/-- The strings `shift x` are the nonempty strings. -/
lemma exists_shift_eq_iff : (∃ x, shift x = y) ↔ y ≠ ∅ := by
  constructor
  · rintro ⟨x, rfl⟩ h
    by_cases hx : NonemptySuffixesBeginWithZero x <;>
      simp only [shift, hx, ite_true, ite_false] at h
    · exact TCEmpty.zero_ne_empty (TCEmpty.eq_empty_of_append_eq_empty h).1
    · exact hx <| h ▸ nonemptySuffixesBeginWithZero_empty
  · intro hy
    by_cases h : NonemptySuffixesBeginWithZero y
    · obtain ⟨x, rfl⟩ := (h ∅ y (by simp)).resolve_left hy
      use x
      simp [shift, nonemptySuffixesBeginWithZero_zero_append_iff.mp h]
    · use y
      simp [shift, h]

@[simp]
lemma shift_ne_empty (x : M) : shift x ≠ ∅ := exists_shift_eq_iff.mp ⟨x, rfl⟩

lemma existsUnique_eq_shift (hy : y ≠ ∅) : ∃! x, y = shift x := by
  obtain ⟨x, rfl⟩ := exists_shift_eq_iff.mpr hy
  use x
  simp [shift_injective.eq_iff, eq_comm]

end TCEmpty

end empty

section shiftTranslation

variable {M : Type} [ConcatenationEmptyStructure M]

/--
The unrelativized translation of $\mathsf{TC}$ into $\mathsf{TC}$ with the empty string that reads
a string `x` as the nonempty string `shift x`.
-/
def shiftTranslation : DirectTranslation 𝗧𝗖ₑ ℒ⌢ where
  domain := ⟨⊤⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. !isShift !!(op(0).const) z”⟩
    | Language.Concatenation.Func.one => ⟨“z. !isShift !!(op(1).const) z”⟩
    | Language.Concatenation.Func.concat =>
      ⟨“z x y. ∃ u v, !isShift u x ∧ !isShift v y ∧ !isShift (u ⌢ v) z”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift (M := M) TCEmpty.zero_ne_empty
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift (M := M) TCEmpty.one_ne_empty
    · simpa [Semiformula.Operator.val] using existsUnique_eq_shift
        (y := shift (e 0) ++ shift (e 1)) fun h ↦
          shift_ne_empty _ (TCEmpty.eq_empty_of_append_eq_empty h).1
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace shiftTranslation

@[simp]
lemma dom {M : Type*} [Tarski.Structure ℒ⌢ₑ M] (x : M) : shiftTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, shiftTranslation, Semiformula.Operator.val]

lemma func_zero_val_iff {e : Fin 1 → M} :
    (shiftTranslation.func Language.Concatenation.Func.zero).val e ↔ 0 = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

lemma func_one_val_iff {e : Fin 1 → M} :
    (shiftTranslation.func Language.Concatenation.Func.one).val e ↔ 1 = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

lemma func_concat_val_iff {e : Fin 3 → M} :
    (shiftTranslation.func Language.Concatenation.Func.concat).val e ↔
      shift (e 1) ++ shift (e 2) = shift (e 0) := by
  simp [shiftTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

/-- The bijection of the strings of `M` with the nonempty ones. -/
noncomputable def equiv : shiftTranslation.Model M ≃ (nonemptyTranslation 𝗧𝗖ₑ).Model M :=
  Equiv.ofBijective (fun x ↦ ⟨shift (x : M), by simp⟩) <| by
    constructor
    · exact fun x y h ↦ Model.ext <| shift_injective <| congrArg Model.val h
    · intro y
      obtain ⟨x, hx⟩ := exists_shift_eq_iff.mpr <| nonemptyTranslation.dom_iff.mp y.dom
      exact ⟨⟨x, dom x⟩, Model.ext hx⟩

@[simp]
lemma val_equiv (x : shiftTranslation.Model M) : (equiv x : M) = shift (x : M) := rfl

lemma shift_equiv_symm (y : (nonemptyTranslation 𝗧𝗖ₑ).Model M) :
    shift ((equiv.symm y : _) : M) = y := by
  rw [← val_equiv, Equiv.apply_symm_apply]

/-- The letters and the concatenation of the nonempty strings transported to all strings. -/
noncomputable abbrev concatenationStructure : ConcatenationStructure (shiftTranslation.Model M) :=
  let := nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ
  .ofEquiv equiv

lemma struc_eq :
    Model.struc shiftTranslation M = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      let := nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ
      symm
      apply Model.func_iff.mpr
      cases f
      · exact func_zero_val_iff.mpr (shift_equiv_symm 0).symm
      · exact func_one_val_iff.mpr (shift_equiv_symm 1).symm
      · exact func_concat_val_iff.mpr (shift_equiv_symm (equiv (v 0) ++ equiv (v 1))).symm)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

end shiftTranslation

/--
The strings of a model of $\mathsf{TC}$ with the empty string, read as its nonempty strings, form a
model of $\mathsf{TC}$.
-/
instance [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : (shiftTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  have : (nonemptyTranslation 𝗧𝗖ₑ).Model M ≡ₑ[ℒ⌢] shiftTranslation.Model M := by
    rw [shiftTranslation.struc_eq,
      @standardModel_ofEquiv _ (nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ),
      ← nonemptyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv _
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory
    (M₁ := (nonemptyTranslation 𝗧𝗖ₑ).Model M)).mp inferInstance

end shiftTranslation

section option

variable {M : Type*} [ConcatenationStructure M] {x y z : M}

/-- Every suffix of `x` begins with the letter $0$. -/
def SuffixesBeginWithZero (x : M) : Prop := ∀ y, x ◧ y → 0 ◨ y

/-- Every suffix of `x` begins with the letter $0$. -/
def suffixesBeginWithZero : Semisentence ℒ⌢ 1 :=
  “x. ∀ y, !isSuffix y x → !isPrefix !!(op(0).const) y”

@[simp]
lemma eval_suffixesBeginWithZero :
    M ⊧/![x] suffixesBeginWithZero ↔ SuffixesBeginWithZero x := by
  simp [suffixesBeginWithZero, SuffixesBeginWithZero]

lemma nonemptySuffixesBeginWithZero_some_iff :
    NonemptySuffixesBeginWithZero (some x) ↔ SuffixesBeginWithZero x := by
  have h (y : M) : (∃ w : Option M, some y = 0 ++ w) ↔ 0 ◨ y := by
    simp [Option.exists, Option.zero_eq_some, IsPrefix, eq_comm (a := y)]
  simp only [NonemptySuffixesBeginWithZero, SuffixesBeginWithZero, Option.forall, h,
    Option.empty_eq_none]
  simpa [IsSuffix, or_imp, forall_and] using fun _ ↦ forall_comm

open Classical in
/--
The letter $0$ for the empty string; for a string `x`, the string `0 ++ x` if every suffix of `x`
begins with the letter $0$, and `x` otherwise.
-/
noncomputable def shiftOption : Option M → M
  | none => 0
  | some x => if SuffixesBeginWithZero x then 0 ++ x else x

/-- `y` is `shiftOption (some x)`. -/
def isShiftSome : Semisentence ℒ⌢ 2 :=
  “y x. (!suffixesBeginWithZero x ∧ y = !!(op(0).const) ⌢ x) ∨
    (¬!suffixesBeginWithZero x ∧ y = x)”

@[simp]
lemma eval_isShiftSome : M ⊧/![y, x] isShiftSome ↔ y = shiftOption (some x) := by
  by_cases h : SuffixesBeginWithZero x <;> simp [isShiftSome, shiftOption, h]

/--
`z` corresponds under `shiftOption` to the concatenation of the strings corresponding to `x`
and `y`.
-/
def IsShiftAppend (z x y : M) : Prop :=
  (x = 0 ∧ z = y) ∨ (y = 0 ∧ z = x) ∨
    ∃ u v, x = shiftOption (some u) ∧ y = shiftOption (some v) ∧ z = shiftOption (some (u ++ v))

/--
`z` corresponds under `shiftOption` to the concatenation of the strings corresponding to `x`
and `y`.
-/
def isShiftAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (x = !!(op(0).const) ∧ z = y) ∨ (y = !!(op(0).const) ∧ z = x) ∨
    ∃ u v, !isShiftSome x u ∧ !isShiftSome y v ∧ !isShiftSome z (u ⌢ v)”

@[simp]
lemma eval_isShiftAppend : M ⊧/![z, x, y] isShiftAppend ↔ IsShiftAppend z x y := by
  simp [isShiftAppend, IsShiftAppend]

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma some_shiftOption (x : Option M) : some (shiftOption x) = shift x := by
  rcases x with _ | x
  · rw [← Option.empty_eq_none, shift, ite_eq_left nonemptySuffixesBeginWithZero_empty]
    simp [Option.empty_eq_none, Option.zero_eq_some, shiftOption]
  · by_cases h : SuffixesBeginWithZero x <;>
      simp [shift, shiftOption, nonemptySuffixesBeginWithZero_some_iff, h, Option.zero_eq_some]

/-- The bijection of the strings of `M` and the empty string with the strings of `M`. -/
noncomputable def shiftOptionEquiv : Option M ≃ M :=
  Equiv.ofBijective shiftOption <| by
    constructor
    · intro x y h
      apply shift_injective
      rw [← some_shiftOption, h, some_shiftOption]
    · intro y
      obtain ⟨x, hx⟩ := exists_shift_eq_iff (y := some y).mpr <| by simp [Option.empty_eq_none]
      use x
      rwa [← some_shiftOption, Option.some_inj] at hx

@[simp]
lemma shiftOptionEquiv_apply (x : Option M) : shiftOptionEquiv x = shiftOption x := rfl

lemma shiftOption_inj {x y : Option M} : shiftOption x = shiftOption y ↔ x = y :=
  shiftOptionEquiv.apply_eq_iff_eq

lemma isShiftAppend_shiftOption_iff {x y : Option M} :
    IsShiftAppend z (shiftOption x) (shiftOption y) ↔ z = shiftOption (x ++ y) := by
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [IsShiftAppend, shiftOption_inj, show (0 : M) = shiftOption none from rfl]

end option

section emptyShiftTranslation

variable {M : Type} [ConcatenationStructure M]

/--
The unrelativized translation of $\mathsf{TC}$ with the empty string into $\mathsf{TC}$ that reads
the string `shiftOption x` as the string `x` or the empty string.
-/
def emptyShiftTranslation : DirectTranslation 𝗧𝗖 ℒ⌢ₑ where
  domain := ⟨⊤⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. !isShiftSome z !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. !isShiftSome z !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isShiftAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(0).const)”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [Semiformula.Operator.val]
    · simp [Semiformula.Operator.val]
    · obtain ⟨x, y, rfl⟩ : ∃ x y, e = ![x, y] := ⟨_, _, Matrix.fun_eq_vec_two _⟩
      obtain ⟨x, rfl⟩ := shiftOptionEquiv.surjective x
      obtain ⟨y, rfl⟩ := shiftOptionEquiv.surjective y
      simp [Semiformula.Operator.val, isShiftAppend_shiftOption_iff]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyShiftTranslation

@[simp]
lemma dom {M : Type*} [Tarski.Structure ℒ⌢ M] (x : M) : emptyShiftTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, emptyShiftTranslation, Semiformula.Operator.val]

lemma func_zero_val_iff {e : Fin 1 → M} :
    (emptyShiftTranslation.func (Sum.inl Language.Concatenation.Func.zero)).val e ↔
      e 0 = shiftOption (some 0) := by
  simp [emptyShiftTranslation, Semiformula.Operator.val]

lemma func_one_val_iff {e : Fin 1 → M} :
    (emptyShiftTranslation.func (Sum.inl Language.Concatenation.Func.one)).val e ↔
      e 0 = shiftOption (some 1) := by
  simp [emptyShiftTranslation, Semiformula.Operator.val]

lemma func_concat_val_iff {e : Fin 3 → M} :
    (emptyShiftTranslation.func (Sum.inl Language.Concatenation.Func.concat)).val e ↔
      IsShiftAppend (e 0) (e 1) (e 2) := by
  rw [← eval_isShiftAppend, ← Matrix.fun_eq_vec_three]
  rfl

lemma func_empty_val_iff {e : Fin 1 → M} :
    (emptyShiftTranslation.func (Sum.inr <| Language.Constant.Func.const ⟨⟩)).val e ↔ e 0 = 0 := by
  simp [emptyShiftTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

/-- The bijection of the strings of `M` and the empty string with the strings of `M`. -/
noncomputable def equiv : Option M ≃ emptyShiftTranslation.Model M :=
  shiftOptionEquiv.trans
    { toFun x := ⟨x, dom x⟩
      invFun x := x }

@[simp]
lemma val_equiv (x : Option M) : (equiv x : M) = shiftOption x := rfl

/--
The letters, the concatenation and the empty string of `Option M` transported to the strings of `M`.
-/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure (emptyShiftTranslation.Model M) := .ofEquiv equiv.symm

lemma struc_eq :
    Model.struc emptyShiftTranslation M = @standardModelEmpty _ concatenationEmptyStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · exact func_zero_val_iff.mpr rfl
      · exact func_one_val_iff.mpr rfl
      · have h : equiv.symm (equiv (v 0)) ++ equiv.symm (equiv (v 1)) = v 0 ++ v 1 := by simp
        exact func_concat_val_iff.mpr <| isShiftAppend_shiftOption_iff.mpr <|
          congrArg shiftOption h
      · exact func_empty_val_iff.mpr rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

end emptyShiftTranslation

/--
The strings of a model of $\mathsf{TC}$, read as its strings and the empty string, form a model of
$\mathsf{TC}$ with the empty string.
-/
instance [M↓[ℒ⌢] ⊧* 𝗧𝗖] : (emptyShiftTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ := by
  have : Option M ≡ₑ[ℒ⌢ₑ] emptyShiftTranslation.Model M := by
    rw [emptyShiftTranslation.struc_eq, standardModelEmpty_ofEquiv]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv _
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option M)).mp inferInstance

end emptyShiftTranslation

/--
The interpretation of $\mathsf{TC}$ in $\mathsf{TC}$ with the empty string by `shiftTranslation`.
-/
abbrev shiftInterpretation : 𝗧𝗖ₑ ⊳ 𝗧𝗖 where
  trln := shiftTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
The interpretation of $\mathsf{TC}$ with the empty string in $\mathsf{TC}$ by
`emptyShiftTranslation`.
-/
abbrev emptyShiftInterpretation : 𝗧𝗖 ⊳ 𝗧𝗖ₑ where
  trln := emptyShiftTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

section

variable {M : Type} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma emptyShiftTranslation.shift_eq (x : emptyShiftTranslation.Model M) :
    @shift _ concatenationEmptyStructure x = equiv (some (x : M)) := by
  let := concatenationEmptyStructure (M := M)
  obtain ⟨x, rfl⟩ := equiv.surjective x
  rw [shift_map equiv (rfl : equiv (0 : Option M) = 0) (fun x y ↦ ?_) (rfl : equiv ∅ = ∅),
    ← some_shiftOption, val_equiv]
  change _ = equiv (equiv.symm (equiv x) ++ equiv.symm (equiv y))
  simp

end

section

variable {M : Type} [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

namespace shiftTranslation

/--
The bijection of the strings of the model of `shiftTranslation` and the empty string with the
strings of `M`.
-/
noncomputable def optionEquiv : Option (shiftTranslation.Model M) ≃ M :=
  Equiv.ofBijective (fun x ↦ x.elim ∅ fun x ↦ shift (x : M)) <| by
    constructor
    · rintro (_ | x) (_ | y) h
      · rfl
      · exact (shift_ne_empty _ h.symm).elim
      · exact (shift_ne_empty _ h).elim
      · exact congrArg some <| Model.ext <| shift_injective h
    · intro y
      rcases Classical.em (y = ∅) with rfl | h
      · exact ⟨none, rfl⟩
      · obtain ⟨x, hx⟩ := exists_shift_eq_iff.mpr h
        exact ⟨some ⟨x, dom x⟩, hx⟩

lemma optionEquiv_zero :
    let := concatenationStructure (M := M)
    optionEquiv (0 : Option (shiftTranslation.Model M)) = 0 :=
  shift_equiv_symm (nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ).toZero.zero

lemma optionEquiv_one :
    let := concatenationStructure (M := M)
    optionEquiv (1 : Option (shiftTranslation.Model M)) = 1 :=
  shift_equiv_symm (nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ).toOne.one

lemma optionEquiv_append (x y : Option (shiftTranslation.Model M)) :
    let := concatenationStructure (M := M)
    optionEquiv (x ++ y) = optionEquiv x ++ optionEquiv y := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact (TCEmpty.empty_append _).symm
  · exact (TCEmpty.empty_append _).symm
  · exact (TCEmpty.append_empty _).symm
  · exact shift_equiv_symm <|
      (nonemptyTranslation.concatenationStructure M 𝗧𝗖ₑ).toAppend.append (equiv x) (equiv y)

lemma val_shiftOption_eq (x : Option (shiftTranslation.Model M)) :
    ((@shiftOption _ concatenationStructure x : shiftTranslation.Model M) : M) =
      optionEquiv x := by
  let := concatenationStructure (M := M)
  apply shift_injective
  have : (shiftTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
    rw [← struc_eq]
    infer_instance
  rw [shift_map optionEquiv optionEquiv_zero optionEquiv_append rfl, ← some_shiftOption]
  rfl

end shiftTranslation

end

lemma emptyShiftTranslation.func_val_iff {M : Type} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖]
    {k} (f : (ℒ⌢).Func k) (e : Fin (k + 1) → emptyShiftTranslation.Model M) :
    (shiftTranslation.func f).val e ↔
      ((DirectTranslation.id 𝗧𝗖).func f).val fun i ↦ (e i : M) := by
  rw [id_func_val_iff, struc_eq]
  let := concatenationEmptyStructure (M := M)
  have h {x : M} {y z : emptyShiftTranslation.Model M} (hz : z = equiv (some x)) :
      z = shift y ↔ (y : M) = x := by
    simp [hz, shift_eq, eq_comm]
  cases f
  · exact shiftTranslation.func_zero_val_iff.trans <| h rfl
  · exact shiftTranslation.func_one_val_iff.trans <| h rfl
  · apply shiftTranslation.func_concat_val_iff.trans <| h _
    rw [shift_eq, shift_eq]
    have h (x y : M) :
        equiv.symm (equiv (some x)) ++ equiv.symm (equiv (some y)) = some (x ++ y) := by simp
    exact congrArg equiv <| h (e 1) (e 2)

lemma shiftTranslation.func_val_iff {M : Type} [ConcatenationEmptyStructure M]
    [M↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] {k} (f : (ℒ⌢ₑ).Func k) (e : Fin (k + 1) → shiftTranslation.Model M) :
    (emptyShiftTranslation.func f).val e ↔
      ((DirectTranslation.id 𝗧𝗖ₑ).func f).val fun i ↦ (e i : M) := by
  rw [id_func_val_iff]
  have : (shiftTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  rw [struc_eq] at this ⊢
  let := concatenationStructure (M := M)
  have h {x : shiftTranslation.Model M} {y : Option (shiftTranslation.Model M)} {z : M}
      (hz : optionEquiv y = z) : x = shiftOption y ↔ (x : M) = z := by
    rw [← hz, ← val_shiftOption_eq, Model.val_inj_iff]
  rcases f with (_ | _ | _) | ⟨⟨⟩⟩
  · exact emptyShiftTranslation.func_zero_val_iff.trans <| h optionEquiv_zero
  · exact emptyShiftTranslation.func_one_val_iff.trans <| h optionEquiv_one
  · obtain ⟨x, hx⟩ := shiftOptionEquiv.surjective (e 1)
    obtain ⟨y, hy⟩ := shiftOptionEquiv.surjective (e 2)
    apply emptyShiftTranslation.func_concat_val_iff.trans
    rw [← hx, ← hy]
    apply isShiftAppend_shiftOption_iff.trans <| h _
    rw [optionEquiv_append, ← val_shiftOption_eq, ← val_shiftOption_eq]
    exact congrArg₂ (fun a b : shiftTranslation.Model M ↦ (a : M) ++ (b : M)) hx hy
  · exact emptyShiftTranslation.func_empty_val_iff.trans <| h (y := none) rfl

open DirectInterpretation in
/--
$\mathsf{TC}$ and $\mathsf{TC}$ with the empty string are definitionally equivalent.
- [Vis09, Appendix A]
-/
def tcDefinitionalEquivalence : DefinitionalEquivalence 𝗧𝗖 𝗧𝗖ₑ where
  r := emptyShiftInterpretation
  l := shiftInterpretation
  equivalent_id_left := {
    domain := complete.{0} _ _ fun M _ _ ↦ models_domainIff_iff.mpr fun x ↦ iff_of_true
      ((compDirectTranslation_Dom_iff shiftTranslation emptyShiftInterpretation).mpr
        ⟨⟨⟨x, emptyShiftTranslation.dom x⟩, shiftTranslation.dom _⟩, rfl⟩) (id_Dom x)
    rel R := complete.{0} _ _ fun M _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦ by
      let e' (i) : emptyShiftTranslation.Model M := ⟨e i, emptyShiftTranslation.dom _⟩
      apply (translateOperator_val_iff emptyShiftInterpretation (shiftTranslation.rel R) e').trans
      apply Iff.trans _ id_rel_val_iff.symm
      cases R
      change Semiformula.Evalb e' “x y. x = y” ↔ e 0 = e 1
      simp [e']
    func f := complete.{0} _ _ fun M _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦
      let e' (i) : emptyShiftTranslation.Model M := ⟨e i, emptyShiftTranslation.dom _⟩
      (translateOperator_val_iff emptyShiftInterpretation _ e').trans <|
        emptyShiftTranslation.func_val_iff f e' }
  equivalent_id_right := {
    domain := completeEmpty.{0} _ _ fun M _ _ ↦ models_domainIff_iff.mpr fun x ↦ iff_of_true
      ((compDirectTranslation_Dom_iff emptyShiftTranslation shiftInterpretation).mpr
        ⟨⟨⟨x, shiftTranslation.dom x⟩, emptyShiftTranslation.dom _⟩, rfl⟩) (id_Dom x)
    rel R := completeEmpty.{0} _ _ fun M _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦ by
      let e' (i) : shiftTranslation.Model M := ⟨e i, shiftTranslation.dom _⟩
      apply (translateOperator_val_iff shiftInterpretation (emptyShiftTranslation.rel R) e').trans
      apply Iff.trans _ id_rel_val_iff.symm
      rcases R with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      change Semiformula.Evalb e' “x y. x = y” ↔ e 0 = e 1
      simp [e']
    func f := completeEmpty.{0} _ _ fun M _ _ ↦ models_operatorIff_iff.mpr fun e _ ↦
      let e' (i) : shiftTranslation.Model M := ⟨e i, shiftTranslation.dom _⟩
      (translateOperator_val_iff shiftInterpretation _ e').trans <|
        shiftTranslation.func_val_iff f e' }

end FFL.FirstOrder.Concatenation

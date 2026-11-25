module

public import Concatenation.TC.EmptyInterpretation
public import Concatenation.WTC.Editor
public import Concatenation.WTC.Standard

/-!
# $\mathsf{WTC}$ with the empty string and the editor axiom

$\mathsf{WTC}$ with the empty string and the unrestricted editor axiom does not interpret
$\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of $\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
inductive IsWTCEmptyEditorAxiom : Sentence ℒ⌢ₑ → Prop
  | wtcEmpty : ∀ φ ∈ 𝗪𝗧𝗖ₑ, IsWTCEmptyEditorAxiom φ
  | editor : IsWTCEmptyEditorAxiom “∀ x y s t, x ⌢ y = s ⌢ t →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”

/--
$\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
abbrev WTCEmptyEditor : Theory ℒ⌢ₑ := Set.ofPred IsWTCEmptyEditorAxiom

instance : 𝗪𝗧𝗖ₑ ⪯ WTCEmptyEditor := Entailment.WeakerThan.ofSubset IsWTCEmptyEditorAxiom.wtcEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ WTCEmptyEditor :=
  Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖ₑ) inferInstance inferInstance

open ConcatenationStructure ConcatenationEmptyStructure DirectTranslation

section option

variable {M : Type*} [ConcatenationStructure M] {x y : M}

lemma Option.ofList_cons (b : Bool) (l : List Bool) :
    (ofList (b :: l) : Option M) = some (ofFreeSemigroup ⟨b, l⟩) := by
  suffices ∀ (l : List Bool) (x : M),
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (some x) =
        some (l.foldl (fun m b ↦ m ++ if b then 1 else 0) x) by
    rw [ofFreeSemigroup, ← this]
    cases b <;> rfl
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro x
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    cases b <;> rfl

@[simp]
lemma Option.not_isSubstring_none : ¬IsSubstring (some x) (none : Option M) := by
  rintro (h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩)
  · simp at h
  · rcases u with _ | u <;> simp at h
  · rcases v with _ | v <;> simp at h
  · rcases u with _ | u <;> rcases v with _ | v <;> simp at h
  · rcases u with _ | u <;> rcases v with _ | v <;> simp at h

lemma Option.isSubstring_of_some (h : IsSubstring (some x) (some y)) : IsSubstring x y := by
  rcases h with h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · exact .inl <| Option.some.inj h
  · rcases u with _ | u
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inl ⟨u, Option.some.inj h⟩
  · rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, Option.some.inj h⟩
  · rcases u with _ | u <;> rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, by simpa using h⟩
    · exact .inr <| .inl ⟨u, by simpa using h⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨u, v, Option.some.inj h⟩
  · rcases u with _ | u <;> rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, by simpa using h⟩
    · exact .inr <| .inl ⟨u, by simpa using h⟩
    · exact .inr <| .inr <| .inr <| .inr ⟨u, v, Option.some.inj h⟩

end option

namespace WTCEditor

section models

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* WTCEditor]

instance : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ⟨fun _ h ↦ Theory.models M WTCEditor (.wtc _ h)⟩

lemma editor {x y z w : M} (h : x ++ y = z ++ w) :
    (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCEditorAxiom.editor
  exact this x y z w h

/--
The strings of a model of $\mathsf{WTC}$ with the editor axiom together with an empty string form a
model of $\mathsf{WTC}$ with the empty string and the editor axiom.
-/
instance : (Option M)↓[ℒ⌢ₑ] ⊧* WTCEmptyEditor := by
  constructor
  rintro _ (⟨_, hσ⟩ | _)
  swap
  · suffices ∀ x y z w : Option M, x ++ y = z ++ w →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ ↦ Option.editor fun _ _ _ _ ↦ editor
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyUnit => simp [models_iff, Option.empty_eq_none]
  case concatAssoc u =>
    suffices ∀ x y z : Option M, IsSubstring (x ++ y ++ z) (ofList u) ∨
        IsSubstring (x ++ (y ++ z)) (ofList u) → x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    rintro (_ | x) (_ | y) (_ | z) <;>
      simp only [Option.none_append, Option.append_none, implies_true, Option.some_append_some,
        Option.some.injEq]
    rcases u with _ | ⟨b, l⟩
    · simp [ofList, Option.empty_eq_none]
    · rw [Option.ofList_cons]
      have assoc : ∀ x y z : M, IsSubstring (x ++ y ++ z) (ofFreeSemigroup ⟨b, l⟩) ∨
          IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup ⟨b, l⟩) → x ++ y ++ z = x ++ (y ++ z) := by
        simpa [models_iff] using Theory.models M 𝗪𝗧𝗖 (.concatAssoc ⟨b, l⟩)
      exact fun h ↦ assoc x y z <|
        h.imp Option.isSubstring_of_some Option.isSubstring_of_some
  case editor u =>
    suffices ∀ x y z w : Option M, x ++ y = z ++ w → IsSubstring (x ++ y) (ofList u) →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ h _ ↦ Option.editor (fun _ _ _ _ ↦ editor) h
  case zeroNeEmpty => simp [models_iff, Option.empty_eq_none, Option.zero_eq_some]
  case oneNeEmpty => simp [models_iff, Option.empty_eq_none, Option.one_eq_some]
  case zeroAtom =>
    suffices ∀ x y : Option M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact (WTC.append_ne_zero x y (Option.some.inj h)).elim
  case oneAtom =>
    suffices ∀ x y : Option M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact (WTC.append_ne_one x y (Option.some.inj h)).elim
  case zeroNeOne =>
    simpa [models_iff, Option.zero_eq_some, Option.one_eq_some] using WTC.zero_ne_one (M := M)

end models

section code

variable {M : Type} [ConcatenationStructure M] {x y z : M}

/-- `z` is the code of the concatenation of the strings coded by `x` and `y`. -/
def IsCodeAppend (z x y : M) : Prop :=
  (x = 1 ∧ z = y) ∨ (y = 1 ∧ z = x) ∨ ∃ u v, x = 1 ++ u ∧ y = 1 ++ v ∧ z = 1 ++ (u ++ v)

/-- `z` is the code of the concatenation of the strings coded by `x` and `y`. -/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (x = !!(op(1).const) ∧ z = y) ∨ (y = !!(op(1).const) ∧ z = x) ∨
    ∃ u v, x = !!(op(1).const) ⌢ u ∧ y = !!(op(1).const) ⌢ v ∧ z = !!(op(1).const) ⌢ (u ⌢ v)”

@[simp]
lemma eval_isCodeAppend : M ⊧/![z, x, y] isCodeAppend ↔ IsCodeAppend z x y := by
  simp [isCodeAppend, IsCodeAppend]

section

variable [M↓[ℒ⌢] ⊧* WTCEditor]

lemma one_append_cancel (h : 1 ++ x = 1 ++ y) : x = y := by
  rcases editor h with ⟨-, h⟩ | ⟨u, ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact h
  · exact (WTC.append_ne_one 1 u h).elim
  · exact (WTC.append_ne_one 1 u h.symm).elim

lemma emptyCode_injective : Function.Injective (emptyCode (M := M)) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (WTC.append_ne_one 1 y h.symm).elim
  · exact (WTC.append_ne_one 1 x h).elim
  · exact congrArg some <| one_append_cancel h

lemma isCodeAppend_emptyCode_iff {x y : Option M} :
    IsCodeAppend z (emptyCode x) (emptyCode y) ↔ z = emptyCode (x ++ y) := by
  have h (x y : M) : 1 ++ x = 1 ++ y ↔ x = y := ⟨one_append_cancel, congrArg _⟩
  have h' (x : M) : 1 ≠ 1 ++ x := fun h ↦ WTC.append_ne_one 1 x h.symm
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [IsCodeAppend, emptyCode, h, h', WTC.append_ne_one]

end

/--
The translation of the language with the empty string into $\mathsf{WTC}$ with the editor axiom that
codes a string by the string itself after the letter $1$, and the empty string by the letter $1$.
-/
def emptyTranslation : DirectTranslation WTCEditor ℒ⌢ₑ where
  domain := ⟨isEmptyCode⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
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

variable [M↓[ℒ⌢] ⊧* WTCEditor]

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
The codes of the strings of a model of $\mathsf{WTC}$ with the editor axiom and of the empty string
form a model of $\mathsf{WTC}$ with the empty string and the editor axiom.
-/
instance [M↓[ℒ⌢] ⊧* WTCEditor] : (emptyTranslation.Model M)↓[ℒ⌢ₑ] ⊧* WTCEmptyEditor := by
  have : Option M ≡ₑ[ℒ⌢ₑ] emptyTranslation.Model M := by
    rw [emptyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv emptyTranslation.equiv
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option M)).mp inferInstance

/--
$\mathsf{WTC}$ with the editor axiom interprets $\mathsf{WTC}$ with the empty string and the editor
axiom.
-/
instance : WTCEditor ⊳ WTCEmptyEditor where
  trln := emptyTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end code

end WTCEditor

/--
$\mathsf{WTC}$ with the empty string and the editor axiom does not interpret $\mathsf{TC}$.
- [HH14, Question 1]
-/
theorem WTCEmptyEditor.notInterprets_TCEmpty : WTCEmptyEditor ⋫ 𝗧𝗖ₑ :=
  ⟨fun π ↦ WTCEditor.notInterprets_TC.false <| DirectInterpretation.comp
    (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖) <| π.comp (inferInstance : WTCEditor ⊳ WTCEmptyEditor)⟩

end FFL.FirstOrder.Concatenation

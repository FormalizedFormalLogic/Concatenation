module

public import Concatenation.TC.EmptyInterpretation
public import Concatenation.WTC.Arithmetic
public import Concatenation.WTC.EmptyUnit
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.Undecidability

/-!
# $\mathsf{WTC}$ with and without the empty string

$\mathsf{WTC}$ with the empty string and $\mathsf{WTC}$ without it are mutually interpretable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open ConcatenationStructure ConcatenationEmptyStructure DirectTranslation

section standard

/--
The binary strings under concatenation.
- [HH14, §2]
-/
instance : ConcatenationEmptyStructure (List Bool) where
  zero := [false]
  one := [true]

instance : (List Bool)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ :=
  IsInitialEmptyEmbedding.models_WTCEmpty (c := id)
    { injective := Function.injective_id
      map_nil := rfl
      map_false := rfl
      map_true := rfl
      map_append := fun _ _ ↦ rfl
      exists_of_append_eq := fun {x y} _ _ ↦ ⟨x, y, rfl, rfl⟩ }

instance : Entailment.Consistent 𝗪𝗧𝗖ₑ :=
  let : (List Bool)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

end standard

namespace WTCEmpty

variable {M : Type} [ConcatenationEmptyStructure M] {x : M}

/--
The translation of $\mathsf{WTC}$ into $\mathsf{WTC}$ with the empty string, relativized to the
nonempty strings.
- [HH14, Theorem 3]
-/
def nonemptyTranslation : DirectTranslation 𝗪𝗧𝗖ₑ ℒ⌢ where
  domain := ⟨isNonempty⟩
  rel
    | Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Language.Concatenation.Func.zero => ⟨“z. z = !!(op(0).const)”⟩
    | Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const)”⟩
    | Language.Concatenation.Func.concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeEmpty.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val, isAtom_ne_empty]
  func_defined f := completeEmpty.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : e i ≠ ∅ := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 0 by simpa [Semiformula.Operator.val]
      use 0
      simp [isAtom_ne_empty]
    · suffices ∃! y : M, y ≠ ∅ ∧ y = 1 by simpa [Semiformula.Operator.val]
      use 1
      simp [isAtom_ne_empty]
    · suffices ∃! y : M, y ≠ ∅ ∧ y = e 0 ++ e 1 by simpa [Semiformula.Operator.val]
      use e 0 ++ e 1
      simpa using fun h ↦ he 0 (eq_empty_of_append_eq_empty h).1
  preserve_eq := completeEmpty.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace nonemptyTranslation

@[simp]
lemma dom_iff : nonemptyTranslation.Dom x ↔ x ≠ ∅ := by
  simp [DirectTranslation.dom_iff, nonemptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ]

/-- The letters and the concatenation of `M` restricted to the nonempty strings. -/
abbrev concatenationStructure : ConcatenationStructure (nonemptyTranslation.Model M) where
  zero := ⟨0, by simp [isAtom_ne_empty]⟩
  one := ⟨1, by simp [isAtom_ne_empty]⟩
  append x y := ⟨x ++ y, dom_iff.mpr fun h ↦ dom_iff.mp x.dom (eq_empty_of_append_eq_empty h).1⟩

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

section

attribute [local instance] concatenationStructure

lemma val_ofFreeSemigroup (u : FreeSemigroup Bool) :
    ((ofFreeSemigroup u : nonemptyTranslation.Model M) : M) = ofFreeSemigroup u := by
  suffices ∀ (l : List Bool) (x : nonemptyTranslation.Model M),
      ((l.foldl (fun m b ↦ m ++ if b then 1 else 0) x : nonemptyTranslation.Model M) : M) =
        l.foldl (fun m b ↦ m ++ if b then 1 else 0) (x : M) by
    rcases u with ⟨b, l⟩
    rw [ofFreeSemigroup, this]
    cases b <;> rfl
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro x
    simp only [List.foldl_cons, ih]
    cases b <;> rfl

lemma isSubstring_val {x y : nonemptyTranslation.Model M} (h : IsSubstring x y) :
    IsSubstring (x : M) y := by
  rcases h with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩
  · simp
  · exact isSubstring_append_right (u : M) x
  · exact isSubstring_append_left (x : M) v
  · exact isSubstring_append_append (u : M) x v
  · right; right; right; right
    use u, v
    rfl

lemma isSubstring_ofList_of_isSubstring {x : nonemptyTranslation.Model M} {u : FreeSemigroup Bool}
    (h : IsSubstring x (ofFreeSemigroup u)) : IsSubstring (x : M) (ofList u.toList) := by
  have h := isSubstring_val h
  rwa [val_ofFreeSemigroup] at h

end

end nonemptyTranslation

/--
The nonempty strings of a model of $\mathsf{WTC}$ with the empty string form a model of
$\mathsf{WTC}$.
- [HH14, Theorem 3]
-/
instance [M↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ] : (nonemptyTranslation.Model M)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  rw [nonemptyTranslation.struc_eq]
  let := nonemptyTranslation.concatenationStructure (M := M)
  have nonempty (x : nonemptyTranslation.Model M) : (x : M) ≠ ∅ :=
    nonemptyTranslation.dom_iff.mp x.dom
  have hc := isInitialEmptyEmbedding_ofList M
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case concatAssoc u =>
    suffices ∀ x y z : nonemptyTranslation.Model M,
        IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
          IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u) → x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    exact fun x y z h ↦ Model.ext <| hc.append_assoc_of_isSubstring <|
      h.imp nonemptyTranslation.isSubstring_ofList_of_isSubstring
        nonemptyTranslation.isSubstring_ofList_of_isSubstring
  case editor u =>
    suffices ∀ x y s t : nonemptyTranslation.Model M, x ++ y = s ++ t →
        IsSubstring (x ++ y) (ofFreeSemigroup u) → (x = s ∧ y = t) ∨
          ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) by
      simpa [models_iff]
    intro x y s t h hu
    have h : (x : M) ++ (y : M) = (s : M) ++ (t : M) := congrArg Model.val h
    have hu : IsSubstring ((x : M) ++ (y : M)) (ofList u.toList) :=
      nonemptyTranslation.isSubstring_ofList_of_isSubstring hu
    obtain ⟨p, q, hx, hy⟩ := hc.exists_of_isSubstring_append hu
    obtain ⟨r, o, hs, ht⟩ := hc.exists_of_isSubstring_append (h ▸ hu)
    obtain ⟨w, hw⟩ := hc.editor_of_isSubstring h hu
    rcases Classical.em (w = ∅) with rfl | hw'
    · left
      simp only [hx, hy, hs, ht, hc.append_empty, hc.empty_append] at hw
      and_intros
      · apply Model.ext
        rw [hx, hs]
        exact hw.elim And.left And.left
      · apply Model.ext
        rw [hy, ht]
        exact hw.elim And.right And.right
    · right
      use ⟨w, by simpa using hw'⟩
      exact hw.imp (And.imp Model.ext Model.ext) (And.imp Model.ext Model.ext)
  case concatNeZero =>
    suffices ∀ x y : nonemptyTranslation.Model M, x ++ y ≠ 0 by simpa [models_iff]
    exact fun x y h ↦ (eq_empty_of_append_isAtom <| Or.inl <| congrArg Model.val h).elim
      (nonempty x) (nonempty y)
  case concatNeOne =>
    suffices ∀ x y : nonemptyTranslation.Model M, x ++ y ≠ 1 by simpa [models_iff]
    exact fun x y h ↦ (eq_empty_of_append_isAtom <| Or.inr <| congrArg Model.val h).elim
      (nonempty x) (nonempty y)
  case zeroNeOne =>
    suffices (0 : nonemptyTranslation.Model M) ≠ 1 by simpa [models_iff]
    exact fun h ↦ WTCEmpty.zero_ne_one (M := M) <| congrArg Model.val h

end WTCEmpty

/--
$\mathsf{WTC}$ with the empty string interprets $\mathsf{WTC}$ on the nonempty strings.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖ₑ ⊳ 𝗪𝗧𝗖 where
  trln := WTCEmpty.nonemptyTranslation
  interpret_theory φ hφ := completeEmpty.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

namespace WTC

variable {M : Type} [ConcatenationStructure M] {w x y z : M}

/-- `w` is the only string that yields `y` after the letter $1$. -/
def IsDecode (w y : M) : Prop := y = 1 ++ w ∧ ∀ v, y = 1 ++ v → v = w

/-- `w` is the only string that yields `y` after the letter $1$. -/
def isDecode : Semisentence ℒ⌢ 2 :=
  “w y. y = !!(op(1).const) ⌢ w ∧ ∀ v, y = !!(op(1).const) ⌢ v → v = w”

@[simp]
lemma eval_isDecode : M ⊧/![w, y] isDecode ↔ IsDecode w y := by simp [isDecode, IsDecode]

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def IsCodeAppend (z x y : M) : Prop :=
  (y = 1 ∧ z = x) ∨ (∃ w, IsDecode w y ∧ z = x ++ w) ∨ (y ≠ 1 ∧ (∀ w, ¬IsDecode w y) ∧ z = 0)

/--
`z` is the code of the concatenation of the strings coded by `x` and `y`, or the letter $0$ if `y`
is not uniquely decoded.
- [HH14, Theorem 3]
-/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(1).const) ∧ z = x) ∨ (∃ w, !isDecode w y ∧ z = x ⌢ w) ∨
    (y ≠ !!(op(1).const) ∧ (∀ w, ¬!isDecode w y) ∧ z = !!(op(0).const))”

@[simp]
lemma eval_isCodeAppend : M ⊧/![z, x, y] isCodeAppend ↔ IsCodeAppend z x y := by
  simp [isCodeAppend, IsCodeAppend]

/-- The code of a possibly empty binary string: the string after the letter $1$. -/
def emptyCode (u : List Bool) : M := ofFreeSemigroup ⟨true, u⟩

@[simp]
lemma emptyCode_nil : (emptyCode [] : M) = 1 := rfl

section model

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

lemma not_isDecode_one : ¬IsDecode w (1 : M) := fun h ↦ append_ne_one _ _ h.1.symm

lemma existsUnique_isCodeAppend (x y : M) : ∃! z, IsCodeAppend z x y := by
  by_cases h₁ : y = 1
  · use x
    simp [IsCodeAppend, h₁, not_isDecode_one]
  by_cases h₂ : ∃ w, IsDecode w y
  · obtain ⟨w, hw⟩ := h₂
    have hw' (v : M) : IsDecode v y ↔ v = w :=
      ⟨fun h ↦ hw.2 v h.1, fun h ↦ h ▸ hw⟩
    use x ++ w
    simp [IsCodeAppend, h₁, hw']
  · use 0
    simp_all [IsCodeAppend]

lemma emptyCode_cons (b : Bool) (l : List Bool) :
    (emptyCode (b :: l) : M) = 1 ++ ofFreeSemigroup ⟨b, l⟩ :=
  ofFreeSemigroup_mul 1 ⟨b, l⟩

lemma isDecode_emptyCode (b : Bool) (l : List Bool) :
    IsDecode (ofFreeSemigroup ⟨b, l⟩ : M) (emptyCode (b :: l)) := by
  and_intros
  · exact emptyCode_cons b l
  · intro v h
    obtain ⟨p, q, hp, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
    obtain rfl : 1 = p := ofFreeSemigroup_injective hp
    have e := congrArg FreeSemigroup.toList e
    congr 1
    apply FreeSemigroup.toList_injective
    simpa [FreeSemigroup.toList, one_eq_of_true, FreeSemigroup.of] using e.symm

lemma isCodeAppend_emptyCode (u v : List Bool) :
    IsCodeAppend (emptyCode (u ++ v) : M) (emptyCode u) (emptyCode v) := by
  rcases v with _ | ⟨b, l⟩
  · left
    simp
  · right; left
    use ofFreeSemigroup ⟨b, l⟩
    exact ⟨isDecode_emptyCode b l, ofFreeSemigroup_mul ⟨true, u⟩ ⟨b, l⟩⟩

lemma exists_of_isCodeAppend_emptyCode {u : List Bool} (h : IsCodeAppend (emptyCode u) x y) :
    ∃ p q, x = emptyCode p ∧ y = emptyCode q := by
  rcases h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, -⟩, h⟩ | ⟨-, -, h⟩
  · use u, []
    simp
  · obtain ⟨⟨a, p⟩, ⟨b, q⟩, rfl, rfl, e⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
    obtain rfl : true = a := congrArg FreeSemigroup.head e
    use p, b :: q
    exact ⟨rfl, (emptyCode_cons b q).symm⟩
  · have e : (⟨true, u⟩ : FreeSemigroup Bool) = 0 := ofFreeSemigroup_injective (M := M) h
    exact absurd (congrArg FreeSemigroup.head e) (by simp [zero_eq_of_false, FreeSemigroup.of])

end model

/--
The translation of $\mathsf{WTC}$ with the empty string into $\mathsf{WTC}$ that codes a string by
the string itself after the letter $1$, and the empty string by the letter $1$.
- [HH14, Theorem 3]
-/
def emptyTranslation : DirectTranslation 𝗪𝗧𝗖 ℒ⌢ₑ where
  domain := ⟨“x. ⊤”⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isCodeAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(1).const)”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_isCodeAppend (e 0) (e 1)
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

lemma dom (x : M) : emptyTranslation.Dom x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

/-- The letters, the concatenation and the empty string coded in a model of $\mathsf{WTC}$. -/
noncomputable abbrev concatenationEmptyStructure :
    ConcatenationEmptyStructure (emptyTranslation.Model M) where
  zero := ⟨1 ++ 0, dom _⟩
  one := ⟨1 ++ 1, dom _⟩
  append x y := ⟨(existsUnique_isCodeAppend (x : M) y).choose, dom _⟩
  emptyCollection := ⟨1, dom _⟩

/--
The structure of the model of `emptyTranslation` is the standard one of
`concatenationEmptyStructure`.
-/
lemma struc_eq :
    Model.struc emptyTranslation M = @standardModelEmpty _ concatenationEmptyStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · rw [Matrix.fun_eq_vec_two fun i ↦ (v i : M)]
        exact eval_isCodeAppend.mpr (existsUnique_isCodeAppend (v 0 : M) (v 1)).choose_spec.1
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| Model.eq_iff v)

end emptyTranslation

/--
The strings of a model of $\mathsf{WTC}$ code a model of $\mathsf{WTC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] : (emptyTranslation.Model M)↓[ℒ⌢ₑ] ⊧* 𝗪𝗧𝗖ₑ := by
  rw [emptyTranslation.struc_eq]
  let := emptyTranslation.concatenationEmptyStructure (M := M)
  have isCodeAppend (x y : emptyTranslation.Model M) : IsCodeAppend ((x ++ y : _) : M) x y :=
    (existsUnique_isCodeAppend (x : M) y).choose_spec.1
  let c (u : List Bool) : emptyTranslation.Model M := ⟨emptyCode u, emptyTranslation.dom _⟩
  apply IsInitialEmptyEmbedding.models_WTCEmpty (c := c)
  constructor
  case injective =>
    intro u v h
    exact congrArg FreeSemigroup.tail <| ofFreeSemigroup_injective (congrArg Model.val h)
  case map_nil => rfl
  case map_false => rfl
  case map_true => rfl
  case map_append =>
    exact fun u v ↦ Model.ext <| (existsUnique_isCodeAppend _ _).unique
      (isCodeAppend_emptyCode u v) (isCodeAppend (c u) (c v))
  case exists_of_append_eq =>
    intro x y u h
    obtain ⟨p, q, hp, hq⟩ : ∃ p q, (x : M) = emptyCode p ∧ (y : M) = emptyCode q :=
      exists_of_isCodeAppend_emptyCode <| (congrArg Model.val h) ▸ isCodeAppend x y
    use p, q
    exact ⟨Model.ext hp, Model.ext hq⟩

end WTC

/--
$\mathsf{WTC}$ interprets $\mathsf{WTC}$ with the empty string.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖 ⊳ 𝗪𝗧𝗖ₑ where
  trln := WTC.emptyTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{WTC}$ and $\mathsf{WTC}$ with the empty string are mutually interpretable.
- [HH14, Theorem 3]
-/
instance : 𝗪𝗧𝗖 ⋈ 𝗪𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{WTC}$ with the empty string interprets $\mathsf{R}_0$.
- [HH14, Theorem 1]
- [Hor12, §4, Theorem 4.1]
-/
instance : 𝗪𝗧𝗖ₑ ⊳ 𝗥₀ :=
  DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀) (inferInstance : 𝗪𝗧𝗖ₑ ⊳ 𝗪𝗧𝗖)

/--
$\mathsf{WTC}$ with the empty string is essentially undecidable.
- [HH14, Theorem 1, Theorem 11]
- [Hor12, §4, Corollary 4.11]
-/
instance : 𝗪𝗧𝗖ₑ.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖ₑ ⊳ 𝗥₀)

/--
$\mathsf{WTC}$ with the empty string is undecidable.
- [HH14, Theorem 1]
-/
theorem WTCEmpty.undecidable : Entailment.Undecidable 𝗪𝗧𝗖ₑ :=
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖ₑ

end FFL.FirstOrder.Concatenation

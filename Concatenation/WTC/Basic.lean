module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Semantics.Basic

/-!
# The weak theories of concatenation

$\mathsf{WTC}$ without and with the empty string, and with arbitrary letters.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
Axioms of the weak theory of concatenation without the empty string.
- [HH14, Definition 5]
- [Mur22, §1]
-/
inductive IsWTCAxiom : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsWTCAxiom φ
  | concatAssoc (u : FreeSemigroup Bool) : IsWTCAxiom
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteral u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteral u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : FreeSemigroup Bool) : IsWTCAxiom
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteral u) →
      (x = s ∧ y = t) ∨ ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | concatNeZero : IsWTCAxiom “∀ x y, x ⌢ y ≠ !!(op(0).const)”
  | concatNeOne : IsWTCAxiom “∀ x y, x ⌢ y ≠ !!(op(1).const)”
  | zeroNeOne : IsWTCAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The weak theory of concatenation without the empty string.
- [HH14, Definition 5]
- [Mur22, §1]
-/
abbrev WTC : Theory ℒ⌢ := Set.ofPred IsWTCAxiom

@[inherit_doc]
notation "𝗪𝗧𝗖" => WTC

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗪𝗧𝗖 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCAxiom.equal φ hφ

/--
Axioms of the weak theory of concatenation with the empty string.
- [HH14, Definition 2]
-/
inductive IsWTCEmptyAxiom : Sentence ℒ⌢ₑ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢ₑ, IsWTCEmptyAxiom φ
  | emptyUnit (u : List Bool) : IsWTCEmptyAxiom
      “∀ x, !isSubstring x !!(biteralEmpty u) → x ⌢ ⋆ = x ∧ ⋆ ⌢ x = x”
  | concatAssoc (u : List Bool) : IsWTCEmptyAxiom
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(biteralEmpty u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(biteralEmpty u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : List Bool) : IsWTCEmptyAxiom
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(biteralEmpty u) →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | zeroNeEmpty : IsWTCEmptyAxiom “!!(op(0).const) ≠ ⋆”
  | zeroAtom : IsWTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(0).const) → x = ⋆ ∨ y = ⋆”
  | oneNeEmpty : IsWTCEmptyAxiom “!!(op(1).const) ≠ ⋆”
  | oneAtom : IsWTCEmptyAxiom “∀ x y, x ⌢ y = !!(op(1).const) → x = ⋆ ∨ y = ⋆”
  | zeroNeOne : IsWTCEmptyAxiom “!!(op(0).const) ≠ !!(op(1).const)”

/--
The weak theory of concatenation with the empty string.
- [HH14, Definition 2]
-/
abbrev WTCEmpty : Theory ℒ⌢ₑ := Set.ofPred IsWTCEmptyAxiom

@[inherit_doc]
notation "𝗪𝗧𝗖ₑ" => WTCEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ 𝗪𝗧𝗖ₑ := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCEmptyAxiom.equal φ hφ

section letters

open DirectTranslation LetterStructure

variable {α : Type}

/--
Axioms of the weak theory of concatenation with the letters `α`, without the empty string.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
inductive IsWTCLettersAxiom (α : Type) : Sentence ℒ⌢[α] → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢[α], IsWTCLettersAxiom α φ
  | concatAssoc (u : FreeSemigroup α) : IsWTCLettersAxiom α
      “∀ x y z, !isSubstring ((x ⌢ y) ⌢ z) !!(stringTerm letterTerm u) ∨
      !isSubstring (x ⌢ (y ⌢ z)) !!(stringTerm letterTerm u) → (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”
  | editor (u : FreeSemigroup α) : IsWTCLettersAxiom α
      “∀ x y s t, x ⌢ y = s ⌢ t ∧ !isSubstring (x ⌢ y) !!(stringTerm letterTerm u) →
      (x = s ∧ y = t) ∨ ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”
  | concatNeLetter (a : α) : IsWTCLettersAxiom α “∀ x y, x ⌢ y ≠ !!(letterTerm a)”
  | letterNeLetter (a b : α) (h : a ≠ b) :
      IsWTCLettersAxiom α “!!(letterTerm a) ≠ !!(letterTerm b)”

/--
The weak theory of concatenation with the letters `α`, without the empty string: for
$\mathsf{WTC}_n$, the letters are `Fin n`.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
abbrev WTCLetters (α : Type) : Theory ℒ⌢[α] := Set.ofPred (IsWTCLettersAxiom α)

@[inherit_doc]
notation "𝗪𝗧𝗖[" α "]" => WTCLetters α

instance : 𝗘𝗤 ℒ⌢[α] ⪯ 𝗪𝗧𝗖[α] :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWTCLettersAxiom.equal φ hφ

section reduct

variable {M : Type*} [Nonempty M] [LetterStructure α M] [M↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α]] {a b : α}

omit [Nonempty M] [M↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α]] in
lemma ofFreeSemigroup_concatenationStructure (u : FreeSemigroup Bool) :
    let := concatenationStructure (M := M) a b
    (ConcatenationStructure.ofFreeSemigroup u : M) =
      stringValue ofLetter ⟨if u.head then b else a, u.tail.map fun i ↦ if i then b else a⟩ := by
  simp only [ConcatenationStructure.ofFreeSemigroup, stringValue, List.foldl_map,
    apply_ite ofLetter]
  rfl

/-- Two letters of a model of `𝗪𝗧𝗖[α]` give a model of $\mathsf{WTC}$. -/
lemma models_WTC_concatenationStructure (h : a ≠ b) :
    let := concatenationStructure (M := M) a b
    M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  intro c
  constructor
  intro σ hσ
  cases hσ
  case equal hφ =>
    have : M↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc u =>
    have := Theory.models M 𝗪𝗧𝗖[α] <| IsWTCLettersAxiom.concatAssoc
      ⟨if u.head then b else a, u.tail.map fun i ↦ if i then b else a⟩
    simpa [models_iff, ofFreeSemigroup_concatenationStructure] using this
  case editor u =>
    have := Theory.models M 𝗪𝗧𝗖[α] <| IsWTCLettersAxiom.editor
      ⟨if u.head then b else a, u.tail.map fun i ↦ if i then b else a⟩
    simpa [models_iff, ofFreeSemigroup_concatenationStructure] using this
  case concatNeZero =>
    simpa [models_iff] using! Theory.models M 𝗪𝗧𝗖[α] <| IsWTCLettersAxiom.concatNeLetter a
  case concatNeOne =>
    simpa [models_iff] using! Theory.models M 𝗪𝗧𝗖[α] <| IsWTCLettersAxiom.concatNeLetter b
  case zeroNeOne =>
    simpa [models_iff] using! Theory.models M 𝗪𝗧𝗖[α] <| IsWTCLettersAxiom.letterNeLetter a b h

end reduct

/-- The translation of the two letters $0$ and $1$ to the letters `a` and `b`. -/
def lettersTranslation (a b : α) : DirectTranslation 𝗪𝗧𝗖[α] ℒ⌢ where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .zero => ⟨“z. z = !!(letterTerm a)”⟩
    | .one => ⟨“z. z = !!(letterTerm b)”⟩
    | .concat => ⟨“z x y. z = x ⌢ y”⟩
  domain_nonempty := completeLetters.{0} _ _ fun M _ _ _ ↦
    (models_domainNonempty_iff _).mpr <| by simp [Semiformula.Operator.val]
  func_defined f := completeLetters.{0} _ _ fun M _ _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f <;> simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := completeLetters.{0} _ _ fun M _ _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

namespace lettersTranslation

variable {M : Type*} [LetterStructure α M] {a b : α}

/-- The domain of the translation is the whole model. -/
def equiv : M ≃ (lettersTranslation a b).Model M where
  toFun x := ⟨x, by simp [dom_iff, lettersTranslation, Semiformula.Operator.val]⟩
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

variable [Nonempty M] [M↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α]]

/-- The structure of the model of `lettersTranslation` is the one the letters `a` and `b` give. -/
lemma struc_eq : Model.struc (lettersTranslation a b) M =
    @Tarski.Structure.ofEquiv ℒ⌢ M (@standardModel M (concatenationStructure a b)) _ equiv :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [lettersTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| (Model.eq_iff v).trans Model.ext_iff)

/-- The model of `lettersTranslation` satisfies $\mathsf{WTC}$. -/
lemma models_WTC (h : a ≠ b) : ((lettersTranslation a b).Model M)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  rw [struc_eq]
  let := concatenationStructure (M := M) a b
  let := @Tarski.Structure.ofEquiv ℒ⌢ M _ _ (equiv (M := M) (a := a) (b := b))
  have := Tarski.Structure.ElementaryEquiv.ofEquiv (L := ℒ⌢) (equiv (M := M) (a := a) (b := b))
  exact Tarski.Structure.ElementaryEquiv.modelsTheory.mp <|
    models_WTC_concatenationStructure (M := M) h

end lettersTranslation

/--
The weak theory of concatenation with at least two letters interprets $\mathsf{WTC}$.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
abbrev WTCLetters.interpretsWTC {a b : α} (h : a ≠ b) : 𝗪𝗧𝗖[α] ⊳ 𝗪𝗧𝗖 where
  trln := lettersTranslation a b
  interpret_theory φ hφ := completeLetters.{0} _ _ fun _ _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp (lettersTranslation.models_WTC h) φ hφ

/--
The weak theory of concatenation with at least two letters interprets $\mathsf{WTC}$.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance [Nontrivial α] : 𝗪𝗧𝗖[α] ⊳ 𝗪𝗧𝗖 :=
  WTCLetters.interpretsWTC (exists_pair_ne α).choose_spec.choose_spec

end letters

end FFL.FirstOrder.Concatenation

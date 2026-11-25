module

public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Concatenation.ToMathlib.FreeSemigroupCode
public import Concatenation.WTC.Letters

/-!
# $\mathsf{R}_0$ interprets $\mathsf{WTC}$

The strings are coded by numerals, and the concatenation is restricted by Cobham's order.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open LetterStructure

section initial

variable {α : Type} {M : Type*} [LetterStructure α M]

/--
`c` embeds the nonempty strings onto an initial part of `M`: if a concatenation is a standard
string, then so are its arguments.
-/
structure IsInitialEmbedding (c : FreeSemigroup α → M) : Prop where
  injective : Function.Injective c
  map_letter (a : α) : c (FreeSemigroup.of a) = ofLetter a
  map_append (u v : FreeSemigroup α) : c (u ++ v) = c u ++ c v
  exists_of_append_eq {x y : M} {w : FreeSemigroup α} (h : x ++ y = c w) :
    ∃ u v, x = c u ∧ y = c v

namespace IsInitialEmbedding

variable {c : FreeSemigroup α → M} (hc : IsInitialEmbedding c) {x y : M} {w : FreeSemigroup α}
include hc

lemma stringValue_eq (w : FreeSemigroup α) : stringValue ofLetter w = c w := by
  suffices ∀ (l : List α) (u : FreeSemigroup α),
      l.foldl (fun m a ↦ m ++ ofLetter a) (c u) = c ⟨u.head, u.tail ++ l⟩ by
    simpa [stringValue, hc.map_letter] using this w.tail (FreeSemigroup.of w.head)
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro u
    rw [List.foldl_cons, ← hc.map_letter, ← hc.map_append, ih]
    simp [FreeSemigroup.of, append_eq_mul, HMul.hMul, Mul.mul]

lemma exists_of_isSubstring (h : IsSubstring x (c w)) : ∃ u, x = c u := by
  rcases h with rfl | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · use w
  · obtain ⟨-, b, -, rfl⟩ := hc.exists_of_append_eq h.symm
    use b
  · obtain ⟨a, -, rfl, -⟩ := hc.exists_of_append_eq h.symm
    use a
  · obtain ⟨a, -, ha, -⟩ := hc.exists_of_append_eq h.symm
    obtain ⟨-, b, -, rfl⟩ := hc.exists_of_append_eq ha
    use b
  · obtain ⟨-, b, -, hb⟩ := hc.exists_of_append_eq h.symm
    obtain ⟨a, -, rfl, -⟩ := hc.exists_of_append_eq hb
    use a

lemma exists_of_isSubstring_append (h : IsSubstring (x ++ y) (c w)) :
    ∃ u v, x = c u ∧ y = c v := by
  obtain ⟨w', hw'⟩ := hc.exists_of_isSubstring h
  exact hc.exists_of_append_eq hw'

lemma append_assoc_of_isSubstring {z : M}
    (h : IsSubstring (x ++ y ++ z) (c w) ∨ IsSubstring (x ++ (y ++ z)) (c w)) :
    x ++ y ++ z = x ++ (y ++ z) := by
  obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, x = c u ∧ y = c v ∧ z = c w := by
    rcases h with h | h
    · obtain ⟨a, e, ha, rfl⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use u, v, e
    · obtain ⟨u, a, rfl, ha⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨v, e, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use u, v, e
  simp only [← hc.map_append, append_eq_mul, mul_assoc]

lemma editor_of_isSubstring {s t : M} (h : x ++ y = s ++ t) (hw : IsSubstring (x ++ y) (c w)) :
    (x = s ∧ y = t) ∨ ∃ u, (x ++ u = s ∧ y = u ++ t) ∨ (x = s ++ u ∧ u ++ y = t) := by
  obtain ⟨a, b, rfl, rfl⟩ := hc.exists_of_isSubstring_append hw
  obtain ⟨d, e, rfl, rfl⟩ := hc.exists_of_append_eq (h.symm.trans (hc.map_append a b).symm)
  rw [← hc.map_append, ← hc.map_append, hc.injective.eq_iff] at h
  rcases FreeSemigroup.mul_eq_mul_iff.mp h with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp
  · right
    use c u
    simp [← hc.map_append]
  · right
    use c u
    simp [← hc.map_append]

lemma append_ne_letter (a : α) : x ++ y ≠ ofLetter a := by
  rw [← hc.map_letter]
  intro h
  obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq h
  rw [← hc.map_append, hc.injective.eq_iff] at h
  exact FreeSemigroup.of_ne_mul a u v h.symm

/-- A structure with an initial embedding of the nonempty strings is a model of `𝗪𝗧𝗖[α]`. -/
theorem models_WTCLetters [Nonempty M] : M↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : M↓[ℒ⌢[α]] ⊧* 𝗘𝗤 ℒ⌢[α] := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc w =>
    simpa [models_iff, hc.stringValue_eq]
      using fun x y z : M ↦ hc.append_assoc_of_isSubstring (x := x) (y := y) (z := z) (w := w)
  case editor w =>
    simpa [models_iff, hc.stringValue_eq]
      using fun x y s t : M ↦ hc.editor_of_isSubstring (x := x) (y := y) (s := s) (t := t) (w := w)
  case concatNeLetter a =>
    simpa [models_iff] using fun x y : M ↦ hc.append_ne_letter (x := x) (y := y) a
  case letterNeLetter a b h =>
    simpa [models_iff, ← hc.map_letter, hc.injective.eq_iff, FreeSemigroup.of] using h⟩

end IsInitialEmbedding

end initial

open DirectTranslation ORingStructure Arithmetic Arithmetic.R0

variable (α : Type) [Primcodable α]

/-- The formula that represents the concatenation of codes on numerals. -/
noncomputable abbrev mulCodeRepresentation : ArithmeticSemisentence 3 :=
  cobhamRepresentation₂ (FreeSemigroup.mulCode α)

variable {M : Type*} [ORingStructure M] {x y z : M}

/--
`z` is the only value of `mulCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
@[mk_iff]
structure IsConcat (x y z : M) : Prop where
  left_le : x ⊴ z
  right_le : y ⊴ z
  eval : M ⊧/![x, y, z] (mulCodeRepresentation α)
  unique (w : M) (hw : M ⊧/![x, y, w] (mulCodeRepresentation α)) : w = z

/--
`z` is the only value of `mulCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
noncomputable def isConcat : ArithmeticSemisentence 3 :=
  “x y z. !cobhamLE x z ∧ !cobhamLE y z ∧ !(mulCodeRepresentation α) x y z ∧
    ∀ w, !(mulCodeRepresentation α) x y w → w = z”

@[simp]
lemma eval_isConcat : M ⊧/![x, y, z] (isConcat α) ↔ IsConcat α x y z := by
  simp [isConcat, isConcat_iff]

/-- `z` is the concatenation of `x` and `y`: `IsConcat α x y z`, or `z` is `0` if there is none. -/
def ConcatGraph (z x y : M) : Prop := IsConcat α x y z ∨ (z = 0 ∧ ∀ w, ¬IsConcat α x y w)

/-- `z` is the concatenation of `x` and `y`: `IsConcat α x y z`, or `z` is `0` if there is none. -/
noncomputable def concatGraph : ArithmeticSemisentence 3 :=
  “z x y. !(isConcat α) x y z ∨ (z = 0 ∧ ∀ w, ¬!(isConcat α) x y w)”

@[simp]
lemma eval_concatGraph : M ⊧/![z, x, y] (concatGraph α) ↔ ConcatGraph α z x y := by
  simp [concatGraph, ConcatGraph]

variable {α}

lemma IsConcat.eq {w : M} (hz : IsConcat α x y z) (hw : IsConcat α x y w) : z = w :=
  hw.unique z hz.eval

variable (α) in
lemma existsUnique_concatGraph (x y : M) : ∃! z, ConcatGraph α z x y := by
  by_cases h : ∃ z, IsConcat α x y z
  · obtain ⟨z, hz⟩ := h
    use z
    and_intros
    · exact Or.inl hz
    · rintro w (hw | ⟨-, hw⟩)
      · exact hw.eq hz
      · exact absurd hz (hw z)
  · push Not at h
    use 0
    and_intros
    · exact Or.inr ⟨rfl, h⟩
    · rintro w (hw | ⟨rfl, -⟩)
      · exact absurd hw (h w)
      · rfl

section R0

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma isConcat_numeral (u v : FreeSemigroup α) :
    IsConcat α (numeral u.code : M) (numeral v.code) (numeral (u * v).code) where
  left_le := by simpa using u.code_le_code_mul_left v
  right_le := by simpa using u.code_le_code_mul_right v
  eval := by simp [FreeSemigroup.primrec₂_mulCode.to_comp]
  unique := by simp [FreeSemigroup.primrec₂_mulCode.to_comp]

lemma IsConcat.exists_of_numeral {w : FreeSemigroup α} (h : IsConcat α x y (numeral w.code)) :
    ∃ u v : FreeSemigroup α, x = numeral u.code ∧ y = numeral v.code := by
  obtain ⟨m, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.left_le
  obtain ⟨n, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.right_le
  have := (eval_cobhamRepresentation₂_numeral_iff FreeSemigroup.primrec₂_mulCode.to_comp m n).mp
    h.eval
  rw [numeral_inj_iff] at this
  obtain ⟨u, v, rfl, rfl⟩ := FreeSemigroup.eq_code_of_mulCode_ne_zero (this ▸ w.code_ne_zero)
  use u, v

lemma ConcatGraph.exists_of_numeral {w : FreeSemigroup α}
    (h : ConcatGraph α (numeral w.code) x y) :
    ∃ u v : FreeSemigroup α, x = numeral u.code ∧ y = numeral v.code := by
  rcases h with h | ⟨h, -⟩
  · exact h.exists_of_numeral
  · have : w.code = 0 := numeral_inj_iff (M := M).mp <| by simpa using h
    exact absurd this w.code_ne_zero

end R0

variable (α) in
/--
The translation of the language of concatenation with the letters `α` into $\mathsf{R}_0$: a
nonempty string is the numeral of its code.
-/
noncomputable def codeTranslation : DirectTranslation 𝗥₀ ℒ⌢[α] where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .letter a => ⟨“z. z = ↑(FreeSemigroup.code (FreeSemigroup.of a))”⟩
    | .concat => ⟨concatGraph α⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_concatGraph α (e 0) (e 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma codeTranslation_dom (x : M) : (codeTranslation α).Dom x := by
  simp [dom_iff, codeTranslation, Semiformula.Operator.val]

namespace codeTranslation

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

/-- The numeral of the code of a nonempty string. -/
def ofString (u : FreeSemigroup α) : (codeTranslation α).Model M := ⟨numeral u.code, by simp⟩

/-- The letters and the concatenation of the codes in `M`. -/
noncomputable abbrev letterStructure : LetterStructure α ((codeTranslation α).Model M) where
  ofLetter a := ofString (FreeSemigroup.of a)
  append x y := Tarski.Structure.func (L := ℒ⌢[α]) .concat ![x, y]

/-- The structure of the model of `codeTranslation` is the one of `letterStructure`. -/
lemma struc_eq : Model.struc (codeTranslation α) M = @lettersModel α _ letterStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [codeTranslation, Semiformula.Operator.val]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] letterStructure

lemma append_eq_iff {x y z : (codeTranslation α).Model M} :
    x ++ y = z ↔ ConcatGraph α (z : M) x y := by
  have := Model.func_iff (π := codeTranslation α) (M := M) (f := .concat) (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → (codeTranslation α).Model M) i : M)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_concatGraph] at this
  exact eq_comm.trans this

/-- The strings are embedded onto an initial part of the model of `codeTranslation`. -/
lemma isInitialEmbedding_ofString :
    IsInitialEmbedding (ofString : FreeSemigroup α → (codeTranslation α).Model M) where
  injective u v h := by simpa [ofString] using h
  map_letter _ := rfl
  map_append u v := (append_eq_iff.mpr <| Or.inl <| isConcat_numeral u v).symm
  exists_of_append_eq h := by
    obtain ⟨u, v, hu, hv⟩ := (append_eq_iff.mp h).exists_of_numeral
    use u, v
    exact ⟨Model.ext hu, Model.ext hv⟩

end

/-- The model of `codeTranslation` satisfies `𝗪𝗧𝗖[α]`. -/
instance : ((codeTranslation α).Model M)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := by
  rw [struc_eq]
  let := letterStructure (α := α) (M := M)
  exact isInitialEmbedding_ofString.models_WTCLetters

end codeTranslation

/--
$\mathsf{R}_0$ interprets the weak theory of concatenation with the letters `α`.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗧𝗖[α] where
  trln := codeTranslation α
  interpret_theory φ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{R}_0$ interprets $\mathsf{WTC}$.
- [Hor11, §3, Theorem 3.9]
-/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗧𝗖 :=
  DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖[Bool] ⊳ 𝗪𝗧𝗖) inferInstance

end FFL.FirstOrder.Concatenation

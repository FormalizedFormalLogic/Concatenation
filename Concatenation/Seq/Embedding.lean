module

public import Concatenation.Seq.Arithmetic
public import Concatenation.ToFoundation.Arithmetic.R
public import Concatenation.ToFoundation.Arithmetic.R0.Representation

/-!
# $\mathsf{R}_0$ interprets $\mathsf{WSeq}$

The sequences are coded by numerals, and the concatenation is restricted by Cobham's order.
Hence $\mathsf{WSeq}$ and $\mathsf{R}$ are mutually interpretable.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace FiniteSequence

open Encodable Denumerable

/-- The code of a sequence. -/
def code : FiniteSequence → ℕ
  | nil => 0
  | .snoc s t => Nat.pair t.code s.code + 1

lemma code_injective : Function.Injective code := by
  intro s
  induction s with
  | nil => rintro (_ | _) <;> simp [code]
  | snoc s t hs ht =>
    rintro (_ | ⟨s', t'⟩)
    · simp [code]
    · simp only [code, Nat.add_right_cancel_iff, Nat.pair_eq_pair, snoc.injEq, and_imp]
      exact fun h₁ h₂ ↦ ⟨hs h₂, ht h₁⟩

@[simp]
lemma code_inj {s t : FiniteSequence} : s.code = t.code ↔ s = t := code_injective.eq_iff

lemma code_surjective : Function.Surjective code := by
  intro n
  induction n using Nat.strongRec with
  | ind n ih =>
    rcases n with _ | n
    · use nil
      rfl
    · obtain ⟨t, ht⟩ := ih _ <| Nat.lt_succ_of_le n.unpair_left_le
      obtain ⟨s, hs⟩ := ih _ <| Nat.lt_succ_of_le n.unpair_right_le
      use s.snoc t
      simp [code, hs, ht]

lemma code_le_code_append_left (s t : FiniteSequence) : s.code ≤ (s ++ t).code := by
  induction t with
  | nil => simp
  | snoc t u ht =>
    rw [append_snoc, code]
    exact ht.trans <| (Nat.right_le_pair _ _).trans <| Nat.le_succ _

lemma code_le_code_append_right (s t : FiniteSequence) : t.code ≤ (s ++ t).code := by
  induction t with
  | nil => simp [code]
  | snoc t u ht =>
    rw [append_snoc, code, code, Nat.add_le_add_iff_right]
    rcases ht.eq_or_lt with h | h
    · rw [h]
    · exact (Nat.pair_lt_pair_right _ h).le

/-- The code of the concatenation of the sequences coded by `m` and `n`. -/
def appendCode (m n : ℕ) : ℕ := encode (ofNat (List ℕ) n ++ ofNat (List ℕ) m)

@[simp]
lemma appendCode_code (s t : FiniteSequence) : appendCode s.code t.code = (s ++ t).code := by
  induction t with
  | nil => simp [appendCode, code]
  | snoc t u ht => simpa [appendCode, code] using ht

lemma primrec₂_appendCode : Primrec₂ appendCode :=
  Primrec.encode.comp <| Primrec.list_append.comp ((Primrec.ofNat _).comp Primrec.snd)
    ((Primrec.ofNat _).comp Primrec.fst)

end FiniteSequence

namespace Sequence

open DirectTranslation FiniteSequence ORingStructure Arithmetic Arithmetic.R0

variable {M : Type*} [ORingStructure M] {x y z : M}

/-- `z` is $\langle y, x \rangle + 1$, in the pairing `Nat.pair`. -/
def SnocGraph (z x y : M) : Prop :=
  (y < x ∧ z = x * x + y + 1) ∨ (¬y < x ∧ z = y * y + y + x + 1)

/-- `z` is $\langle y, x \rangle + 1$, in the pairing `Nat.pair`. -/
def snocGraph : ArithmeticSemisentence 3 :=
  “z x y. (y < x ∧ z = x * x + y + 1) ∨ (¬y < x ∧ z = y * y + y + x + 1)”

@[simp]
lemma eval_snocGraph : M ⊧/![z, x, y] snocGraph ↔ SnocGraph z x y := by
  simp [snocGraph, SnocGraph]

lemma existsUnique_snocGraph (x y : M) : ∃! z, SnocGraph z x y := by
  by_cases h : y < x
  · use x * x + y + 1
    simp [SnocGraph, h]
  · use y * y + y + x + 1
    simp [SnocGraph, h]

/-- The formula that represents the concatenation of codes on numerals. -/
noncomputable abbrev appendCodeRepresentation : ArithmeticSemisentence 3 :=
  cobhamRepresentation₂ appendCode

/--
`z` is the only value of `appendCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z`
in Cobham's order.
-/
@[mk_iff]
structure IsConcat (x y z : M) : Prop where
  left_le : x ⊴ z
  right_le : y ⊴ z
  eval : M ⊧/![x, y, z] appendCodeRepresentation
  unique (w : M) (hw : M ⊧/![x, y, w] appendCodeRepresentation) : w = z

/--
`z` is the only value of `appendCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z`
in Cobham's order.
-/
noncomputable def isConcat : ArithmeticSemisentence 3 :=
  “x y z. !cobhamLE x z ∧ !cobhamLE y z ∧ !appendCodeRepresentation x y z ∧
    ∀ w, !appendCodeRepresentation x y w → w = z”

@[simp]
lemma eval_isConcat : M ⊧/![x, y, z] isConcat ↔ IsConcat x y z := by
  simp [isConcat, isConcat_iff]

/-- `z` is the concatenation of `x` and `y`: `IsConcat x y z`, or `z` is `x` if there is none. -/
def ConcatGraph (z x y : M) : Prop := IsConcat x y z ∨ (z = x ∧ ∀ w, ¬IsConcat x y w)

/-- `z` is the concatenation of `x` and `y`: `IsConcat x y z`, or `z` is `x` if there is none. -/
noncomputable def concatGraph : ArithmeticSemisentence 3 :=
  “z x y. !isConcat x y z ∨ (z = x ∧ ∀ w, ¬!isConcat x y w)”

@[simp]
lemma eval_concatGraph : M ⊧/![z, x, y] concatGraph ↔ ConcatGraph z x y := by
  simp [concatGraph, ConcatGraph]

lemma existsUnique_concatGraph (x y : M) : ∃! z, ConcatGraph z x y := by
  by_cases h : ∃ z, IsConcat x y z
  · obtain ⟨z, hz⟩ := h
    use z
    and_intros
    · exact Or.inl hz
    · rintro w (hw | ⟨-, hw⟩)
      · exact hz.unique w hw.eval
      · exact absurd hz (hw z)
  · push Not at h
    use x
    and_intros
    · exact Or.inr ⟨rfl, h⟩
    · rintro w (hw | ⟨rfl, -⟩)
      · exact absurd hw (h w)
      · rfl

/--
The translation of the language of sequences into $\mathsf{R}_0$: a sequence is the numeral of its
code.
-/
noncomputable def codeTranslation : DirectTranslation 𝗥₀ ℒ⊢ where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .empty => ⟨“z. z = 0”⟩
    | .snoc => ⟨snocGraph⟩
    | .concat => ⟨concatGraph⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_snocGraph (e 0) (e 1)
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_concatGraph (e 0) (e 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma codeTranslation_dom (x : M) : codeTranslation.Dom x := by
  simp [dom_iff, codeTranslation, Semiformula.Operator.val]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma snocGraph_numeral (s t : FiniteSequence) :
    SnocGraph (numeral (s.snoc t).code : M) (numeral s.code) (numeral t.code) := by
  by_cases h : t.code < s.code
  · simp [SnocGraph, FiniteSequence.code, Nat.pair, h, numeral_mul_numeral, numeral_add_numeral,
      R0.numeral_add_one]
  · simp [SnocGraph, FiniteSequence.code, Nat.pair, h, numeral_mul_numeral, numeral_add_numeral,
      R0.numeral_add_one]

lemma isConcat_numeral (s t : FiniteSequence) :
    IsConcat (numeral s.code : M) (numeral t.code) (numeral (s ++ t).code) where
  left_le := by simpa using s.code_le_code_append_left t
  right_le := by simpa using s.code_le_code_append_right t
  eval := by simp [primrec₂_appendCode.to_comp]
  unique := by simp [primrec₂_appendCode.to_comp]

lemma ConcatGraph.exists_of_numeral {s : FiniteSequence}
    (h : ConcatGraph (numeral s.code) x y) : ∃ u, u ◨ s ∧ x = numeral u.code := by
  rcases h with h | ⟨rfl, -⟩
  · obtain ⟨m, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.left_le
    obtain ⟨n, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.right_le
    obtain ⟨u, rfl⟩ := code_surjective m
    obtain ⟨v, rfl⟩ := code_surjective n
    use u
    and_intros
    · use v
      simpa [primrec₂_appendCode.to_comp, eq_comm] using h.eval
    · rfl
  · use s
    and_intros
    · use nil
      rfl
    · rfl

namespace codeTranslation

/-- The numeral of the code of a sequence. -/
def ofSequence (s : FiniteSequence) : codeTranslation.Model M := ⟨numeral s.code, by simp⟩

/-- The empty sequence and the operations on codes in `M`. -/
noncomputable abbrev sequenceStructure : SequenceStructure (codeTranslation.Model M) where
  emptyCollection := ofSequence .nil
  snoc x y := Tarski.Structure.func (L := ℒ⊢) Language.Sequence.Func.snoc ![x, y]
  append x y := Tarski.Structure.func (L := ℒ⊢) Language.Sequence.Func.concat ![x, y]

/-- The structure of the model of `codeTranslation` is the one of `sequenceStructure`. -/
lemma struc_eq : Model.struc codeTranslation M = @standardModel _ sequenceStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [codeTranslation, Semiformula.Operator.val]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] sequenceStructure

variable {x y z : codeTranslation.Model M}

lemma snoc_eq_iff : SequenceStructure.snoc x y = z ↔ SnocGraph (z : M) x y := by
  have := Model.func_iff (π := codeTranslation) (M := M) (f := Language.Sequence.Func.snoc)
    (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → codeTranslation.Model M) i : M)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_snocGraph] at this
  exact eq_comm.trans this

lemma append_eq_iff : x ++ y = z ↔ ConcatGraph (z : M) x y := by
  have := Model.func_iff (π := codeTranslation) (M := M) (f := Language.Sequence.Func.concat)
    (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → codeTranslation.Model M) i : M)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_concatGraph] at this
  exact eq_comm.trans this

/-- The sequences are embedded onto an initial part of the model of `codeTranslation`. -/
lemma isInitialEmbedding_ofSequence :
    IsInitialEmbedding (ofSequence : FiniteSequence → codeTranslation.Model M) where
  injective s t h := by simpa [ofSequence] using h
  map_nil := rfl
  map_snoc s t := (snoc_eq_iff.mpr <| snocGraph_numeral s t).symm
  map_append s t := (append_eq_iff.mpr <| Or.inl <| isConcat_numeral s t).symm
  exists_of_isPrefix := by
    rintro x s ⟨y, h⟩
    obtain ⟨u, hu, hx⟩ := (append_eq_iff.mp h).exists_of_numeral
    exact ⟨u, hu, Model.ext hx⟩

end

/-- The model of `codeTranslation` satisfies $\mathsf{WSeq}$. -/
instance : (codeTranslation.Model M)↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾 := by
  rw [struc_eq]
  let := sequenceStructure (M := M)
  exact isInitialEmbedding_ofSequence.models_WSeq

end codeTranslation

end Sequence

/-- $\mathsf{R}_0$ interprets $\mathsf{WSeq}$. -/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗦𝗲𝗾 where
  trln := Sequence.codeTranslation
  interpret_theory φ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{WSeq}$ and $\mathsf{R}$ are mutually interpretable.
- [KM24, §2]
-/
noncomputable instance : 𝗪𝗦𝗲𝗾 ⋈ 𝗥 :=
  MutualDirectInterpretation.trans (T₂ := 𝗥₀) ⟨inferInstance, inferInstance⟩ inferInstance

end FFL.FirstOrder

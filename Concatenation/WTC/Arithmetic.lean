module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Semantics.Standard
public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Concatenation.ToMathlib.FreeSemigroupCode
public import Concatenation.WTC.Basic

/-!
# $\mathsf{R}_0$ interprets $\mathsf{WTC}$

The binary strings are coded by numerals, and the concatenation is restricted by Cobham's order.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section initial

variable {M : Type*} [ConcatenationStructure M]

/--
`c` embeds the nonempty binary strings onto an initial part of `M`: if a concatenation is a
standard string, then so are its arguments.
-/
structure IsInitialEmbedding (c : FreeSemigroup Bool → M) : Prop where
  injective : Function.Injective c
  map_zero : c 0 = 0
  map_one : c 1 = 1
  map_append (u v : FreeSemigroup Bool) : c (u ++ v) = c u ++ c v
  exists_of_append_eq {x y : M} {w : FreeSemigroup Bool} (h : x ++ y = c w) :
    ∃ u v, x = c u ∧ y = c v

namespace IsInitialEmbedding

variable {c : FreeSemigroup Bool → M} (hc : IsInitialEmbedding c) {x y : M}
  {w : FreeSemigroup Bool}
include hc

lemma ofFreeSemigroup_eq (w : FreeSemigroup Bool) :
    ConcatenationStructure.ofFreeSemigroup w = c w := by
  have hb (b : Bool) : c (FreeSemigroup.of b) = if b then 1 else 0 := by
    cases b
    · exact hc.map_zero
    · exact hc.map_one
  suffices ∀ (l : List Bool) (u : FreeSemigroup Bool),
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (c u) = c ⟨u.head, u.tail ++ l⟩ by
    simpa [ConcatenationStructure.ofFreeSemigroup, hb]
      using this w.tail (FreeSemigroup.of w.head)
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro u
    rw [List.foldl_cons, ← hb, ← hc.map_append, ih]
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

lemma append_ne_of (b : Bool) : x ++ y ≠ c (FreeSemigroup.of b) := by
  intro h
  obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq h
  rw [← hc.map_append, hc.injective.eq_iff] at h
  exact FreeSemigroup.of_ne_mul b u v h.symm

/--
A structure with an initial embedding of the nonempty binary strings is a model of
$\mathsf{WTC}$.
-/
theorem models_WTC : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : M↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc w =>
    simpa [models_iff, hc.ofFreeSemigroup_eq]
      using fun x y z : M ↦ hc.append_assoc_of_isSubstring (x := x) (y := y) (z := z) (w := w)
  case editor w =>
    simpa [models_iff, hc.ofFreeSemigroup_eq]
      using fun x y s t : M ↦ hc.editor_of_isSubstring (x := x) (y := y) (s := s) (t := t) (w := w)
  case concatNeZero =>
    simpa [models_iff] using fun x y : M ↦ hc.map_zero ▸ hc.append_ne_of (x := x) (y := y) false
  case concatNeOne =>
    simpa [models_iff] using fun x y : M ↦ hc.map_one ▸ hc.append_ne_of (x := x) (y := y) true
  case zeroNeOne =>
    simp [models_iff, ← hc.map_zero, ← hc.map_one, hc.injective.eq_iff]⟩

end IsInitialEmbedding

end initial

open DirectTranslation ORingStructure Arithmetic Arithmetic.R0

variable {M : Type*} [ORingStructure M] {x y z : M}

/-- The formula that represents the concatenation of codes on numerals. -/
noncomputable abbrev mulCodeRepresentation : ArithmeticSemisentence 3 :=
  cobhamRepresentation₂ (FreeSemigroup.mulCode Bool)

/--
`z` is the only value of `mulCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
@[mk_iff]
structure IsConcat (x y z : M) : Prop where
  left_le : x ⊴ z
  right_le : y ⊴ z
  eval : M ⊧/![x, y, z] mulCodeRepresentation
  unique (w : M) (hw : M ⊧/![x, y, w] mulCodeRepresentation) : w = z

/--
`z` is the only value of `mulCodeRepresentation` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
noncomputable def isConcat : ArithmeticSemisentence 3 :=
  “x y z. !cobhamLE x z ∧ !cobhamLE y z ∧ !mulCodeRepresentation x y z ∧
    ∀ w, !mulCodeRepresentation x y w → w = z”

@[simp]
lemma eval_isConcat : M ⊧/![x, y, z] isConcat ↔ IsConcat x y z := by
  simp [isConcat, isConcat_iff]

/-- `z` is the concatenation of `x` and `y`: `IsConcat x y z`, or `z` is `0` if there is none. -/
def ConcatGraph (z x y : M) : Prop := IsConcat x y z ∨ (z = 0 ∧ ∀ w, ¬IsConcat x y w)

/-- `z` is the concatenation of `x` and `y`: `IsConcat x y z`, or `z` is `0` if there is none. -/
noncomputable def concatGraph : ArithmeticSemisentence 3 :=
  “z x y. !isConcat x y z ∨ (z = 0 ∧ ∀ w, ¬!isConcat x y w)”

@[simp]
lemma eval_concatGraph : M ⊧/![z, x, y] concatGraph ↔ ConcatGraph z x y := by
  simp [concatGraph, ConcatGraph]

lemma IsConcat.eq {w : M} (hz : IsConcat x y z) (hw : IsConcat x y w) : z = w :=
  hw.unique z hz.eval

lemma existsUnique_concatGraph (x y : M) : ∃! z, ConcatGraph z x y := by
  by_cases h : ∃ z, IsConcat x y z
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

lemma isConcat_numeral (u v : FreeSemigroup Bool) :
    IsConcat (numeral u.code : M) (numeral v.code) (numeral (u * v).code) where
  left_le := by simpa using u.code_le_code_mul_left v
  right_le := by simpa using u.code_le_code_mul_right v
  eval := by simp [FreeSemigroup.primrec₂_mulCode.to_comp]
  unique := by simp [FreeSemigroup.primrec₂_mulCode.to_comp]

lemma IsConcat.exists_of_numeral {w : FreeSemigroup Bool} (h : IsConcat x y (numeral w.code)) :
    ∃ u v : FreeSemigroup Bool, x = numeral u.code ∧ y = numeral v.code := by
  obtain ⟨m, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.left_le
  obtain ⟨n, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.right_le
  have := (eval_cobhamRepresentation₂_numeral_iff FreeSemigroup.primrec₂_mulCode.to_comp m n).mp
    h.eval
  rw [numeral_inj_iff] at this
  obtain ⟨u, v, rfl, rfl⟩ := FreeSemigroup.eq_code_of_mulCode_ne_zero (this ▸ w.code_ne_zero)
  use u, v

lemma ConcatGraph.exists_of_numeral {w : FreeSemigroup Bool}
    (h : ConcatGraph (numeral w.code) x y) :
    ∃ u v : FreeSemigroup Bool, x = numeral u.code ∧ y = numeral v.code := by
  rcases h with h | ⟨h, -⟩
  · exact h.exists_of_numeral
  · have : w.code = 0 := numeral_inj_iff (M := M).mp <| by simpa using h
    exact absurd this w.code_ne_zero

end R0

/--
The translation of the language of concatenation into $\mathsf{R}_0$: a nonempty binary string is
the numeral of its code.
-/
noncomputable def codeTranslation : DirectTranslation 𝗥₀ ℒ⌢ where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .zero => ⟨“z. z = ↑(FreeSemigroup.code (0 : FreeSemigroup Bool))”⟩
    | .one => ⟨“z. z = ↑(FreeSemigroup.code (1 : FreeSemigroup Bool))”⟩
    | .concat => ⟨concatGraph⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_concatGraph (e 0) (e 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma codeTranslation_dom (x : M) : codeTranslation.Dom x := by
  simp [dom_iff, codeTranslation, Semiformula.Operator.val]

namespace codeTranslation

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

/-- The numeral of the code of a nonempty binary string. -/
def ofString (u : FreeSemigroup Bool) : codeTranslation.Model M := ⟨numeral u.code, by simp⟩

/-- The letters and the concatenation of the codes in `M`. -/
noncomputable abbrev concatenationStructure : ConcatenationStructure (codeTranslation.Model M) where
  zero := ofString 0
  one := ofString 1
  append x y := Tarski.Structure.func (L := ℒ⌢) Language.Concatenation.Func.concat ![x, y]

/-- The structure of the model of `codeTranslation` is the one of `concatenationStructure`. -/
lemma struc_eq : Model.struc codeTranslation M = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [codeTranslation, Semiformula.Operator.val]
        rfl
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

attribute [local instance] concatenationStructure

lemma append_eq_iff {x y z : codeTranslation.Model M} :
    x ++ y = z ↔ ConcatGraph (z : M) x y := by
  have := Model.func_iff (π := codeTranslation) (M := M) (f := Language.Concatenation.Func.concat)
    (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → codeTranslation.Model M) i : M)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_concatGraph] at this
  exact eq_comm.trans this

/-- The strings are embedded onto an initial part of the model of `codeTranslation`. -/
lemma isInitialEmbedding_ofString :
    IsInitialEmbedding (ofString : FreeSemigroup Bool → codeTranslation.Model M) where
  injective u v h := by simpa [ofString] using h
  map_zero := rfl
  map_one := rfl
  map_append u v := (append_eq_iff.mpr <| Or.inl <| isConcat_numeral u v).symm
  exists_of_append_eq h := by
    obtain ⟨u, v, hu, hv⟩ := (append_eq_iff.mp h).exists_of_numeral
    use u, v
    exact ⟨Model.ext hu, Model.ext hv⟩

end

/-- The model of `codeTranslation` satisfies $\mathsf{WTC}$. -/
instance : (codeTranslation.Model M)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := by
  rw [struc_eq]
  let := concatenationStructure (M := M)
  exact isInitialEmbedding_ofString.models_WTC

end codeTranslation

/--
$\mathsf{R}_0$ interprets $\mathsf{WTC}$.
- [Hor11, §3, Theorem 3.9]
-/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗧𝗖 where
  trln := codeTranslation
  interpret_theory φ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder.Concatenation

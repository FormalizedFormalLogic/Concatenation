module

public import Concatenation.Semantics.Basic
public import Concatenation.ToFoundation.Arithmetic.PeanoMinus.Pairing
public import Concatenation.ToMathlib.NonnegSpecialLinearGroup
public import AlphaCentauri.Interpretability.Basic
public import AlphaCentauri.ToMathlib.Algebra.Order.Ring.RingOfDifferences

/-!
# The matrix interpretation of $\mathsf{TC}$

$\mathsf{PA}^-$ interprets $\mathsf{TC}$ on the $2 \times 2$ matrices of determinant $1$ other than
the identity.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Language Arithmetic DirectTranslation Matrix.SpecialLinearGroup RingOfDifferences

section

variable {M : Type*} [ORingStructure M] {x y z p q r s p' q' r' s' : M}

/-- The code of the matrix $\begin{pmatrix} p & q \\ r & s \end{pmatrix}$. -/
def matrixCode (p q r s : M) : M := squarePair (squarePair p q) (squarePair r s)

/-- `x` is the code of the matrix $\begin{pmatrix} p & q \\ r & s \end{pmatrix}$. -/
def isMatrixCode : ArithmeticSemisentence 5 :=
  “x p q r s. ∃ u v, !isSquarePair u p q ∧ !isSquarePair v r s ∧ !isSquarePair x u v”

@[simp]
lemma eval_isMatrixCode : M ⊧/![x, p, q, r, s] isMatrixCode ↔ x = matrixCode p q r s := by
  simp [isMatrixCode, matrixCode]

/--
`x` is a string: the code of a matrix of determinant $1$ other than the identity.
- [Mur24, §5.1, §6.1]
-/
def IsMatrixString (x : M) : Prop :=
  x ≠ matrixCode 1 0 0 1 ∧ ∃ p q r s, x = matrixCode p q r s ∧ p * s = q * r + 1

/--
`x` is a string: the code of a matrix of determinant $1$ other than the identity.
- [Mur24, §5.1, §6.1]
-/
def isMatrixString : ArithmeticSemisentence 1 :=
  “x. ¬!isMatrixCode x 1 0 0 1 ∧ ∃ p q r s, !isMatrixCode x p q r s ∧ p * s = q * r + 1”

@[simp]
lemma eval_isMatrixString : M ⊧/![x] isMatrixString ↔ IsMatrixString x := by
  simp [isMatrixString, Matrix.comp_vecCons'', IsMatrixString]

/--
`z` is the code of the product of the matrices with the codes `x` and `y`.
- [Mur24, §5.1]
-/
def MatrixMulGraph (z x y : M) : Prop :=
  ∃ p q r s, x = matrixCode p q r s ∧ ∃ p' q' r' s', y = matrixCode p' q' r' s' ∧
    z = matrixCode (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s')

/--
`z` is the code of the product of the matrices with the codes `x` and `y`.
- [Mur24, §5.1]
-/
def matrixMulGraph : ArithmeticSemisentence 3 :=
  “z x y. ∃ p q r s, !isMatrixCode x p q r s ∧ ∃ p' q' r' s', !isMatrixCode y p' q' r' s' ∧
    !isMatrixCode z (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s')”

@[simp]
lemma eval_matrixMulGraph : M ⊧/![z, x, y] matrixMulGraph ↔ MatrixMulGraph z x y := by
  simp [matrixMulGraph, Matrix.comp_vecCons'', MatrixMulGraph]

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

@[simp]
lemma matrixCode_inj :
    matrixCode p q r s = matrixCode p' q' r' s' ↔ p = p' ∧ q = q' ∧ r = r' ∧ s = s' := by
  simp [matrixCode, and_assoc]

/-- `x` is the code of the matrix `A` over the ring of differences. -/
def CodesMatrix (x : M) (A : Matrix.SpecialLinearGroup (Fin 2) (RingOfDifferences M)) : Prop :=
  ∃ p q r s, x = matrixCode p q r s ∧ (A : Matrix (Fin 2) (Fin 2) (RingOfDifferences M)) =
    !![.of p, .of q; .of r, .of s]

private lemma of_add (a b : M) : of (a + b) = of a + of b := map_add of a b

private lemma of_mul (a b : M) : of (a * b) = of a * of b := map_mul of a b

variable {A B : Matrix.SpecialLinearGroup (Fin 2) (RingOfDifferences M)}

lemma CodesMatrix.mem_nonneg (h : CodesMatrix x A) : A ∈ nonneg (RingOfDifferences M) := by
  obtain ⟨p, q, r, s, rfl, hA⟩ := h
  simp only [mem_nonneg_iff, hA]
  exact Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨of_nonneg p, of_nonneg q⟩,
    Fin.forall_fin_two.mpr ⟨of_nonneg r, of_nonneg s⟩⟩

lemma exists_codesMatrix (h : A ∈ nonneg (RingOfDifferences M)) : ∃ x, CodesMatrix x A := by
  obtain ⟨p, hp⟩ := nonneg_iff.mp (h 0 0)
  obtain ⟨q, hq⟩ := nonneg_iff.mp (h 0 1)
  obtain ⟨r, hr⟩ := nonneg_iff.mp (h 1 0)
  obtain ⟨s, hs⟩ := nonneg_iff.mp (h 1 1)
  use matrixCode p q r s, p, q, r, s, rfl
  rw [hp, hq, hr, hs]
  exact Matrix.eta_fin_two _

lemma CodesMatrix.eq_iff (hx : CodesMatrix x A) (hy : CodesMatrix y B) : x = y ↔ A = B := by
  obtain ⟨p, q, r, s, rfl, hA⟩ := hx
  obtain ⟨p', q', r', s', rfl, hB⟩ := hy
  simp [Matrix.SpecialLinearGroup.ext_iff, Fin.forall_fin_two, hA, hB, and_assoc]

lemma codesMatrix_one : CodesMatrix (matrixCode 1 0 0 1 : M) 1 := by
  use 1, 0, 0, 1, rfl
  simp [Matrix.one_fin_two]

lemma codesMatrix_lower : CodesMatrix (matrixCode 1 0 1 1 : M) (lower _) := by
  use 1, 0, 1, 1, rfl
  simp [lower]

lemma codesMatrix_upper : CodesMatrix (matrixCode 1 1 0 1 : M) (upper _) := by
  use 1, 1, 0, 1, rfl
  simp [upper]

lemma isMatrixString_iff : IsMatrixString x ↔ ∃ A, CodesMatrix x A ∧ A ≠ 1 := by
  constructor
  · rintro ⟨h, p, q, r, s, rfl, hd⟩
    have hA : CodesMatrix (matrixCode p q r s)
        ⟨!![.of p, .of q; .of r, .of s], by simp [← of_mul, hd, of_add]⟩ := ⟨p, q, r, s, rfl, rfl⟩
    exact ⟨_, hA, fun h₁ ↦ h <| (hA.eq_iff codesMatrix_one).mpr h₁⟩
  · rintro ⟨A, hx, hA⟩
    and_intros
    · exact fun h ↦ hA <| (hx.eq_iff codesMatrix_one).mp h
    · obtain ⟨p, q, r, s, rfl, hA⟩ := hx
      use p, q, r, s, rfl
      have := apply_mul_apply_eq A
      apply of_injective
      simpa [hA, of_add, of_mul] using this

lemma CodesMatrix.matrixMulGraph_iff (hx : CodesMatrix x A) (hy : CodesMatrix y B) :
    MatrixMulGraph z x y ↔ CodesMatrix z (A * B) := by
  have h : ∃ w, CodesMatrix w (A * B) ∧ ∀ z, MatrixMulGraph z x y ↔ z = w := by
    obtain ⟨p, q, r, s, rfl, hA⟩ := hx
    obtain ⟨p', q', r', s', rfl, hB⟩ := hy
    use matrixCode (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s')
    and_intros
    · exact ⟨_, _, _, _, rfl, by simp [hA, hB, of_add, of_mul]⟩
    · simp [MatrixMulGraph]
  obtain ⟨w, hw, h⟩ := h
  rw [h]
  exact ⟨fun e ↦ e ▸ hw, fun hz ↦ (hz.eq_iff hw).mpr rfl⟩

lemma existsUnique_matrixMulGraph (hx : IsMatrixString x) (hy : IsMatrixString y) :
    ∃! z, IsMatrixString z ∧ MatrixMulGraph z x y := by
  obtain ⟨A, hA, hA₁⟩ := isMatrixString_iff.mp hx
  obtain ⟨B, hB, hB₁⟩ := isMatrixString_iff.mp hy
  obtain ⟨z, hz⟩ := exists_codesMatrix (mul_mem hA.mem_nonneg hB.mem_nonneg)
  simp only [hA.matrixMulGraph_iff hB]
  have h : A * B ≠ 1 := fun h ↦ hA₁ <| And.left <| eq_one_of_mul_eq_one
    (fun _ ↦ one_le_of_pos one_le_of_zero_lt) hA.mem_nonneg hB.mem_nonneg h
  use z
  exact ⟨⟨isMatrixString_iff.mpr ⟨_, hz, h⟩, hz⟩, fun w hw ↦ (hw.2.eq_iff hz).mpr rfl⟩

lemma isMatrixString_zero : IsMatrixString (matrixCode 1 0 1 1 : M) :=
  isMatrixString_iff.mpr ⟨_, codesMatrix_lower, lower_ne_one _⟩

lemma isMatrixString_one : IsMatrixString (matrixCode 1 1 0 1 : M) :=
  isMatrixString_iff.mpr ⟨_, codesMatrix_upper, upper_ne_one _⟩

end

/--
The translation of the language of concatenation into that of arithmetic on the matrices of
determinant $1$ other than the identity: the letters are $\begin{pmatrix} 1 & 0 \\ 1 & 1
\end{pmatrix}$ and $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$, and the concatenation is the
product.
- [Mur24, §5.1, §6.2, Theorem 22]
-/
def matrixTranslation : DirectTranslation 𝗣𝗔⁻ ℒ⌢ where
  domain := ⟨isMatrixString⟩
  rel R := match R with
    | Concatenation.Rel.eq => Semiformula.Operator.Eq.eq
  func f := match f with
    | Concatenation.Func.zero => ⟨“z. !isMatrixCode z 1 0 1 1”⟩
    | Concatenation.Func.one => ⟨“z. !isMatrixCode z 1 1 0 1”⟩
    | Concatenation.Func.concat => ⟨matrixMulGraph⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun M _ _ ↦
    (models_domainNonempty_iff _).mpr <| by
      use matrixCode 1 0 1 1
      simpa [Semiformula.Operator.val] using isMatrixString_zero
  func_defined f := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsMatrixString (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, IsMatrixString y ∧ y = matrixCode 1 0 1 1 by
        simpa [Semiformula.Operator.val, Matrix.comp_vecCons'']
      use matrixCode 1 0 1 1
      simp [isMatrixString_zero]
    · suffices ∃! y : M, IsMatrixString y ∧ y = matrixCode 1 1 0 1 by
        simpa [Semiformula.Operator.val, Matrix.comp_vecCons'']
      use matrixCode 1 1 0 1
      simp [isMatrixString_one]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_matrixMulGraph (he 0) (he 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] {x : M}

namespace matrixTranslation

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] in
@[simp]
lemma dom_iff : matrixTranslation.Dom x ↔ IsMatrixString x := by
  simp [DirectTranslation.dom_iff, matrixTranslation, Semiformula.Operator.val]

/-- The letters and the product of the strings of a model of $\mathsf{PA}^-$. -/
noncomputable abbrev concatenationStructure :
    ConcatenationStructure (matrixTranslation.Model M) where
  zero := ⟨matrixCode 1 0 1 1, dom_iff.mpr isMatrixString_zero⟩
  one := ⟨matrixCode 1 1 0 1, dom_iff.mpr isMatrixString_one⟩
  append x y := Tarski.Structure.func (L := ℒ⌢) Concatenation.Func.concat ![x, y]

/-- The structure of the model of `matrixTranslation` is the one of `concatenationStructure`. -/
lemma struc_eq : Model.struc matrixTranslation M = @standardModel _ concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [matrixTranslation, Semiformula.Operator.val, Matrix.comp_vecCons'']
        rfl
      · symm
        apply Model.func_iff.mpr
        simp [matrixTranslation, Semiformula.Operator.val, Matrix.comp_vecCons'']
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] concatenationStructure

variable {a b c d : matrixTranslation.Model M}
  {A B : Matrix.SpecialLinearGroup (Fin 2) (RingOfDifferences M)}

lemma exists_codesMatrix_val (a : matrixTranslation.Model M) :
    ∃ A, CodesMatrix (a : M) A ∧ A ≠ 1 := isMatrixString_iff.mp <| dom_iff.mp a.dom

lemma exists_codesMatrix_val_eq (hA : A ∈ nonneg (RingOfDifferences M)) (h : A ≠ 1) :
    ∃ a : matrixTranslation.Model M, CodesMatrix (a : M) A := by
  obtain ⟨x, hx⟩ := exists_codesMatrix hA
  use ⟨x, dom_iff.mpr <| isMatrixString_iff.mpr ⟨A, hx, h⟩⟩

lemma codesMatrix_val_append (ha : CodesMatrix (a : M) A) (hb : CodesMatrix (b : M) B) :
    CodesMatrix ((a ++ b : matrixTranslation.Model M) : M) (A * B) := by
  apply (ha.matrixMulGraph_iff hb).mp
  have h := Model.eval_func (π := matrixTranslation) (M := M) Concatenation.Func.concat ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → matrixTranslation.Model M) i : M)] at h
  simp only [matrixTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_matrixMulGraph] at h
  exact h

lemma eq_iff (ha : CodesMatrix (a : M) A) (hb : CodesMatrix (b : M) B) : a = b ↔ A = B :=
  Model.val_inj_iff.symm.trans <| ha.eq_iff hb

protected lemma append_assoc (a b c : matrixTranslation.Model M) : a ++ (b ++ c) = a ++ b ++ c := by
  obtain ⟨A, hA, -⟩ := exists_codesMatrix_val a
  obtain ⟨B, hB, -⟩ := exists_codesMatrix_val b
  obtain ⟨C, hC, -⟩ := exists_codesMatrix_val c
  exact (eq_iff (codesMatrix_val_append hA (codesMatrix_val_append hB hC))
    (codesMatrix_val_append (codesMatrix_val_append hA hB) hC)).mpr (mul_assoc A B C).symm

protected lemma zero_ne_append (a b : matrixTranslation.Model M) : 0 ≠ a ++ b := by
  obtain ⟨A, hA, hA₁⟩ := exists_codesMatrix_val a
  obtain ⟨B, hB, hB₁⟩ := exists_codesMatrix_val b
  intro h
  have h := (eq_iff codesMatrix_lower (codesMatrix_val_append hA hB)).mp h
  exact (eq_one_of_mul_eq_lower (fun _ ↦ one_le_of_pos one_le_of_zero_lt) hA.mem_nonneg
    hB.mem_nonneg h.symm).elim hA₁ hB₁

protected lemma one_ne_append (a b : matrixTranslation.Model M) : 1 ≠ a ++ b := by
  obtain ⟨A, hA, hA₁⟩ := exists_codesMatrix_val a
  obtain ⟨B, hB, hB₁⟩ := exists_codesMatrix_val b
  intro h
  have h := (eq_iff codesMatrix_upper (codesMatrix_val_append hA hB)).mp h
  exact (eq_one_of_mul_eq_upper (fun _ ↦ one_le_of_pos one_le_of_zero_lt) hA.mem_nonneg
    hB.mem_nonneg h.symm).elim hA₁ hB₁

protected lemma zero_ne_one : (0 : matrixTranslation.Model M) ≠ 1 :=
  fun h ↦ lower_ne_upper _ <| (eq_iff codesMatrix_lower codesMatrix_upper).mp h

lemma exists_append_eq (hA : CodesMatrix (a : M) A) (hB : CodesMatrix (b : M) B)
    (hn : A⁻¹ * B ∈ nonneg (RingOfDifferences M)) (h₁ : A ≠ B)
    {C D : Matrix.SpecialLinearGroup (Fin 2) (RingOfDifferences M)} (hC : CodesMatrix (c : M) C)
    (hD : CodesMatrix (d : M) D) (h : A * C = B * D) : ∃ u, a ++ u = b ∧ c = u ++ d := by
  obtain ⟨u, hu⟩ := exists_codesMatrix_val_eq hn fun h₂ ↦ h₁ <| inv_mul_eq_one.mp h₂
  use u
  and_intros
  · exact (eq_iff (codesMatrix_val_append hA hu) hB).mpr <| by simp
  · exact (eq_iff hC (codesMatrix_val_append hu hD)).mpr <| by simp [mul_assoc, ← h]

/--
The strings satisfy the editor axiom.
- [Mur24, §6.2, Theorem 22]
-/
protected lemma editor (h : a ++ b = c ++ d) :
    (a = c ∧ b = d) ∨ ∃ u, (a ++ u = c ∧ b = u ++ d) ∨ (a = c ++ u ∧ u ++ b = d) := by
  obtain ⟨A, hA, -⟩ := exists_codesMatrix_val a
  obtain ⟨B, hB, -⟩ := exists_codesMatrix_val b
  obtain ⟨C, hC, -⟩ := exists_codesMatrix_val c
  obtain ⟨D, hD, -⟩ := exists_codesMatrix_val d
  have h := (eq_iff (codesMatrix_val_append hA hB) (codesMatrix_val_append hC hD)).mp h
  by_cases h₁ : A = C
  · subst h₁
    exact Or.inl ⟨(eq_iff hA hC).mpr rfl, (eq_iff hB hD).mpr <| mul_left_cancel h⟩
  · right
    rcases inv_mul_mem_nonneg_or (fun _ ↦ one_le_of_pos one_le_of_zero_lt) hA.mem_nonneg
      hB.mem_nonneg hC.mem_nonneg hD.mem_nonneg h with hn | hn
    · obtain ⟨u, hu⟩ := exists_append_eq hA hC hn h₁ hB hD h
      use u
      exact Or.inl hu
    · obtain ⟨u, hu₁, hu₂⟩ := exists_append_eq hC hA hn (Ne.symm h₁) hD hB h.symm
      use u
      exact Or.inr ⟨hu₁.symm, hu₂.symm⟩

end

/--
The strings of a model of $\mathsf{PA}^-$ form a model of $\mathsf{TC}$.
- [Mur24, §6.2, Theorem 22]
-/
instance : (matrixTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  rw [struc_eq]
  let := concatenationStructure (M := M)
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case concatAssoc => simpa [models_iff] using matrixTranslation.append_assoc (M := M)
  case editor =>
    simpa [models_iff] using fun a b c d ↦
      matrixTranslation.editor (M := M) (a := a) (b := b) (c := c) (d := d)
  case zeroNeConcat => simpa [models_iff] using matrixTranslation.zero_ne_append (M := M)
  case oneNeConcat => simpa [models_iff] using matrixTranslation.one_ne_append (M := M)
  case zeroNeOne => simpa [models_iff] using matrixTranslation.zero_ne_one (M := M)

end matrixTranslation

/--
$\mathsf{PA}^-$ interprets $\mathsf{TC}$.
- [Mur24, §6.2, Theorem 22]
-/
instance : 𝗣𝗔⁻ ⊳ 𝗧𝗖 where
  trln := matrixTranslation
  interpret_theory φ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder.Concatenation

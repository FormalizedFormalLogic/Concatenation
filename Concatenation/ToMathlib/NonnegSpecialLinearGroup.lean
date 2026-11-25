module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# Nonnegative matrices of $\mathrm{SL}_2$

The monoid of the $2 \times 2$ matrices of determinant $1$ with nonnegative entries over a
discretely ordered commutative ring.
-/

@[expose] public section

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

variable (R) in
/--
The submonoid of $\mathrm{SL}_2$ of the matrices with nonnegative entries.
- [Mur24, §5.1]
-/
def nonneg : Submonoid (SpecialLinearGroup (Fin 2) R) where
  carrier := {A | ∀ i j, 0 ≤ A i j}
  one_mem' := by simp [Fin.forall_fin_two]
  mul_mem' {A B} hA hB i j := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      add_nonneg (mul_nonneg (hA i 0) (hB 0 j)) (mul_nonneg (hA i 1) (hB 1 j))

variable {A B C D : SpecialLinearGroup (Fin 2) R}

lemma mem_nonneg_iff : A ∈ nonneg R ↔ ∀ i j, 0 ≤ A i j := Iff.rfl

lemma apply_mul_apply_eq (A : SpecialLinearGroup (Fin 2) R) :
    A 0 0 * A 1 1 = A 0 1 * A 1 0 + 1 := by
  linear_combination (Matrix.det_fin_two (A : Matrix (Fin 2) (Fin 2) R)).symm.trans A.det_coe

lemma pos_of_mem_nonneg (hA : A ∈ nonneg R) : 0 < A 0 0 ∧ 0 < A 1 1 := by
  have h : 0 < A 0 0 * A 1 1 := by
    rw [apply_mul_apply_eq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (hA 0 1) (hA 1 0)) one_pos
  exact ⟨pos_of_mul_pos_left h (hA 1 1), pos_of_mul_pos_right h (hA 0 0)⟩

variable (hR : ∀ x : R, 0 < x → 1 ≤ x)

include hR in
lemma apply_eq_one (hA : A ∈ nonneg R) (h : A 0 1 * A 1 0 = 0) : A 0 0 = 1 ∧ A 1 1 = 1 := by
  have h₁ := hR _ (pos_of_mem_nonneg hA).1
  have h₂ := hR _ (pos_of_mem_nonneg hA).2
  have h₃ := apply_mul_apply_eq A
  constructor <;> nlinarith

include hR in
lemma eq_one_of_apply_eq_zero (hA : A ∈ nonneg R) (h₁ : A 0 1 = 0) (h₂ : A 1 0 = 0) : A = 1 := by
  obtain ⟨h₃, h₄⟩ := apply_eq_one hR hA (by simp [h₁])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₁, h₂, h₃, h₄]

include hR in
lemma eq_one_of_mul_apply_eq_zero (hA : A ∈ nonneg R) (hB : B ∈ nonneg R) (h₁ : (A * B) 0 1 = 0)
    (h₂ : (A * B) 1 0 = 0) : A = 1 := by
  obtain ⟨hA₀, hA₁⟩ := pos_of_mem_nonneg hA
  obtain ⟨hB₀, hB₁⟩ := pos_of_mem_nonneg hB
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h₁ h₂
  have := hA 0 1
  have := hA 1 0
  have := hB 0 1
  have := hB 1 0
  apply eq_one_of_apply_eq_zero hR hA <;> nlinarith

include hR in
/--
The product of two matrices with nonnegative entries is the identity only if both are.
- [Mur24, §6.1, Lemma 20]
-/
lemma eq_one_of_mul_eq_one (hA : A ∈ nonneg R) (hB : B ∈ nonneg R) (h : A * B = 1) :
    A = 1 ∧ B = 1 := by
  have hA : A = 1 := eq_one_of_mul_apply_eq_zero hR hA hB (by simp [h]) (by simp [h])
  simpa [hA] using h

variable (R) in
/--
The matrix $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$.
- [Mur24, §5.1]
-/
def lower : SpecialLinearGroup (Fin 2) R := ⟨!![1, 0; 1, 1], by simp⟩

variable (R) in
/--
The matrix $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$.
- [Mur24, §5.1]
-/
def upper : SpecialLinearGroup (Fin 2) R := ⟨!![1, 1; 0, 1], by simp⟩

variable (R) in
lemma lower_ne_one : lower R ≠ 1 := fun h ↦ by simpa [lower] using congr($h 1 0)

variable (R) in
lemma upper_ne_one : upper R ≠ 1 := fun h ↦ by simpa [upper] using congr($h 0 1)

variable (R) in
lemma lower_ne_upper : lower R ≠ upper R := fun h ↦ by simpa [lower, upper] using congr($h 0 1)

include hR in
/--
The matrix $\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ is an atom.
- [Mur24, §6.1, Lemma 20]
-/
lemma eq_one_of_mul_eq_lower (hA : A ∈ nonneg R) (hB : B ∈ nonneg R) (h : A * B = lower R) :
    A = 1 ∨ B = 1 := by
  have h₁ := congr($h 0 1)
  have h₂ := congr($h 1 0)
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, lower, of_apply, cons_val_zero,
    cons_val_one, cons_val', cons_val_fin_one] at h₁ h₂
  obtain ⟨hA₀, hA₁⟩ := pos_of_mem_nonneg hA
  obtain ⟨hB₀, hB₁⟩ := pos_of_mem_nonneg hB
  have hA₂ := hA 0 1
  have hB₂ := hB 0 1
  have hA₃ : A 0 1 = 0 := by nlinarith
  have hB₃ : B 0 1 = 0 := by nlinarith
  obtain ⟨hA₄, hA₅⟩ := apply_eq_one hR hA (by simp [hA₃])
  obtain ⟨hB₄, hB₅⟩ := apply_eq_one hR hB (by simp [hB₃])
  simp only [hA₅, hB₄, one_mul, mul_one] at h₂
  rcases (hA 1 0).eq_or_lt with h₃ | h₃
  · exact Or.inl <| eq_one_of_apply_eq_zero hR hA hA₃ h₃.symm
  · have := hR _ h₃
    have : B 1 0 = 0 := le_antisymm (by linarith) (hB 1 0)
    exact Or.inr <| eq_one_of_apply_eq_zero hR hB hB₃ this

include hR in
/--
The matrix $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ is an atom.
- [Mur24, §6.1, Lemma 20]
-/
lemma eq_one_of_mul_eq_upper (hA : A ∈ nonneg R) (hB : B ∈ nonneg R) (h : A * B = upper R) :
    A = 1 ∨ B = 1 := by
  have h₁ := congr($h 1 0)
  have h₂ := congr($h 0 1)
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, upper, of_apply, cons_val_zero,
    cons_val_one, cons_val', cons_val_fin_one] at h₁ h₂
  obtain ⟨hA₀, hA₁⟩ := pos_of_mem_nonneg hA
  obtain ⟨hB₀, hB₁⟩ := pos_of_mem_nonneg hB
  have hA₂ := hA 1 0
  have hB₂ := hB 1 0
  have hA₃ : A 1 0 = 0 := by nlinarith
  have hB₃ : B 1 0 = 0 := by nlinarith
  obtain ⟨hA₄, hA₅⟩ := apply_eq_one hR hA (by simp [hA₃])
  obtain ⟨hB₄, hB₅⟩ := apply_eq_one hR hB (by simp [hB₃])
  simp only [hA₄, hB₅, one_mul, mul_one] at h₂
  rcases (hA 0 1).eq_or_lt with h₃ | h₃
  · exact Or.inl <| eq_one_of_apply_eq_zero hR hA h₃.symm hA₃
  · have := hR _ h₃
    have : B 0 1 = 0 := le_antisymm (by linarith) (hB 0 1)
    exact Or.inr <| eq_one_of_apply_eq_zero hR hB this hB₃

private lemma apply_zero_zero_pos {W : SpecialLinearGroup (Fin 2) R} (hA : A ∈ nonneg R)
    (hD : D ∈ nonneg R) (hAW : A * W ∈ nonneg R) (hWD : W * D ∈ nonneg R) : 0 < W 0 0 := by
  by_contra! hw
  have h₁ := (pos_of_mem_nonneg hAW).1
  have h₂ := hAW 0 1
  have h₃ := (pos_of_mem_nonneg hWD).1
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h₁ h₂ h₃
  have ha := (pos_of_mem_nonneg hA).1
  have hb := hA 0 1
  have he := (pos_of_mem_nonneg hD).1
  have hg := hD 1 0
  have hy : 0 < W 1 0 := by by_contra!; nlinarith
  have hx : 0 < W 0 1 := by by_contra!; nlinarith
  have := apply_mul_apply_eq W
  nlinarith [mul_pos h₁ hx, mul_nonneg h₂ (neg_nonneg.mpr hw)]

private lemma apply_one_one_pos {W : SpecialLinearGroup (Fin 2) R} (hA : A ∈ nonneg R)
    (hD : D ∈ nonneg R) (hAW : A * W ∈ nonneg R) (hWD : W * D ∈ nonneg R) : 0 < W 1 1 := by
  by_contra! hz
  have h₂ := (pos_of_mem_nonneg hAW).2
  have h₃ := (pos_of_mem_nonneg hWD).2
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h₂ h₃
  have hd := (pos_of_mem_nonneg hA).2
  have hc := hA 1 0
  have hh := (pos_of_mem_nonneg hD).2
  have hf := hD 0 1
  have hx : 0 < W 0 1 := by by_contra!; nlinarith
  have hy : 0 < W 1 0 := by by_contra!; nlinarith
  have := apply_mul_apply_eq W
  nlinarith [apply_zero_zero_pos hA hD hAW hWD]

include hR in
/--
Of two factors with nonnegative entries of a matrix, one divides the other.
-/
lemma inv_mul_mem_nonneg_or (hA : A ∈ nonneg R) (hB : B ∈ nonneg R) (hC : C ∈ nonneg R)
    (hD : D ∈ nonneg R) (h : A * B = C * D) : A⁻¹ * C ∈ nonneg R ∨ C⁻¹ * A ∈ nonneg R := by
  obtain ⟨W, hW⟩ : ∃ W, W = A⁻¹ * C := ⟨_, rfl⟩
  have hW' : C⁻¹ * A = W⁻¹ := by simp [hW]
  have hAW : A * W = C := by simp [hW]
  have hWD : W * D = B := by rw [hW, mul_assoc, ← h]; simp
  rw [← hW, hW']
  rw [← hAW] at hC
  rw [← hWD] at hB
  have hw := apply_zero_zero_pos hA hD hC hB
  have hz := apply_one_one_pos hA hD hC hB
  have hdet := apply_mul_apply_eq W
  simp only [mem_nonneg_iff, SL2_inv_expl, Fin.forall_fin_two]
  simp only [coe_mk, of_apply, cons_val_zero, cons_val_one, cons_val', cons_val_fin_one,
    Left.nonneg_neg_iff]
  have hxy : 0 ≤ W 0 1 * W 1 0 := by
    by_contra! h₀
    have := hR _ (neg_pos.mpr h₀)
    have := mul_pos hw hz
    linarith
  rcases nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨⟨hw.le, hx⟩, hy, hz.le⟩
  · exact Or.inr ⟨⟨hz.le, hx⟩, hy, hw.le⟩

end Matrix.SpecialLinearGroup

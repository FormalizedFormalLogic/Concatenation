module

public import Concatenation.Minimality.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
import Concatenation.OpenProblem

/-!
# $\mathsf{D}$ without one of the axioms on the prefixes of $y0$ and $y1$

The dyadic contractions of the unit interval are a model of both theories that is definable in the
field of real numbers with a predicate for the powers of two. Whether the theory of either model is
decidable is open, and with it the minimality of $\mathsf{D}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
The maps $u \mapsto c + 2^{-n} u$ of $[0, 1)$ into itself with $n \geq 1$, composed in reverse
order. The letters are $u \mapsto u / 2$ and $u \mapsto (1 + u) / 2$, and $x$ is below $y$ when
$y$ is $x$ followed by a power of the letter `b`.
-/
@[ext]
structure DyadicContraction (b : Bool) where
  /-- The exponent $n$ of the slope $2^{-n}$. -/
  level : ℕ
  /-- The value $c$ at $0$. -/
  shift : ℝ
  one_le_level : 1 ≤ level
  shift_nonneg : 0 ≤ shift
  shift_add_le : shift + (1 / 2) ^ level ≤ 1

namespace DyadicContraction

variable {b : Bool} {x y : DyadicContraction b}

noncomputable instance : Zero (DyadicContraction b) := ⟨⟨1, 0, le_rfl, le_rfl, by norm_num⟩⟩

noncomputable instance : One (DyadicContraction b) := ⟨⟨1, 1 / 2, le_rfl, by norm_num, by norm_num⟩⟩

noncomputable instance : Append (DyadicContraction b) :=
  ⟨fun x y ↦
    { level := x.level + y.level
      shift := y.shift + (1 / 2) ^ y.level * x.shift
      one_le_level := le_add_right x.one_le_level
      shift_nonneg := add_nonneg y.shift_nonneg <| mul_nonneg (by positivity) x.shift_nonneg
      shift_add_le := by
        have hx := x.shift_add_le
        have hy := y.shift_add_le
        have p : (0 : ℝ) < (1 / 2) ^ y.level := by positivity
        rw [pow_add]
        nlinarith }⟩

/-- The letter `b`. -/
noncomputable def letter (b : Bool) : DyadicContraction b := if b then 1 else 0

/-- `x` is below `y` when `y` is `x` followed by a power of the letter `b`. -/
instance : LE (DyadicContraction b) := ⟨fun x y ↦ ∃ j : ℕ, y = (· ++ letter b)^[j] x⟩

lemma le_def : x ≤ y ↔ ∃ j : ℕ, y = (· ++ letter b)^[j] x := Iff.rfl

@[simp]
lemma level_append (x y : DyadicContraction b) : (x ++ y).level = x.level + y.level := rfl

@[simp]
lemma shift_append (x y : DyadicContraction b) :
    (x ++ y).shift = y.shift + (1 / 2) ^ y.level * x.shift := rfl

@[simp]
lemma level_zero : (0 : DyadicContraction b).level = 1 := rfl

@[simp]
lemma level_one : (1 : DyadicContraction b).level = 1 := rfl

@[simp]
lemma shift_zero : (0 : DyadicContraction b).shift = 0 := rfl

@[simp]
lemma shift_one : (1 : DyadicContraction b).shift = 1 / 2 := rfl

lemma letter_true : letter true = 1 := rfl

lemma letter_false : letter false = 0 := rfl

@[simp]
lemma level_letter : (letter b).level = 1 := by cases b <;> rfl

protected lemma append_assoc (x y z : DyadicContraction b) : (x ++ y) ++ z = x ++ (y ++ z) := by
  ext
  · simp [add_assoc]
  · simp [pow_add]
    ring

lemma append_zero_injective : Function.Injective fun x : DyadicContraction b ↦ x ++ 0 :=
  fun x y h ↦ by
    have h₁ := congrArg level h
    have h₂ := congrArg shift h
    ext
    · simpa using h₁
    · simpa using h₂

lemma append_one_injective : Function.Injective fun x : DyadicContraction b ↦ x ++ 1 :=
  fun x y h ↦ by
    have h₁ := congrArg level h
    have h₂ := congrArg shift h
    ext
    · simpa using h₁
    · simpa using h₂

lemma append_letter_injective : Function.Injective fun x : DyadicContraction b ↦ x ++ letter b := by
  cases b
  · exact append_zero_injective
  · exact append_one_injective

lemma append_zero_ne_append_one (x y : DyadicContraction b) : x ++ 0 ≠ y ++ 1 := fun h ↦ by
  have h₁ := congrArg level h
  have h₂ := congrArg shift h
  have hx := x.shift_add_le
  have hy := y.shift_nonneg
  have p : (0 : ℝ) < (1 / 2) ^ x.level := by positivity
  simp only [shift_append, shift_zero, level_zero, shift_one, level_one] at h₂
  linarith

lemma le_zero_iff : x ≤ 0 ↔ x = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · exact hj.symm
    · rw [Function.iterate_succ_apply'] at hj
      have h := congrArg level hj
      have := ((· ++ letter b)^[j] x).one_le_level
      simp only [level_zero, level_append, level_letter] at h
      omega
  · rintro rfl
    exact ⟨0, rfl⟩

lemma le_append_letter : x ≤ y ++ letter b ↔ x = y ++ letter b ∨ x ≤ y := by
  constructor
  · rintro ⟨j, hj⟩
    rcases j with _ | j
    · exact .inl hj.symm
    · rw [Function.iterate_succ_apply'] at hj
      exact .inr ⟨j, append_letter_injective hj⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j + 1, by rw [Function.iterate_succ_apply']⟩

/-- The model of the axioms of $\mathsf{D}$ that hold whichever letter orders the model. -/
lemma models_of_isDAxiom {σ : Sentence ℒ⌢⊑} (h : IsDAxiom σ) (h₀ : σ ≠ prefixConcatZero)
    (h₁ : σ ≠ prefixConcatOne) : (DyadicContraction b)↓[ℒ⌢⊑] ⊧ σ := by
  cases h
  case equal hφ =>
    have : (DyadicContraction b)↓[ℒ⌢⊑] ⊧* 𝗘𝗤 ℒ⌢⊑ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simp [models_iff, DyadicContraction.append_assoc]
  case concatRightCancel =>
    simpa [models_iff] using fun (x y : DyadicContraction b) h ↦
      ⟨fun e ↦ h <| append_zero_injective e, fun e ↦ h <| append_one_injective e⟩
  case concatZeroNeConcatOne => simpa [models_iff] using append_zero_ne_append_one (b := b)
  case prefixZero => simpa [models_iff] using fun x : DyadicContraction b ↦ le_zero_iff
  case prefixConcatZero => exact absurd rfl h₀
  case prefixConcatOne => exact absurd rfl h₁

/-- Ordered by the powers of $1$, the dyadic contractions are a model of $\mathsf{D}$ without the
axiom on the prefixes of $y0$. -/
instance models_D_diff_prefixConcatZero :
    (DyadicContraction true)↓[ℒ⌢⊑] ⊧* (𝗗 \ {prefixConcatZero} : Theory ℒ⌢⊑) := ⟨by
  rintro σ ⟨h, hσ⟩
  by_cases h₁ : σ = prefixConcatOne
  · rw [h₁]
    simpa [models_iff, prefixConcatOne] using
      fun x y : DyadicContraction true ↦ letter_true ▸ le_append_letter (b := true)
  · exact models_of_isDAxiom h hσ h₁⟩

/-- Ordered by the powers of $0$, the dyadic contractions are a model of $\mathsf{D}$ without the
axiom on the prefixes of $y1$. -/
instance models_D_diff_prefixConcatOne :
    (DyadicContraction false)↓[ℒ⌢⊑] ⊧* (𝗗 \ {prefixConcatOne} : Theory ℒ⌢⊑) := ⟨by
  rintro σ ⟨h, hσ⟩
  by_cases h₀ : σ = prefixConcatZero
  · rw [h₀]
    simpa [models_iff, prefixConcatZero] using
      fun x y : DyadicContraction false ↦ letter_false ▸ le_append_letter (b := false)
  · exact models_of_isDAxiom h h₀ hσ⟩

end DyadicContraction

/--
$\mathsf{D}$ without the axiom on the prefixes of $y0$ is not essentially undecidable, if the
theory of the dyadic contractions ordered by the powers of $1$ is decidable.
- [Mur22, Open Problem 2]
-/
theorem not_essentiallyUndecidable_D_diff_prefixConcatZero_of_decidable
    (h : Entailment.Decidable (Tarski.Structure.theory ℒ⌢⊑ (DyadicContraction true))) :
    ¬(𝗗 \ {prefixConcatZero} : Theory ℒ⌢⊑).EssentiallyUndecidable :=
  Theory.not_essentiallyUndecidable_of_models (DyadicContraction true) h

/--
$\mathsf{D}$ without the axiom on the prefixes of $y1$ is not essentially undecidable, if the
theory of the dyadic contractions ordered by the powers of $0$ is decidable.
- [Mur22, Open Problem 2]
-/
theorem not_essentiallyUndecidable_D_diff_prefixConcatOne_of_decidable
    (h : Entailment.Decidable (Tarski.Structure.theory ℒ⌢⊑ (DyadicContraction false))) :
    ¬(𝗗 \ {prefixConcatOne} : Theory ℒ⌢⊑).EssentiallyUndecidable :=
  Theory.not_essentiallyUndecidable_of_models (DyadicContraction false) h

/--
Is $\mathsf{D} - \mathsf{D}_5$, without the axiom
$x \preceq y0 \leftrightarrow x = y0 \lor x \preceq y$, not essentially undecidable?
- [Mur22, Open Problem 2]
-/
open_problem not_essentiallyUndecidable_D_diff_prefixConcatZero :=
  ¬(𝗗 \ {prefixConcatZero} : Theory ℒ⌢⊑).EssentiallyUndecidable

/--
Is $\mathsf{D} - \mathsf{D}_6$, without the axiom
$x \preceq y1 \leftrightarrow x = y1 \lor x \preceq y$, not essentially undecidable?
- [Mur22, Open Problem 2]
-/
open_problem not_essentiallyUndecidable_D_diff_prefixConcatOne :=
  ¬(𝗗 \ {prefixConcatOne} : Theory ℒ⌢⊑).EssentiallyUndecidable

end FFL.FirstOrder.Concatenation

module

public import Concatenation.Coding
public import Concatenation.TC.Arithmetic
public import Concatenation.ToFoundation.Arithmetic.R0.Representation

/-!
# Weak representability in $\mathsf{TC}$

The transport of weak representations in $\mathsf{R}_0$ to $\mathsf{TC}^+$ along the arithmetic
translation, and to $\mathsf{TC}$ along the translation on the thin strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

variable {M : Type*} [ConcatenationStructure M]

/--
The element named by `numeralTerm n`: the letter `0` for `n = 0`, the string of `n` letters `1`
otherwise.
-/
def tallyOf : ℕ → M
  | 0 => 0
  | 1 => 1
  | n + 2 => tallyOf (n + 1) ++ 1

@[simp]
lemma tallyOf_zero : (tallyOf 0 : M) = 0 := rfl

@[simp]
lemma tallyOf_one : (tallyOf 1 : M) = 1 := rfl

@[simp]
lemma tallyOf_add_two (n : ℕ) : (tallyOf (n + 2) : M) = tallyOf (n + 1) ++ 1 := rfl

@[simp]
lemma val_numeralTerm : ∀ n, (numeralTerm n).val (![] : Fin 0 → M) Empty.elim = tallyOf n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [val_numeralTerm (n + 1)]

/--
The transport of an arithmetic formula `γ` to the language of concatenation: `y` is a number, and
`x` and `y` satisfy the translation of `γ`.
-/
def transportedRepresentation (γ : ArithmeticSemisentence 2) : Semisentence ℒ⌢ 2 :=
  “x y. !isNumber y ∧ !(arithmeticTranslation.translate γ) x y”

/--
The transport of a formula `γ` of the language of concatenation to the thin strings: `y` is thin,
and `x` and `y` satisfy the translation of `γ`.
- [Gan09, §3, Lemma 6]
-/
def thinRepresentation (γ : Semisentence ℒ⌢ 2) : Semisentence ℒ⌢ 2 :=
  “x y. !isThin y ∧ !(thinTranslation.translate γ) x y”

/-- The transport of an arithmetic formula `γ` to the thin numbers. -/
def weakRepresentation (γ : ArithmeticSemisentence 2) : Semisentence ℒ⌢ 2 :=
  thinRepresentation (transportedRepresentation γ)

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma isTally_tallyOf_succ : ∀ n, IsTally 1 (tallyOf (n + 1) : M)
  | 0 => isTally_one_one
  | n + 1 => (isTally_tallyOf_succ n).append_one

lemma isNumber_tallyOf : ∀ n, IsNumber (tallyOf n : M)
  | 0 => isNumber_zero
  | n + 1 => (isTally_tallyOf_succ n).isNumber

lemma isThin_tallyOf : ∀ n, IsThin (tallyOf n : M)
  | 0 => isThin_zero
  | 1 => isThin_one
  | n + 2 => (isThin_tallyOf (n + 1)).append isThin_one

end TC

section TCPlus

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

namespace arithmeticTranslation

section

attribute [local instance] oRingStructure

@[simp]
lemma val_numeral :
    ∀ n, ((ORingStructure.numeral n : arithmeticTranslation.Model M) : M) = tallyOf n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    have h := val_numeral (n + 1)
    rw [ORingStructure.numeral, val_add_of_isTally (h ▸ isTally_tallyOf_succ n) isTally_one_one, h]
    rfl

end

@[simp]
lemma val_operator_numeral (n : ℕ) :
    (((Semiterm.Operator.numeral ℒₒᵣ n).val ![] : arithmeticTranslation.Model M) : M) =
      tallyOf n := by
  let _ : ORingStructure (arithmeticTranslation.Model M) := oRingStructure
  rw [struc_eq, Tarski.Structure.numeral_eq_numeral, val_numeral]

/-- The numbers of a model of $\mathsf{TC}^+$ form a model of $\mathsf{R}_0$. -/
instance : (arithmeticTranslation.Model M)↓[ℒₒᵣ] ⊧* 𝗥₀ :=
  models_of_subtheory (inferInstance : (arithmeticTranslation.Model M)↓[ℒₒᵣ] ⊧* 𝗤)

end arithmeticTranslation

variable {γ : ArithmeticSemisentence 2} {f : ℕ → ℕ}

lemma eval_transportedRepresentation (hγ : ∀ n, 𝗥₀ ⊢ “∀ y, !γ ↑n y ↔ y = ↑(f n)”) (n : ℕ) (y : M) :
    M ⊧/![tallyOf n, y] (transportedRepresentation γ) ↔ y = tallyOf (f n) := by
  by_cases hy : IsNumber y
  · let a : arithmeticTranslation.Model M := (Semiterm.Operator.numeral ℒₒᵣ n).val ![]
    let b : arithmeticTranslation.Model M := ⟨y, arithmeticTranslation_dom_iff.mpr hy⟩
    have h : ∀ c : arithmeticTranslation.Model M, (arithmeticTranslation.Model M) ⊧/![a, c] γ ↔
        c = (Semiterm.Operator.numeral ℒₒᵣ (f n)).val ![] := by
      simpa [models_iff] using
        models_of_provable (M := arithmeticTranslation.Model M) inferInstance (hγ n)
    replace h := h b
    rw [← Model.evalb_doubleton_translate_iff, ← Model.val_inj_iff] at h
    simpa [transportedRepresentation, hy, a, b] using h
  · suffices y ≠ tallyOf (f n) by simpa [transportedRepresentation, hy]
    rintro rfl
    exact hy <| isNumber_tallyOf _

/--
If `γ` weakly represents `f` in $\mathsf{R}_0$, then the transport of `γ` weakly represents `f` in
$\mathsf{TC}^+$.
- [Sve08, §3.3]
- [Gan09, §3, Theorem 4]
-/
lemma transportedRepresentation_spec (hγ : ∀ n, 𝗥₀ ⊢ “∀ y, !γ ↑n y ↔ y = ↑(f n)”) (n : ℕ) :
    𝗧𝗖⁺ ⊢ “∀ y, !(transportedRepresentation γ) !!(Rew.bShift (numeralTerm n)) y ↔
        y = !!(Rew.bShift (numeralTerm (f n)))” :=
  complete.{0} _ _ fun M _ _ ↦ by
    simpa [models_iff] using eval_transportedRepresentation hγ n

end TCPlus

section thin

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖] {γ : Semisentence ℒ⌢ 2} {f : ℕ → ℕ}

namespace thinTranslation

attribute [local instance] concatenationStructure in
lemma val_tallyOf : ∀ n, ((tallyOf n : thinTranslation.Model M) : M) = tallyOf n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (· ++ 1) <| val_tallyOf (n + 1)

@[simp]
lemma val_numeralTerm (n : ℕ) :
    (((numeralTerm n).val ![] Empty.elim : thinTranslation.Model M) : M) = tallyOf n := by
  let := concatenationStructure (M := M)
  rw [struc_eq, Concatenation.val_numeralTerm, val_tallyOf]

end thinTranslation

lemma eval_thinRepresentation
    (hγ : ∀ n, 𝗧𝗖⁺ ⊢ “∀ y, !γ !!(Rew.bShift (numeralTerm n)) y ↔
      y = !!(Rew.bShift (numeralTerm (f n)))”) (n : ℕ) (y : M) :
    M ⊧/![tallyOf n, y] (thinRepresentation γ) ↔ y = tallyOf (f n) := by
  by_cases hy : IsThin y
  · let a : thinTranslation.Model M := (numeralTerm n).val ![] Empty.elim
    let b : thinTranslation.Model M := ⟨y, thinTranslation_dom_iff.mpr hy⟩
    have h : ∀ c : thinTranslation.Model M, (thinTranslation.Model M) ⊧/![a, c] γ ↔
        c = (numeralTerm (f n)).val ![] Empty.elim := by
      simpa [models_iff] using
        models_of_provable (M := thinTranslation.Model M) inferInstance (hγ n)
    replace h := h b
    rw [← Model.evalb_doubleton_translate_iff, ← Model.val_inj_iff] at h
    simpa [thinRepresentation, hy, a, b] using h
  · suffices y ≠ tallyOf (f n) by simpa [thinRepresentation, hy]
    rintro rfl
    exact hy <| isThin_tallyOf _

/--
If `γ` weakly represents `f` in $\mathsf{TC}^+$, then the transport of `γ` to the thin strings
weakly represents `f` in $\mathsf{TC}$.
- [Gan09, §3, Lemma 6]
-/
lemma thinRepresentation_spec
    (hγ : ∀ n, 𝗧𝗖⁺ ⊢ “∀ y, !γ !!(Rew.bShift (numeralTerm n)) y ↔
      y = !!(Rew.bShift (numeralTerm (f n)))”) (n : ℕ) :
    𝗧𝗖 ⊢ “∀ y, !(thinRepresentation γ) !!(Rew.bShift (numeralTerm n)) y ↔
      y = !!(Rew.bShift (numeralTerm (f n)))” :=
  complete.{0} _ _ fun M _ _ ↦ by
    simpa [models_iff] using eval_thinRepresentation hγ n

end thin

/--
If `γ` weakly represents `f` in $\mathsf{R}_0$, then `weakRepresentation γ` weakly represents `f` in
$\mathsf{TC}$.
- [Sve08, §3.3]
- [Gan09, §3, Theorem 5]
-/
lemma weakRepresentation_spec {γ : ArithmeticSemisentence 2} {f : ℕ → ℕ}
    (hγ : ∀ n, 𝗥₀ ⊢ “∀ y, !γ ↑n y ↔ y = ↑(f n)”) (n : ℕ) :
    𝗧𝗖 ⊢ “∀ y, !(weakRepresentation γ) !!(Rew.bShift (numeralTerm n)) y ↔
      y = !!(Rew.bShift (numeralTerm (f n)))” :=
  thinRepresentation_spec (transportedRepresentation_spec hγ) n

/--
`weakRepresentation (Arithmetic.R0.cobhamRepresentation f)` weakly represents the computable
function `f` in $\mathsf{TC}$.
- [Sve08, §3.3]
- [Gan09, §3, Theorem 5]
-/
theorem weakRepresentation_cobhamRepresentation_spec {f : ℕ → ℕ} (hf : Computable f) (n : ℕ) :
    𝗧𝗖 ⊢ “∀ y, !(weakRepresentation (Arithmetic.R0.cobhamRepresentation f))
      !!(Rew.bShift (numeralTerm n)) y ↔ y = !!(Rew.bShift (numeralTerm (f n)))” :=
  weakRepresentation_spec (Arithmetic.R0.cobhamRepresentation_spec hf) n

end FFL.FirstOrder.Concatenation

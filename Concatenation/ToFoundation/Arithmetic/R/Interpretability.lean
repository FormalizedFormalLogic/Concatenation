module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.ToFoundation.Arithmetic.R
public import Concatenation.ToFoundation.Arithmetic.R0.Cobham
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability

/-!
# Interpretability of $\mathsf{R}$ in $\mathsf{R}_0$

$\mathsf{R}$ is mutually interpretable with $\mathsf{R}_0$, and it is essentially undecidable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open DirectTranslation ORingStructure

namespace R0

/--
The translation of the language of arithmetic into $\mathsf{R}_0$ that reads the order as the
strict part of Cobham's order.
- [Sve08, §3.3]
-/
def cobhamTranslation : DirectTranslation 𝗥₀ ℒₒᵣ where
  domain := ⟨“x. ⊤”⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨cobhamLTDef⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Function.comp_def]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {V : Type*} [ORingStructure V]

@[simp]
lemma cobhamTranslation_dom (x : V) : cobhamTranslation.Dom x := by
  simp [dom_iff, cobhamTranslation, Semiformula.Operator.val]

namespace cobhamTranslation

/-- The constants and the operations of `V`, with the strict part of Cobham's order. -/
abbrev oRingStructure : ORingStructure (cobhamTranslation.Model V) where
  zero := ⟨0, by simp⟩
  one := ⟨1, by simp⟩
  add x y := ⟨x + y, by simp⟩
  mul x y := ⟨x * y, by simp⟩
  lt x y := CobhamLT (x : V) y

attribute [local instance] oRingStructure in
lemma val_numeral (n : ℕ) : ((numeral n : cobhamTranslation.Model V) : V) = numeral n :=
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (· + (1 : V)) (val_numeral (n + 1))

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

/-- The structure of the model of `cobhamTranslation` is the one of `oRingStructure`. -/
lemma struc_eq : Model.struc cobhamTranslation V = @standardModel _ oRingStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [cobhamTranslation, Semiformula.Operator.val,
        Semiformula.Operator.Eq.sentence_eq] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      · exact propext <| Model.eq_iff v
      · change (cobhamTranslation.rel .lt).val (fun i ↦ (v i : V)) = CobhamLT (v 0 : V) (v 1)
        rw [Matrix.fun_eq_vec_two (fun i ↦ (v i : V))]
        simp [cobhamTranslation, Semiformula.Operator.val])

/--
A model of $\mathsf{R}_0$ with the strict part of Cobham's order is a model of $\mathsf{R}$.
- [Sve08, §3.3]
-/
instance : (cobhamTranslation.Model V)↓[ℒₒᵣ] ⊧* 𝗥 := by
  rw [struc_eq]
  let := oRingStructure (V := V)
  have lt_iff (x : cobhamTranslation.Model V) (n : ℕ) :
      x < numeral n ↔ (x : V) < numeral n := by
    change CobhamLT (x : V) (numeral n : cobhamTranslation.Model V) ↔ _
    rw [val_numeral, cobhamLT_numeral_iff]
  rw [R.models_iff_models_R0]
  and_intros
  · constructor
    intro σ hσ
    cases hσ
    case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
    case Ω₁ n m =>
      suffices (numeral n + numeral m : cobhamTranslation.Model V) = numeral (n + m) by
        simpa [models_iff]
      apply Model.ext
      rw [val_numeral, ← numeral_add_numeral]
      exact congrArg₂ (· + ·) (val_numeral n) (val_numeral m)
    case Ω₂ n m =>
      suffices (numeral n * numeral m : cobhamTranslation.Model V) = numeral (n * m) by
        simpa [models_iff]
      apply Model.ext
      rw [val_numeral, ← numeral_mul_numeral]
      exact congrArg₂ (· * ·) (val_numeral n) (val_numeral m)
    case Ω₃ n =>
      suffices ∀ x : cobhamTranslation.Model V, x < numeral n ↔ ∃ i < n, x = numeral i by
        simpa [models_iff]
      intro x
      rw [lt_iff, lt_numeral_iff, Fin.exists_iff]
      simp [← Model.val_inj_iff, val_numeral]
  · intro n x
    by_cases h : (x : V) = numeral n
    · exact Or.inl <| Model.ext <| h.trans (val_numeral n).symm
    · right
      have h' := cobhamLE_numeral_or (x := (x : V)) n
      rw [← val_numeral (V := V)] at h h'
      exact h'.imp (⟨·, h⟩) (⟨·, Ne.symm h⟩)

end cobhamTranslation

end model

end R0

/--
$\mathsf{R}_0$ interprets $\mathsf{R}$.
- [Sve08, §3.3]
-/
instance : 𝗥₀ ⊳ 𝗥 where
  trln := R0.cobhamTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

instance : 𝗥 ⊳ 𝗥₀ := DirectInterpretation.ofWeakerThan 𝗥 𝗥₀

/--
$\mathsf{R}_0$ and $\mathsf{R}$ are mutually interpretable.
- [Sve08, §3.3]
-/
instance : 𝗥₀ ⋈ 𝗥 := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{R}$ is essentially undecidable.
- [Hor11, §3]
- [Sve08, §3.3]
-/
instance : (𝗥 : ArithmeticTheory).EssentiallyUndecidable :=
  Theory.EssentiallyUndecidable.of_weakerThan 𝗥₀ 𝗥

end FFL.FirstOrder.Arithmetic

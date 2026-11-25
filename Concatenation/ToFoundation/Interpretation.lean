module

public import Foundation.FirstOrder.LK.Interpretation

/-!
# Direct translations and interpretations

The provability obligations of a direct translation restated in a model, and the transport of
translations and interpretations along weaker and stronger theories.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace DirectTranslation

section models

variable {L₁ : Language} [L₁.Eq] {M : Type*} [Nonempty M] [Tarski.Structure L₁ M]
  [Tarski.Structure.Eq L₁ M]

omit [L₁.Eq] [Tarski.Structure.Eq L₁ M] in
lemma models_domainNonempty_iff (D : Semiformula.Operator L₁ 1) :
    M↓[L₁] ⊧ “∃ x, %D x” ↔ ∃ x : M, D.val ![x] := by
  simp [models_iff]

lemma models_funcDefined_iff {k} (D : Semiformula.Operator L₁ 1)
    (F : Semiformula.Operator L₁ (k + 1)) :
    M↓[L₁] ⊧ ∀¹* “(⋀ i, %D #(i : Fin k)) → ∃! y, %D y ∧ %F y ⋯” ↔
      ∀ e : Fin k → M, (∀ i, D.val ![e i]) → ∃! y : M, D.val ![y] ∧ F.val (y :> e) := by
  simp [models_iff, Function.comp_def, Matrix.constant_eq_singleton]

lemma models_preserveEq_iff (D : Semiformula.Operator L₁ 1) (E : Semiformula.Operator L₁ 2) :
    M↓[L₁] ⊧ “∀ x y, %D x → %D y → (%E x y ↔ x = y)” ↔
      ∀ x y : M, D.val ![x] → D.val ![y] → (E.val ![x, y] ↔ x = y) := by
  simp [models_iff]

end models

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/-- The translation with the same domain, relations and function graphs over a stronger base
theory.
- [HP98, Remark III.1.7] -/
def ofWeakerThan (π : DirectTranslation T L₂) {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] :
    DirectTranslation T' L₂ where
  domain := π.domain
  rel := π.rel
  func := π.func
  domain_nonempty := Entailment.WeakerThan.pbl π.domain_nonempty
  func_defined f := Entailment.WeakerThan.pbl (π.func_defined f)
  preserve_eq := Entailment.WeakerThan.pbl π.preserve_eq

variable {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] (π : DirectTranslation T L₂)

@[simp]
lemma ofWeakerThan_domain : (π.ofWeakerThan (T' := T')).domain = π.domain := rfl

@[simp]
lemma ofWeakerThan_rel {k} (R : L₂.Rel k) : (π.ofWeakerThan (T' := T')).rel R = π.rel R := rfl

@[simp]
lemma ofWeakerThan_func {k} (f : L₂.Func k) : (π.ofWeakerThan (T' := T')).func f = π.func f :=
  rfl

@[simp]
lemma ofWeakerThan_varEqual {ξ n} (t : Semiterm L₂ ξ n) :
    (π.ofWeakerThan (T' := T')).varEqual t = π.varEqual t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => simp [DirectTranslation.varEqual, ih]

@[simp]
lemma ofWeakerThan_translate {ξ n} (φ : Semiformula L₂ ξ n) :
    (π.ofWeakerThan (T' := T')).translate φ = π.translate φ := by
  induction φ using Semiformula.rec' with
  | hverum => rfl
  | hfalsum => rfl
  | hrel r v => simp only [translate_rel, translateRel, ofWeakerThan_varEqual,
      ofWeakerThan_domain, ofWeakerThan_rel]
  | hnrel r v => simp only [translate_nrel, translateRel, ofWeakerThan_varEqual,
      ofWeakerThan_domain, ofWeakerThan_rel]
  | hand _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hor _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | hall _ ih => simp [translate_all, DirectTranslation.fal, ih]
  | hexs _ ih => simp [translate_ex, DirectTranslation.exs, ih]

end DirectTranslation

namespace DirectInterpretation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂}

/-- If `T` interprets `U` and `T` is consistent, then `U` is consistent.
- [HP98, Corollary III.1.6] -/
theorem consistent (π : T ⊳ U) [Entailment.Consistent T] : Entailment.Consistent U :=
  Entailment.Consistent.of_unprovable (φ := ⊥) fun h ↦
    Entailment.Consistent.not_bot (𝓢 := T) (by simpa using π.sound h)

/-- If `T` interprets `U` and `T'` extends `T`, then `T'` interprets `U` by the same
translation.
- [Lin03, Chapter 6, §1] -/
abbrev ofWeakerThanLeft (π : T ⊳ U) {T' : Theory L₁} [𝗘𝗤 _ ⪯ T'] [T ⪯ T'] : T' ⊳ U where
  trln := π.trln.ofWeakerThan
  interpret_theory φ hφ := by
    have h : T' ⊢ π.trln.translate φ := Entailment.WeakerThan.pbl (π.interpret_theory φ hφ)
    simpa using h

/-- If `T` interprets `U` and `U'` is weaker than `U`, then `T` interprets `U'` by the same
translation.
- [Lin03, Chapter 6, §1] -/
abbrev ofWeakerThanRight (π : T ⊳ U) {U' : Theory L₂} [U' ⪯ U] : T ⊳ U' where
  trln := π.trln
  interpret_theory _φ hφ := π.sound (Entailment.WeakerThan.pbl (Entailment.by_axm hφ))

end DirectInterpretation

end FFL.FirstOrder

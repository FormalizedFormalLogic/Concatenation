module

public import AlphaCentauri.Interpretability.Basic

/-!
# Definitional equivalence

Definitional equivalence, or synonymy, of first-order theories.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

/--
Two translations of `L₂` into `T` are equivalent if `T` proves that they have the same domain, and
that on it they define the same relations and the same graphs of functions.
-/
structure Equivalent (π ρ : DirectTranslation T L₂) : Prop where
  domain : T ⊢ “∀ x, %(π.domain) x ↔ %(ρ.domain) x”
  rel {k} (R : L₂.Rel k) :
    T ⊢ ∀¹* “(⋀ i, %(π.domain) #(i : Fin k)) → (%(π.rel R) ⋯ ↔ %(ρ.rel R) ⋯)”
  func {k} (f : L₂.Func k) :
    T ⊢ ∀¹* “(⋀ i, %(π.domain) #(i : Fin (k + 1))) → (%(π.func f) ⋯ ↔ %(ρ.func f) ⋯)”

section

variable {V : Type*} [Nonempty V] [Tarski.Structure L₁ V] {D D' : Semiformula.Operator L₁ 1}

omit [L₁.Eq] in
lemma models_domainIff_iff : V↓[L₁] ⊧ “∀ x, %D x ↔ %D' x” ↔ ∀ x : V, D.val ![x] ↔ D'.val ![x] := by
  simp [models_iff]

omit [L₁.Eq] in
lemma models_operatorIff_iff {k} {O O' : Semiformula.Operator L₁ k} :
    V↓[L₁] ⊧ ∀¹* “(⋀ i, %D #(i : Fin k)) → (%O ⋯ ↔ %O' ⋯)” ↔
      ∀ e : Fin k → V, (∀ i, D.val ![e i]) → (O.val e ↔ O'.val e) := by
  simp [models_iff, Function.comp_def, Matrix.constant_eq_singleton]

omit [Nonempty V] in
lemma id_rel_val_iff {k} {R : L₁.Rel k} {e : Fin k → V} :
    ((DirectTranslation.id T).rel R).val e ↔ Tarski.Structure.rel R e := by
  simp [id_rel_def, Semiformula.Operator.val, Semiformula.eval_rel, Function.comp_def]

omit [Nonempty V] in
lemma id_func_val_iff [Tarski.Structure.Eq L₁ V] {k} {f : L₁.Func k} {e : Fin (k + 1) → V} :
    ((DirectTranslation.id T).func f).val e ↔ e 0 = Tarski.Structure.func f fun i ↦ e i.succ := by
  simp [id_func_def, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.eval_rel, Function.comp_def]

end

end DirectTranslation

/--
A definitional equivalence, or synonymy, of `T` and `U`: interpretations of each in the other whose
two composites are, up to provable equivalence, the identity translations. Both interpretations
translate equality by equality, and they are unrelativized since the identity translations are.
- [Mur24a, §5]
-/
structure DefinitionalEquivalence {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T]
    (U : Theory L₂) [𝗘𝗤 _ ⪯ U] extends T ⋈ U where
  equivalent_id_left : (l.comp r).trln.Equivalent (.id T)
  equivalent_id_right : (r.comp l).trln.Equivalent (.id U)

namespace DefinitionalEquivalence

open DirectTranslation DirectInterpretation Semiformula

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T] {U : Theory L₂} [𝗘𝗤 _ ⪯ U]

/-- Definitional equivalence is symmetric. -/
abbrev symm (π : DefinitionalEquivalence T U) : DefinitionalEquivalence U T where
  toMutualDirectInterpretation := π.toMutualDirectInterpretation.symm
  equivalent_id_left := π.equivalent_id_right
  equivalent_id_right := π.equivalent_id_left

variable (π : DefinitionalEquivalence T U)

/-- The interpretations of a definitional equivalence are unrelativized. -/
lemma provable_domain : T ⊢ “∀ x, %(π.r.trln.domain) x” :=
  Theory.Proof.complete_on_eq_models.{_, 0} _ fun V _ _ _ hT ↦ by
    suffices ∀ x : V, π.r.trln.Dom x by simpa [models_iff] using! this
    intro x
    have h := models_domainIff_iff.mp (models_of_provable hT π.equivalent_id_left.domain) x
    obtain ⟨z, rfl⟩ := (compDirectTranslation_Dom_iff π.l.trln π.r).mp <| h.mpr <| id_Dom x
    simp

/--
A formula translated by the one and then by the other interpretation of a definitional equivalence
is provably equivalent to itself.
-/
theorem provable_translate_translate {n} (φ : Semisentence L₁ n) :
    T ⊢ ∀¹* (π.r.translate (π.l.translate φ) 🡘 φ) :=
  Theory.Proof.complete_on_eq_models.{_, 0} _ fun V _ _ _ hT ↦ by
    suffices ∀ e : Fin n → V, V ⊧/e (π.r.translate (π.l.translate φ)) ↔ V ⊧/e φ by
      simpa [models_iff] using this
    intro e
    have : (π.r.Model V)↓[L₂] ⊧* U := π.r.model_models_theory hT
    let ρ := π.l.comp π.r
    have h := π.equivalent_id_left
    have hD (x : V) : ρ.trln.Dom x ↔ (DirectTranslation.id T).Dom x :=
      models_domainIff_iff.mp (models_of_provable hT h.domain) x
    choose z hz using fun i ↦ (compDirectTranslation_Dom_iff π.l.trln π.r).mp <|
      (hD <| e i).mpr <| id_Dom <| e i
    have he : e = fun i ↦ ((z i : π.r.Model V) : V) := funext hz
    let e' (i) : ρ.Model V := ⟨e i, (hD _).mpr <| id_Dom _⟩
    let e'' (i) : (DirectTranslation.id T).Model V := ⟨e i, id_Dom _⟩
    calc
      _ ↔ (π.l.Model (π.r.Model V)) ⊧/z φ := by
        rw [he]
        exact Model.evalb_translate_iff.trans Model.evalb_translate_iff
      _ ↔ (ρ.Model V) ⊧/e' φ :=
        (eval_compDirectTranslation_Model_equiv π.l.trln π.r (fun x ↦ x.elim) hz).symm
      _ ↔ V ⊧/e (ρ.trln.translate φ) := Model.evalb_translate_iff.symm
      _ ↔ V ⊧/e ((DirectTranslation.id T).translate φ) := by
        apply eval_translate_congr
        · intro x
          rw [Matrix.fun_eq_vec_one (v := x)]
          exact hD (x 0)
        · exact fun R x ↦ models_operatorIff_iff.mp (models_of_provable hT <| h.rel R) x
            fun i ↦ (hD _).mpr <| id_Dom _
        · exact fun f x ↦ models_operatorIff_iff.mp (models_of_provable hT <| h.func f) x
            fun i ↦ (hD _).mpr <| id_Dom _
      _ ↔ ((DirectTranslation.id T).Model V) ⊧/e'' φ :=
        (Model.evalb_translate_iff (e := e'')).trans Iff.rfl
      _ ↔ V ⊧/e φ :=
        id_models_iff.trans <| iff_of_eq <| congrArg (fun ε ↦ Eval (M := V) e ε φ) <|
          funext fun x ↦ x.elim

end DefinitionalEquivalence

end FFL.FirstOrder

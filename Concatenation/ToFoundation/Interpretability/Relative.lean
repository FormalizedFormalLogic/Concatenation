module

public import AlphaCentauri.Interpretability.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Relative interpretations of several dimensions

Relative interpretations, without parameters and with one piece, whose elements are tuples, taken up
to a definable equivalence relation.
-/

@[expose] public section

namespace FFL.FirstOrder

/--
A translation of `L₂` into `L₁`: an element is a tuple of length `dim`. The first tuple of variables
of the graph of a function is its value.
- [Mur24, §2.2]
- [Mur23, §1.2]
-/
structure RelativeTranslation (L₁ L₂ : Language.{0}) where
  dim : ℕ
  domain : Semisentence L₁ dim
  rel {k} : L₂.Rel k → Semisentence L₁ (k * dim)
  func {k} : L₂.Func k → Semisentence L₁ ((k + 1) * dim)

namespace RelativeTranslation

variable {L₁ L₂ : Language.{0}} (τ : RelativeTranslation L₁ L₂)

/-- The concatenation of `k` tuples. -/
def flatten {M : Type*} {k n : ℕ} (w : Fin k → Fin n → M) : Fin (k * n) → M := fun i ↦
  w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

section

variable (M : Type*) [Tarski.Structure L₁ M]

/-- The tuples in the domain. -/
def Dom : Type _ := {w : Fin τ.dim → M // M ⊧/w τ.domain}

variable {M} {N : Type*} [Tarski.Structure L₂ N]

/--
`f` exhibits `N` as the quotient of the domain of `τ` in `M` by the equivalence relation
`f x = f y`, where the symbols are interpreted by `τ`.
-/
structure Represents (f : τ.Dom M → N) : Prop where
  surjective : Function.Surjective f
  rel {k} (R : L₂.Rel k) (w : Fin k → τ.Dom M) :
    (M ⊧/(flatten fun i ↦ (w i).1) (τ.rel R)) ↔ Tarski.Structure.rel R fun i ↦ f (w i)
  func {k} (F : L₂.Func k) (y : τ.Dom M) (w : Fin k → τ.Dom M) :
    (M ⊧/(flatten (y.1 :> fun i ↦ (w i).1)) (τ.func F)) ↔
      f y = Tarski.Structure.func F fun i ↦ f (w i)

end

variable [L₁.Eq] [L₂.Eq]

/--
`τ` interprets `U` in `T`: it defines a model of `U` in every model of `T`.
- [Mur24, §2.2]
- [Mur23, §1.2]
-/
def Interprets (T : Theory L₁) (U : Theory L₂) : Prop :=
  ∀ (M : Type) [Nonempty M] [Tarski.Structure L₁ M] [Tarski.Structure.Eq L₁ M], M↓[L₁] ⊧* T →
    ∃ (N : Type) (_ : Nonempty N) (_ : Tarski.Structure L₂ N) (_ : Tarski.Structure.Eq L₂ N)
      (f : τ.Dom M → N), τ.Represents f ∧ N↓[L₂] ⊧* U

/-- The formulas translating the symbols are computed from the symbols. -/
def IsComputable [L₁.Encodable] [L₂.Encodable] : Prop :=
  (∃ r : ℕ → ℕ, Computable r ∧ ∀ (k) (R : L₂.Rel k),
    r (Nat.pair k (Encodable.encode R)) = Encodable.encode (τ.rel R)) ∧
  ∃ f : ℕ → ℕ, Computable f ∧ ∀ (k) (F : L₂.Func k),
    f (Nat.pair k (Encodable.encode F)) = Encodable.encode (τ.func F)

end RelativeTranslation

variable {L₁ L₂ : Language.{0}} [L₁.Eq] [L₂.Eq]

/--
`U` is relatively interpretable in `T`, possibly in several dimensions and with a nonabsolute
equality.
- [Mur24, §2.2]
-/
def RelativelyInterprets (T : Theory L₁) (U : Theory L₂) : Prop :=
  ∃ τ : RelativeTranslation L₁ L₂, τ.Interprets T U

/--
`U` is relatively interpretable in `T` by a computable translation.
- [Mur23, §1.1]
-/
def ComputablyInterprets [L₁.Encodable] [L₂.Encodable] (T : Theory L₁) (U : Theory L₂) : Prop :=
  ∃ τ : RelativeTranslation L₁ L₂, τ.IsComputable ∧ τ.Interprets T U

variable {T : Theory L₁} [𝗘𝗤 L₁ ⪯ T] {U : Theory L₂}

open RelativeTranslation in
theorem DirectInterpretation.relativelyInterprets (π : T ⊳ U) : RelativelyInterprets T U := by
  let τ : RelativeTranslation L₁ L₂ :=
    { dim := 1
      domain := π.trln.domain.sentence
      rel {k} R := (π.trln.rel R).operator fun i ↦ #(finProdFinEquiv (i, 0))
      func {k} F := (π.trln.func F).operator fun i ↦ #(finProdFinEquiv (i, 0)) }
  use τ
  intro M _ _ _ hM
  have hdom (w : τ.Dom M) : π.trln.Dom (w.1 0) := by
    have := w.2
    rw [Matrix.fun_eq_vec_one (v := w.1)] at this
    exact this
  use π.trln.Model M, inferInstance, inferInstance, inferInstance, fun w ↦ ⟨w.1 0, hdom w⟩
  and_intros
  · constructor
    · rintro ⟨x, hx⟩
      use ⟨![x], hx⟩
      rfl
    · intro k R w
      simp [τ, flatten, DirectTranslation.Model.rel_iff, Function.comp_def]
    · intro k F y w
      rw [DirectTranslation.Model.func_iff]
      simp only [τ, Semiformula.eval_operator, flatten, Function.comp_def, Semiterm.val_bvar,
        Equiv.symm_apply_apply]
      apply iff_of_eq
      congr 1
      ext i
      cases i using Fin.cases <;> rfl
  · constructor
    intro σ hσ
    exact DirectTranslation.Model.translate_iff.mp <|
      models_of_provable hM (π.interpret_theory σ hσ)

end FFL.FirstOrder

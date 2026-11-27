module

public import Concatenation.ToFoundation.Arithmetic.Pairing
public import Concatenation.ToFoundation.Arithmetic.R0.Cobham
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Weak representability of computable binary functions in $\mathsf{R}_0$

Every computable binary function is weakly representable in $\mathsf{R}_0$, through Cobham's order
and the pairing.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure
open scoped FFL.FirstOrder.Bounding

/--
A $\Delta_0$ formula $\psi(w, \vec{x})$ such that $\exists w\, \psi(w, \vec{x})$ is equivalent in
`ℕ` to the $\Sigma_1$ formula `φ`.
-/
noncomputable def delta0Matrix {k : ℕ} (φ : 𝚺ᴬ₁.Semisentence k) : 𝚺ᴬ₀.Semisentence (k + 1) :=
  .mkSigma φ.sigma_prop.prenex.sigmaInv.val (by simp)

lemma nat_eval_iff_exists_delta0Matrix {k : ℕ} (φ : 𝚺ᴬ₁.Semisentence k) (v : Fin k → ℕ) :
    ℕ ⊧/v φ.val ↔ ∃ w, ℕ ⊧/(w :> v) (delta0Matrix φ).val :=
  ((Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) φ.sigma_prop).choose_spec ℕ v
    Empty.elim).trans (Bounding.Prenex.models_sigmaInv _ _)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗥₀]

/-- The formula that represents the computable binary function `f` through the pairing. -/
noncomputable def cobhamRepresentation₂ (f : ℕ → ℕ → ℕ) : ArithmeticSemisentence 3 :=
  “x y z. ∃ p, !pairDef p x y ∧ !(cobhamRepresentation fun p ↦ f p.unpair.1 p.unpair.2) p z”

@[simp]
lemma eval_cobhamRepresentation₂_numeral_iff {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) {z : V}
    (m n : ℕ) :
    V ⊧/![numeral m, numeral n, z] (cobhamRepresentation₂ f) ↔ z = numeral (f m n) := by
  have hf' : Computable fun p : ℕ ↦ f p.unpair.1 p.unpair.2 :=
    hf.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  have := models_of_provable (M := V) inferInstance <|
    cobhamRepresentation_spec hf' (Nat.pair m n)
  simp [models_iff] at this
  simp [cobhamRepresentation₂, isPair_numeral_iff, this]

section value

variable {f : ℕ → ℕ → ℕ} {V : Type*} [ORingStructure V] {x y z : V}

/--
`z` is the only value of `cobhamRepresentation₂ f` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
@[mk_iff]
structure IsValue₂ (f : ℕ → ℕ → ℕ) (x y z : V) : Prop where
  left_le : x ≤ᶜ z
  right_le : y ≤ᶜ z
  eval : V ⊧/![x, y, z] (cobhamRepresentation₂ f)
  unique (w : V) (hw : V ⊧/![x, y, w] (cobhamRepresentation₂ f)) : w = z

/--
`z` is the only value of `cobhamRepresentation₂ f` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
noncomputable def isValue₂Def (f : ℕ → ℕ → ℕ) : ArithmeticSemisentence 3 :=
  “x y z. !cobhamLEDef x z ∧ !cobhamLEDef y z ∧ !(cobhamRepresentation₂ f) x y z ∧
    ∀ w, !(cobhamRepresentation₂ f) x y w → w = z”

instance isValue₂_defined : ℒₒᵣ-relation₃[V] (IsValue₂ f) via isValue₂Def f :=
  ⟨fun v ↦ by simp [isValue₂Def, isValue₂_iff]⟩

instance isValue₂_definable : ℒₒᵣ-relation₃[V] (IsValue₂ f) := isValue₂_defined.to_definable

/-- A value, or a given element if there is none, exists uniquely. -/
lemma existsUnique_isValue₂_or (f : ℕ → ℕ → ℕ) (x y d : V) :
    ∃! z, IsValue₂ f x y z ∨ (z = d ∧ ∀ w, ¬IsValue₂ f x y w) := by
  by_cases h : ∃ z, IsValue₂ f x y z
  · obtain ⟨z, hz⟩ := h
    use z
    and_intros
    · exact .inl hz
    · rintro w (hw | ⟨-, hw⟩)
      · exact hz.unique w hw.eval
      · exact absurd hz (hw z)
  · push Not at h
    use d
    simp [h]

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma isValue₂_numeral (hf : Computable₂ f) {m n : ℕ} (hm : m ≤ f m n) (hn : n ≤ f m n) :
    IsValue₂ f (numeral m : V) (numeral n) (numeral (f m n)) where
  left_le := by simpa using hm
  right_le := by simpa using hn
  eval := by simp [hf]
  unique := by simp [hf]

/-- The arguments of a numeral value are numerals, and the value is that of `f`. -/
lemma IsValue₂.exists_of_numeral (hf : Computable₂ f) {k : ℕ} (h : IsValue₂ f x y (numeral k)) :
    ∃ m n, x = numeral m ∧ y = numeral n ∧ f m n = k := by
  obtain ⟨m, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.left_le
  obtain ⟨n, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral h.right_le
  use m, n
  simpa [hf, eq_comm] using h.eval

end value

end FFL.FirstOrder.Arithmetic

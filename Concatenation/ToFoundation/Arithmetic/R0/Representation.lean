module

public import Concatenation.ToFoundation.Arithmetic.R0.Cobham
public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Weak representability of computable functions in $\mathsf{R}_0$

Every computable function is weakly representable in $\mathsf{R}_0$, through Cobham's order.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure

/--
The formula $\exists w\,(y \lhd w \wedge \exists v\,(v \lhd w \wedge \varphi(x, y, v)) \wedge
\forall z\,\forall u\,(z \lhd w \to u \lhd w \to \varphi(x, z, u) \to y = z))$, where $\lhd$ is
Cobham's order.
- [Sve08, §3.3, Theorem 3]
-/
def cobhamRepresentation (φ : ArithmeticSemisentence 3) : ArithmeticSemisentence 2 :=
  “x y. ∃ w, !cobhamLE y w ∧ (∃ v, !cobhamLE v w ∧ !φ x y v) ∧
    ∀ z u, !cobhamLE z w → !cobhamLE u w → !φ x z u → y = z”

variable {M : Type*} [ORingStructure M] {φ : ArithmeticSemisentence 3}

@[simp]
lemma eval_cobhamRepresentation {x y : M} :
    M ⊧/![x, y] (cobhamRepresentation φ) ↔ ∃ w, y ⊴ w ∧
      (∃ v, v ⊴ w ∧ M ⊧/![x, y, v] φ) ∧
      ∀ z u, z ⊴ w → u ⊴ w → M ⊧/![x, z, u] φ → y = z := by
  simp [cobhamRepresentation]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma eval_numeral_iff_of_deltaZero (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (n i j : ℕ) :
    M ⊧/![numeral n, numeral i, numeral j] φ ↔ ℕ ⊧/![n, i, j] φ := by
  have e : (numeral ∘ ![n, i, j] : Fin 3 → M) = ![numeral n, numeral i, numeral j] := by
    funext x
    match x with | 0 | 1 | 2 => rfl
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := M) (σ := ∼φ) (by simpa using hφ₀.of_zero)
      (bv := ![n, i, j]) (by simpa using h')
    exact absurd h (by simpa [e] using this)
  · intro h
    simpa [e] using bold_sigma_one_completeness' (M := M) hφ₀.of_zero h

variable {f : ℕ → ℕ}

section

variable (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (hφ : ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ)
include hφ₀ hφ

/--
If the $\Delta_0$ formula $\varphi(x, y, v)$ defines the graph of `f` in `ℕ` up to an existential
quantifier on $v$, then `cobhamRepresentation φ` defines the graph of `f` on numeral arguments in
every model of $\mathsf{R}_0$.
- [Sve08, §3.3, Theorem 3]
-/
lemma eval_cobhamRepresentation_numeral_iff (n : ℕ) (y : M) :
    M ⊧/![numeral n, y] (cobhamRepresentation φ) ↔ y = numeral (f n) := by
  obtain ⟨k, hk⟩ := (hφ n (f n)).mp rfl
  have key : ∀ i j, M ⊧/![numeral n, numeral i, numeral j] φ → i = f n := fun i j h ↦
    (hφ n i).mpr ⟨j, (eval_numeral_iff_of_deltaZero hφ₀ n i j).mp h⟩
  have hkM : M ⊧/![numeral n, numeral (f n), numeral k] φ :=
    (eval_numeral_iff_of_deltaZero hφ₀ n (f n) k).mpr hk
  rw [eval_cobhamRepresentation]
  constructor
  · rintro ⟨w, hyw, ⟨v, hvw, hv⟩, huniq⟩
    rcases cobhamLE_numeral_or (x := w) (max (f n) k) with hw | hw
    · obtain ⟨l, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hw
      obtain ⟨i, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hyw
      obtain ⟨j, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hvw
      rw [key i j hv]
    · exact huniq _ _ (cobhamLE_numeral_of_le (le_max_left _ _) hw)
        (cobhamLE_numeral_of_le (le_max_right _ _) hw) hkM
  · rintro rfl
    use numeral (max (f n) k)
    and_intros
    · simp
    · use numeral k
      and_intros
      · simp
      · exact hkM
    · intro z u hz hu hzu
      obtain ⟨i, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hz
      obtain ⟨j, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hu
      rw [key i j hzu]

/--
`cobhamRepresentation φ` weakly represents `f` in $\mathsf{R}_0$ whenever the $\Delta_0$ formula
$\varphi(x, y, v)$ defines the graph of `f` in `ℕ` up to an existential quantifier on $v$.
- [Sve08, §3.3, Theorem 3]
-/
theorem cobhamRepresentation_spec (n : ℕ) :
    𝗥₀ ⊢ “∀ y, !(cobhamRepresentation φ) ↑n y ↔ y = ↑(f n)” := by
  apply complete.{0}
  intro M _ _
  simpa [models_iff] using eval_cobhamRepresentation_numeral_iff hφ₀ hφ n

end

/--
Every computable function is weakly representable in $\mathsf{R}_0$.
- [Sve08, §3.3, Theorem 3]
-/
theorem exists_cobhamRepresentation (hf : Computable f) :
    ∃ γ : ArithmeticSemisentence 2, ∀ n, 𝗥₀ ⊢ “∀ y, !γ ↑n y ↔ y = ↑(f n)” := by
  let F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (f (v.get 0))
  have hF : Nat.Partrec' F := Nat.Partrec'.of_part <| hf.comp (Primrec.to_comp (by primrec))
  have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (codeOfPartrec' F) := by simp [codeOfPartrec']
  obtain ⟨ψ, hψ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hσ
  let φ : ArithmeticSemisentence 3 := “x y v. !ψ.sigmaInv.val v y x”
  have hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ := by simp [φ]
  use cobhamRepresentation φ
  apply cobhamRepresentation_spec hφ₀
  intro n m
  have := (codeOfPartrec'_spec hF (y := m) (v := ![n])).symm.trans
    ((hψ ℕ (m :> ![n]) Empty.elim).trans (ψ.models_sigmaInv _))
  simpa [F, φ] using this

end FFL.FirstOrder.Arithmetic.R0

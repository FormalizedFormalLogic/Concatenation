module

public import Concatenation.ToFoundation.Arithmetic.R0.Cobham
public import Foundation.FirstOrder.Arithmetic.IOpen.Basic
public import Foundation.FirstOrder.Arithmetic.Prenex
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Weak representability of computable functions in $\mathsf{R}_0$

Every computable function is weakly representable in $\mathsf{R}_0$, through Cobham's order.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure

/--
The formula $\exists w\,(y \lhd w \wedge \exists v\,(v \lhd w \wedge \varphi(x, y, v)) \wedge
\forall z\,\forall u\,(z \lhd w \to u \lhd w \to \varphi(x, z, u) \to y = z))$, where $\lhd$ is
Cobham's order.
- [Sve08, §3.3, Theorem 3]
-/
def cobhamComparison (φ : ArithmeticSemisentence 3) : ArithmeticSemisentence 2 :=
  “x y. ∃ w, !cobhamLEDef y w ∧ (∃ v, !cobhamLEDef v w ∧ !φ x y v) ∧
    ∀ z u, !cobhamLEDef z w → !cobhamLEDef u w → !φ x z u → y = z”

variable {V : Type*} [ORingStructure V] {φ : ArithmeticSemisentence 3}
  {A : ArithmeticSemisentence 2}

@[simp]
lemma eval_cobhamComparison {x y : V} :
    V ⊧/![x, y] (cobhamComparison φ) ↔ ∃ w, y ⊴ w ∧
      (∃ v, v ⊴ w ∧ V ⊧/![x, y, v] φ) ∧
      ∀ z u, z ⊴ w → u ⊴ w → V ⊧/![x, z, u] φ → y = z := by
  simp [cobhamComparison]

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma eval_numeral_iff_of_deltaZero (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (n i j : ℕ) :
    V ⊧/![numeral n, numeral i, numeral j] φ ↔ ℕ ⊧/![n, i, j] φ := by
  have e : (numeral ∘ ![n, i, j] : Fin 3 → V) = ![numeral n, numeral i, numeral j] := by
    funext x
    match x with | 0 | 1 | 2 => rfl
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := V) (σ := ∼φ) (by simpa using hφ₀.of_zero)
      (bv := ![n, i, j]) (by simpa using h')
    exact absurd h (by simpa [e] using this)
  · intro h
    simpa [e] using bold_sigma_one_completeness' (M := V) hφ₀.of_zero h

lemma eval_numeral_iff_of_deltaZero₂ (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) (i j : ℕ) :
    V ⊧/![numeral i, numeral j] A ↔ ℕ ⊧/![i, j] A := by
  have e : (numeral ∘ ![i, j] : Fin 2 → V) = ![numeral i, numeral j] := by
    funext x
    match x with | 0 | 1 => rfl
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := V) (σ := ∼A) (by simpa using hA.of_zero)
      (bv := ![i, j]) (by simpa using h')
    exact absurd h (by simpa [e] using this)
  · intro h
    simpa [e] using bold_sigma_one_completeness' (M := V) hA.of_zero h

variable {f : ℕ → ℕ}

section

variable (hφ₀ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ) (hφ : ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ)
include hφ₀ hφ

/--
If the $\Delta_0$ formula $\varphi(x, y, v)$ defines the graph of `f` in `ℕ` up to an existential
quantifier on $v$, then `cobhamComparison φ` defines the graph of `f` on numeral arguments in
every model of $\mathsf{R}_0$.
- [Sve08, §3.3, Theorem 3]
-/
lemma eval_cobhamComparison_numeral_iff (n : ℕ) (y : V) :
    V ⊧/![numeral n, y] (cobhamComparison φ) ↔ y = numeral (f n) := by
  obtain ⟨k, hk⟩ := (hφ n (f n)).mp rfl
  have key : ∀ i j, V ⊧/![numeral n, numeral i, numeral j] φ → i = f n := fun i j h ↦
    (hφ n i).mpr ⟨j, (eval_numeral_iff_of_deltaZero hφ₀ n i j).mp h⟩
  have hkV : V ⊧/![numeral n, numeral (f n), numeral k] φ :=
    (eval_numeral_iff_of_deltaZero hφ₀ n (f n) k).mpr hk
  rw [eval_cobhamComparison]
  constructor
  · rintro ⟨w, hyw, ⟨v, hvw, hv⟩, huniq⟩
    rcases cobhamLE_numeral_or (x := w) (max (f n) k) with hw | hw
    · grind [eq_numeral_of_cobhamLE_numeral]
    · exact huniq _ _ (cobhamLE_numeral_of_le (le_max_left _ _) hw)
        (cobhamLE_numeral_of_le (le_max_right _ _) hw) hkV
  · rintro rfl
    use numeral (max (f n) k)
    and_intros
    · simp
    · use numeral k, by simp
    · grind [eq_numeral_of_cobhamLE_numeral]

end

/--
The graph of a computable function is defined in `ℕ` by a $\Delta_0$ formula up to an existential
quantifier.
-/
lemma exists_deltaZero_graph (hf : Computable f) : ∃ φ : ArithmeticSemisentence 3,
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ ∧ ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ := by
  let F : List.Vector ℕ 1 →. ℕ := fun v ↦ Part.some (f (v.get 0))
  have hF : Nat.Partrec' F := Nat.Partrec'.of_part <| hf.comp (Primrec.to_comp (by primrec))
  have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (codeOfPartrec' F) := by simp [codeOfPartrec']
  obtain ⟨ψ, hψ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hσ
  use “x y v. !ψ.sigmaInv.val v y x”
  and_intros
  · simp
  · intro n m
    have := (codeOfPartrec'_spec hF (y := m) (v := ![n])).symm.trans
      ((hψ ℕ (m :> ![n]) Empty.elim).trans (ψ.models_sigmaInv _))
    simpa [F] using this

/--
The formula that represents the computable function `f` through Cobham's order.
- [Sve08, §3.3, Theorem 3]
-/
noncomputable def cobhamRepresentation (f : ℕ → ℕ) : ArithmeticSemisentence 2 :=
  cobhamComparison <| Classical.epsilon fun φ ↦
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 φ ∧ ∀ n m, m = f n ↔ ∃ k, ℕ ⊧/![n, m, k] φ

/--
`cobhamRepresentation f` weakly represents the computable function `f` in $\mathsf{R}_0$.
- [Sve08, §3.3, Theorem 3]
-/
theorem cobhamRepresentation_spec (hf : Computable f) (n : ℕ) :
    𝗥₀ ⊢ “∀ y, !(cobhamRepresentation f) ↑n y ↔ y = ↑(f n)” := by
  obtain ⟨hφ₀, hφ⟩ := Classical.epsilon_spec (exists_deltaZero_graph hf)
  apply complete.{0}
  intro V _ _
  simpa [models_iff, cobhamRepresentation, -eval_cobhamComparison]
    using eval_cobhamComparison_numeral_iff (V := V) hφ₀ hφ n

lemma eval_pairDef_numeral_iff {p : V} (m n : ℕ) :
    V ⊧/![p, numeral m, numeral n] pairDef.val ↔ p = numeral (Nat.pair m n) := by
  simp [pairDef, Nat.pair, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    numeral_mul_numeral, numeral_add_numeral]
  grind

@[simp, grind =]
lemma nat_eval_pairDef {q m n : ℕ} : ℕ ⊧/![q, m, n] pairDef.val ↔ q = Nat.pair m n := by
  simpa using eval_pairDef_numeral_iff (V := ℕ) (p := q) m n

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
  simp [cobhamRepresentation₂, eval_pairDef_numeral_iff, this]

section value

variable {f : ℕ → ℕ → ℕ} {V : Type*} [ORingStructure V] {x y z : V}

/--
`z` is the only value of `cobhamRepresentation₂ f` at `x` and `y`, and `x` and `y` are below `z` in
Cobham's order.
-/
@[mk_iff]
structure IsValue₂ (f : ℕ → ℕ → ℕ) (x y z : V) : Prop where
  left_le : x ⊴ z
  right_le : y ⊴ z
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

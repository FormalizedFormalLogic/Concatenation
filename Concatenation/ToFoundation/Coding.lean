module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax
public import Foundation.FirstOrder.Incompleteness.Church
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Codes of formulas

Quantifying and casting the bound variables of formulas are primitive recursive.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

open Encodable

section

variable {L : Language} [L.Encodable] {ξ : Type*} [Encodable ξ] {n n' : ℕ}

lemma Semiterm.encode_castLE (h : n ≤ n') (t : Semiterm L ξ n) :
    encode (Rew.castLE h t) = encode t := by
  simp only [encode_eq_toNat]
  induction t <;> simp [toNat, Rew.func, toNat_func, *]

lemma Semiformula.encode_castLE (h : n ≤ n') (φ : Semiformula L ξ n) :
    encode (Rew.castLE h ▹ φ) = encode φ := by
  induction φ using rec' generalizing n' <;>
    simp [encode_rel, encode_nrel, encode_verum, encode_falsum, encode_and, encode_or, encode_all,
      encode_ex, Function.comp_def, Semiterm.encode_castLE, ← encode_eq_toNat, *]

end

section inversion

variable {L : Language} [L.Encodable] {n : ℕ} {q r k f v : ℕ}

attribute [local simp] Semiformula.encode_rel Semiformula.encode_nrel Semiformula.encode_verum
  Semiformula.encode_falsum Semiformula.encode_and Semiformula.encode_or Semiformula.encode_all
  Semiformula.encode_ex Semiterm.encode_eq_toNat Semiterm.toNat Nat.pair_eq_pair

namespace Semiformula

variable {φ : Semisentence L n}

lemma exists_eq_and_of_encode_eq (h : encode φ = Nat.pair 4 (Nat.pair q r) + 1) :
    ∃ φ₁ φ₂, φ = φ₁ ⋏ φ₂ ∧ encode φ₁ = q ∧ encode φ₂ = r := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h
  | φ₁ ⋏ φ₂ =>
    simp only [Semiformula.encode_and, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, φ₂, rfl, h.2⟩

lemma exists_eq_or_of_encode_eq (h : encode φ = Nat.pair 5 (Nat.pair q r) + 1) :
    ∃ φ₁ φ₂, φ = φ₁ ⋎ φ₂ ∧ encode φ₁ = q ∧ encode φ₂ = r := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | ∀¹ _ | ∃¹ _ => simp at h
  | φ₁ ⋎ φ₂ =>
    simp only [Semiformula.encode_or, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, φ₂, rfl, h.2⟩

lemma exists_eq_all_of_encode_eq (h : encode φ = Nat.pair 6 q + 1) :
    ∃ φ₁, φ = ∀¹ φ₁ ∧ encode φ₁ = q := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∃¹ _ => simp at h
  | ∀¹ φ₁ =>
    simp only [Semiformula.encode_all, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, rfl, h.2⟩

lemma exists_eq_ex_of_encode_eq (h : encode φ = Nat.pair 7 q + 1) :
    ∃ φ₁, φ = ∃¹ φ₁ ∧ encode φ₁ = q := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ => simp at h
  | ∃¹ φ₁ =>
    simp only [Semiformula.encode_ex, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, rfl, h.2⟩

lemma eq_falsum_of_encode_eq (h : encode φ = Nat.pair 3 0 + 1) : φ = ⊥ := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h
  | ⊥ => rfl

lemma exists_eq_rel_of_encode_eq (h : encode φ = Nat.pair 0 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (R : L.Rel k) (t : Fin k → ClosedSemiterm L n), φ = .rel R t ∧ encode R = f ∧
      Matrix.vecToNat (fun i ↦ encode (t i)) = v := by
  match φ with
  | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h
  | .rel R t =>
    simp only [Semiformula.encode_rel, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨R, t, rfl, h⟩

lemma exists_eq_nrel_of_encode_eq (h : encode φ = Nat.pair 1 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (R : L.Rel k) (t : Fin k → ClosedSemiterm L n), φ = .nrel R t ∧ encode R = f ∧
      Matrix.vecToNat (fun i ↦ encode (t i)) = v := by
  match φ with
  | .rel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ => simp at h
  | .nrel R t =>
    simp only [Semiformula.encode_nrel, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨R, t, rfl, h⟩

end Semiformula

namespace Semiterm

variable {t : ClosedSemiterm L n}

lemma exists_eq_bvar_of_encode_eq {i : ℕ} (h : encode t = Nat.pair 0 i + 1) :
    ∃ x : Fin n, t = #x ∧ x = i := by
  match t with
  | #x => exact ⟨x, rfl, by simpa using h⟩
  | .func _ _ => simp at h

lemma exists_eq_func_of_encode_eq (h : encode t = Nat.pair 2 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (F : L.Func k) (u : Fin k → ClosedSemiterm L n), t = .func F u ∧ encode F = f ∧
      Matrix.vecToNat (fun i ↦ encode (u i)) = v := by
  match t with
  | #x => simp at h
  | .func F u =>
    simp only [Semiterm.encode_eq_toNat, Semiterm.toNat, Nat.add_right_cancel_iff,
      Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨F, u, rfl, h⟩

end Semiterm

end inversion

section

variable {L : Language} [L.Encodable] [L.Primcodable] {ξ : Type*} [Primcodable ξ] {n n' : ℕ}

namespace Semiformula

lemma primrec_all : Primrec fun φ : Semiformula L ξ (n + 1) ↦ ∀¹ φ :=
  Primrec.encode_iff.mp <| Primrec.of_eq
    (f := fun φ : Semiformula L ξ (n + 1) ↦ Nat.pair 6 (encode φ) + 1)
    (by primrec) fun φ ↦ (encode_all φ).symm

lemma primrec_ex : Primrec fun φ : Semiformula L ξ (n + 1) ↦ ∃¹ φ :=
  Primrec.encode_iff.mp <| Primrec.of_eq
    (f := fun φ : Semiformula L ξ (n + 1) ↦ Nat.pair 7 (encode φ) + 1)
    (by primrec) fun φ ↦ (encode_ex φ).symm

lemma primrec_castLE (h : n ≤ n') :
    Primrec fun φ : Semiformula L ξ n ↦ (Rew.castLE h ▹ φ : Semiformula L ξ n') :=
  Primrec.encode_iff.mp <| Primrec.encode.of_eq fun φ ↦ (encode_castLE h φ).symm

end Semiformula

/-- The range of a primitive recursive sequence of sentences is recursively enumerable. -/
lemma Theory.RE.range [L.DecidableEq] {f : ℕ → Sentence L} (hf : Primrec f) :
    Theory.RE (Set.range f) :=
  ⟨REPred.projection (p := fun x : Sentence L × ℕ ↦ f x.2 = x.1) <|
    (PrimrecPred.computablePred <| Primrec.eq.comp (hf.comp Primrec.snd) Primrec.fst).to_re⟩

end

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

lemma computable_subst_quote_self :
    Computable fun σ : ArithmeticSemisentence 1 ↦ (σ/[⌜σ⌝] : ArithmeticSentence) := by
  have : Computable₂ fun σ π : ArithmeticSemisentence 1 ↦ (σ/[⌜π⌝] : ArithmeticSentence) :=
    computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ)) (by definability)
      fun σ τ ↦ by simp [← Sentence.quote_eq_encode_nat, substNumeral_app_quote]
  exact this.comp Computable.id Computable.id

end FFL.FirstOrder.Arithmetic

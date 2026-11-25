module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Primitive recursive operations on formulas

Quantifying and casting the bound variables are primitive recursive, and the range of a primitive
recursive sequence of sentences is recursively enumerable.
-/

@[expose] public section

namespace FFL.FirstOrder

open Encodable

section

variable {L : Language} [L.Encodable] {ξ : Type*} [Encodable ξ] {n n' : ℕ}

lemma Semiterm.encode_castLE (h : n ≤ n') (t : Semiterm L ξ n) :
    encode (Rew.castLE h t) = encode t := by
  simp only [encode_eq_toNat]
  induction t with
  | bvar x => simp [toNat]
  | fvar x => simp [toNat]
  | func f v ih => simp [Rew.func, toNat_func, ih]

lemma Semiformula.encode_castLE (φ : Semiformula L ξ n) :
    ∀ {n' : ℕ} (h : n ≤ n'), encode (Rew.castLE h ▹ φ) = encode φ := by
  induction φ using rec' with
  | hverum => intro n' h; rfl
  | hfalsum => intro n' h; rfl
  | hrel r v =>
    intro n' h
    simp [encode_rel, Function.comp_def, Semiterm.encode_castLE]
  | hnrel r v =>
    intro n' h
    simp [encode_nrel, Function.comp_def, Semiterm.encode_castLE]
  | hand φ ψ ihφ ihψ =>
    intro n' h
    simp [encode_and, ← encode_eq_toNat, ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
    intro n' h
    simp [encode_or, ← encode_eq_toNat, ihφ, ihψ]
  | hall φ ih =>
    intro n' h
    simp [encode_all, ← encode_eq_toNat, ih]
  | hexs φ ih =>
    intro n' h
    simp [encode_ex, ← encode_eq_toNat, ih]

end

section

variable {L : Language} [L.Encodable] [L.Primcodable] {ξ : Type*} [Primcodable ξ] {n n' : ℕ}

namespace Semiformula

theorem primrec_all : Primrec fun φ : Semiformula L ξ (n + 1) ↦ ∀¹ φ :=
  Primrec.encode_iff.mp <| Primrec.of_eq
    (f := fun φ : Semiformula L ξ (n + 1) ↦ Nat.pair 6 (encode φ) + 1)
    (by primrec) fun φ ↦ (encode_all φ).symm

theorem primrec_ex : Primrec fun φ : Semiformula L ξ (n + 1) ↦ ∃¹ φ :=
  Primrec.encode_iff.mp <| Primrec.of_eq
    (f := fun φ : Semiformula L ξ (n + 1) ↦ Nat.pair 7 (encode φ) + 1)
    (by primrec) fun φ ↦ (encode_ex φ).symm

theorem primrec_castLE (h : n ≤ n') :
    Primrec fun φ : Semiformula L ξ n ↦ (Rew.castLE h ▹ φ : Semiformula L ξ n') :=
  Primrec.encode_iff.mp <| Primrec.encode.of_eq fun φ ↦ (encode_castLE φ h).symm

end Semiformula

/-- The range of a primitive recursive sequence of sentences is recursively enumerable. -/
lemma Theory.RE.range [L.DecidableEq] {f : ℕ → Sentence L} (hf : Primrec f) :
    Theory.RE (Set.range f) :=
  ⟨REPred.projection (p := fun x : Sentence L × ℕ ↦ f x.2 = x.1) <|
    (PrimrecPred.computablePred <| Primrec.eq.comp (hf.comp Primrec.snd) Primrec.fst).to_re⟩

end

end FFL.FirstOrder

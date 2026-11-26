module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
public import Mathlib.Data.Fintype.Sum

/-!
# Codes of formulas and languages

Quantifying and casting the bound variables of formulas are primitive recursive, and the internal
substitution of a closed term agrees with the substitution. The symbols of the sum of two languages
are primitive-recursively coded if those of the summands are.
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

lemma Semiformula.encode_castLE (φ : Semiformula L ξ n) :
    ∀ {n' : ℕ} (h : n ≤ n'), encode (Rew.castLE h ▹ φ) = encode φ := by
  induction φ using rec' <;> intro n' h <;>
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
  Primrec.encode_iff.mp <| Primrec.encode.of_eq fun φ ↦ (encode_castLE φ h).symm

end Semiformula

/-- The range of a primitive recursive sequence of sentences is recursively enumerable. -/
lemma Theory.RE.range [L.DecidableEq] {f : ℕ → Sentence L} (hf : Primrec f) :
    Theory.RE (Set.range f) :=
  ⟨REPred.projection (p := fun x : Sentence L × ℕ ↦ f x.2 = x.1) <|
    (PrimrecPred.computablePred <| Primrec.eq.comp (hf.comp Primrec.snd) Primrec.fst).to_re⟩

end

end FFL.FirstOrder

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {L : Language} [L.Encodable]
  [L.LORDefinable]

lemma substs1_app_quote (σ : Semisentence L 1) (t : ClosedSemiterm L 0) :
    substs1 L (⌜t⌝ : V) ⌜σ⌝ = ⌜(σ/[t] : Sentence L)⌝ := by
  simp [substs1, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]
  rfl

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Language

variable {L₁ L₂ : Language} [L₁.Encodable] [L₂.Encodable]

instance : (L₁.add L₂).Encodable where
  func k := inferInstanceAs (Encodable (L₁.Func k ⊕ L₂.Func k))
  rel k := inferInstanceAs (Encodable (L₁.Rel k ⊕ L₂.Rel k))

/-- The code of the sum of two options, given by their codes, at the code `e`. -/
def sumCode (a b : ℕ → ℕ) (e : ℕ) : ℕ :=
  bif e.bodd then bif b e.div2 == 0 then 0 else 2 * b e.div2
  else bif a e.div2 == 0 then 0 else 2 * a e.div2 - 1

lemma encode_decode_sum {α β : Type*} [Encodable α] [Encodable β] (e : ℕ) :
    Encodable.encode (Encodable.decode e : Option (α ⊕ β)) =
      sumCode (fun e ↦ Encodable.encode (Encodable.decode e : Option α))
        (fun e ↦ Encodable.encode (Encodable.decode e : Option β)) e := by
  change Encodable.encode (Encodable.decodeSum e : Option (α ⊕ β)) = _
  unfold Encodable.decodeSum sumCode
  cases e.bodd
  · cases h' : (Encodable.decode e.div2 : Option α) <;> simp [h']; omega
  · cases h' : (Encodable.decode e.div2 : Option β) <;> simp [h']; omega

lemma primrec_sumCode {a b : ℕ → ℕ → ℕ} (ha : Primrec₂ a) (hb : Primrec₂ b) :
    Primrec₂ fun k e ↦ sumCode (a k) (b k) e := by
  have hd : Primrec fun p : ℕ × ℕ ↦ p.2.div2 := Primrec.nat_div2.comp .snd
  have ha' := ha.comp Primrec.fst hd
  have hb' := hb.comp Primrec.fst hd
  apply Primrec.cond (Primrec.nat_bodd.comp .snd)
  · exact Primrec.cond (Primrec.beq.comp hb' (.const 0)) (.const 0)
      (Primrec.nat_mul.comp (.const 2) hb')
  · exact Primrec.cond (Primrec.beq.comp ha' (.const 0)) (.const 0)
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp (.const 2) ha') (.const 1))

instance [L₁.Primcodable] [L₂.Primcodable] : (L₁.add L₂).Primcodable where
  func := (primrec_sumCode Primcodable.func Primcodable.func).of_eq
    fun _ _ ↦ (encode_decode_sum _).symm
  rel := (primrec_sumCode Primcodable.rel Primcodable.rel).of_eq
    fun _ _ ↦ (encode_decode_sum _).symm

instance [L₁.Finite] [L₂.Finite] : (L₁.add L₂).Finite where
  func :=
    have := Finite.func (L := L₁)
    have := Finite.func (L := L₂)
    Fintype.ofEquiv _ (Equiv.sigmaSumDistrib L₁.Func L₂.Func).symm
  rel :=
    have := Finite.rel (L := L₁)
    have := Finite.rel (L := L₂)
    Fintype.ofEquiv _ (Equiv.sigmaSumDistrib L₁.Rel L₂.Rel).symm

end FFL.FirstOrder.Language

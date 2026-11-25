module

public import Concatenation.Biteral
public import Concatenation.ToFoundation.AddCoding
public import Concatenation.ToFoundation.Bootstrapping
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Coding of the language of concatenation

The symbols of `ℒ⌢` are primitive-recursively coded and $\Delta_0$-definable in arithmetic, so
that Foundation's computability arguments on formulas apply to `ℒ⌢`.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Language.Concatenation

instance : (ℒ⌢).Primcodable where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦
        if (p.1 = 0 ∧ p.2 < 2) ∨ (p.1 = 2 ∧ p.2 = 0) then p.2 + 1 else 0 := by
      primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     0 => rfl
    |     0,     1 => rfl
    |     0, _ + 2 => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

lemma mem_range_encode_func_iff {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒ⌢).Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨
    (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    rcases f <;> simp <;> rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Func.zero; rfl
    · use Func.one; rfl
    · use Func.concat; rfl

lemma mem_range_encode_rel_iff {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒ⌢).Rel k → ℕ) ↔ k = 2 ∧ r = 0 := by
  constructor
  · rintro ⟨r, rfl⟩
    rcases r; simp; rfl
  · rintro ⟨rfl, rfl⟩
    use Rel.eq; rfl

instance : (ℒ⌢).LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. k = 2 ∧ r = 0”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! mem_range_encode_rel_iff

end Language.Concatenation

namespace Language.PrefixRel

instance : prefixRel.Primcodable where
  func := by
    apply (Primrec.const 0 : Primrec fun _ : ℕ × ℕ ↦ 0).of_eq
    rintro ⟨k, e⟩
    simp [Encodable.decode]
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => rfl
    |     1,     _ => rfl
    |     2,     0 => rfl
    |     2, _ + 1 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

end Language.PrefixRel

namespace Language.ConcatenationPrefix

lemma mem_range_encode_func_iff {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒ⌢⊑).Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 2) ∨
    (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨f | f, rfl⟩
    · rcases f
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr <| .inl ⟨rfl, rfl⟩
      · exact .inr <| .inr ⟨rfl, rfl⟩
    · exact f.elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Sum.inl Concatenation.Func.zero; rfl
    · use Sum.inl Concatenation.Func.one; rfl
    · use Sum.inl Concatenation.Func.concat; rfl

lemma mem_range_encode_rel_iff {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒ⌢⊑).Rel k → ℕ) ↔ (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨r | r, rfl⟩
    · rcases r
      exact .inl ⟨rfl, rfl⟩
    · rcases r
      exact .inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Sum.inl Concatenation.Rel.eq; rfl
    · use Sum.inr PrefixRel.pref; rfl

instance : (ℒ⌢⊑).LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 2) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! mem_range_encode_rel_iff

end Language.ConcatenationPrefix

namespace Language

instance : unit.{0}.Encodable where
  func := fun k ↦ inferInstanceAs (Encodable (Constant.Func PUnit k))
  rel := fun _ ↦ inferInstanceAs (Encodable PEmpty)

instance : unit.{0}.Primcodable where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 0 ∧ p.2 = 0 then 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     0 => rfl
    |     0, _ + 1 => rfl
    | _ + 1,     _ => rfl
  rel := by
    apply (Primrec.const 0 : Primrec fun _ : ℕ × ℕ ↦ 0).of_eq
    exact fun _ ↦ rfl

end Language

namespace Concatenation

/--
The closed term naming `n`: the letter $0$ for $n = 0$, the string of $n$ letters $1$ otherwise.
- [Gan09, §1, Definition 2]
-/
def numeralTerm : ℕ → ClosedSemiterm ℒ⌢ 0
  | 0 => ‘!!(op(0).const)’
  | 1 => ‘!!(op(1).const)’
  | n + 2 => ‘!!(numeralTerm (n + 1)) ⌢ !!(op(1).const)’

@[simp]
lemma numeralTerm_zero : numeralTerm 0 = ‘!!(op(0).const)’ := rfl

@[simp]
lemma numeralTerm_one : numeralTerm 1 = ‘!!(op(1).const)’ := rfl

@[simp]
lemma numeralTerm_add_two (n : ℕ) :
    numeralTerm (n + 2) = ‘!!(numeralTerm (n + 1)) ⌢ !!(op(1).const)’ := rfl

lemma numeralTerm_add_one_eq_biteral (n : ℕ) :
    numeralTerm (n + 1) = biteral ⟨true, List.replicate n true⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [biteral, List.replicate_succ', List.foldl_append] at ih ⊢
    rw [← ih]
    rfl

lemma encode_numeralTerm_add_two (n : ℕ) :
    Encodable.encode (numeralTerm (n + 2)) = Nat.pair 2 (Nat.pair 2 (Nat.pair 0
      (Nat.pair (Encodable.encode (numeralTerm (n + 1)))
        (Nat.pair (Encodable.encode (numeralTerm 1)) 0 + 1) + 1))) + 1 :=
  rfl

lemma primrec_encode_numeralTerm : Primrec fun n ↦ Encodable.encode (numeralTerm n) := by
  have hstep : Primrec₂ fun (_ a : ℕ) ↦ Nat.pair 2 (Nat.pair 2 (Nat.pair 0
      (Nat.pair a (Nat.pair (Encodable.encode (numeralTerm 1)) 0 + 1) + 1))) + 1 := by
    primrec
  have hrec (n : ℕ) : Nat.rec (Encodable.encode (numeralTerm 1)) (fun (_ a : ℕ) ↦
      Nat.pair 2 (Nat.pair 2 (Nat.pair 0
        (Nat.pair a (Nat.pair (Encodable.encode (numeralTerm 1)) 0 + 1) + 1))) + 1) n =
        Encodable.encode (numeralTerm (n + 1)) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [encode_numeralTerm_add_two, ← ih]
  exact (Primrec.nat_casesOn₁ (Encodable.encode (numeralTerm 0)) (Primrec.nat_rec₁ _ hstep)).of_eq
    fun | 0 => rfl | n + 1 => hrec n

lemma computable_subst_numeralTerm_encode :
    Computable fun σ : Semisentence ℒ⌢ 1 ↦
      (σ/[numeralTerm (Encodable.encode σ)] : Sentence ℒ⌢) := by
  have hc : 𝚺ᴬ₁-Function₁ fun n ↦ Encodable.encode (numeralTerm n) :=
    Arithmetic.computable_iff_sigma1.mp primrec_encode_numeralTerm.to_comp
  apply Arithmetic.computable_iff_sigma1_simulate
    (f := fun e ↦ Arithmetic.Bootstrapping.substs1 ℒ⌢ (Encodable.encode (numeralTerm e)) e)
    (by definability)
  intro σ
  have ht : Encodable.encode (numeralTerm (Encodable.encode σ)) =
      (⌜numeralTerm (Encodable.encode σ)⌝ : ℕ) := by
    simp [Semiterm.empty_quote_eq_encode]
  rw [ht, ← Sentence.quote_eq_encode_nat, Arithmetic.Bootstrapping.substs1_app_quote,
    Sentence.quote_eq_encode_nat]

end Concatenation

end FFL.FirstOrder

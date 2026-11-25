module

public import Concatenation.ToFoundation.Arithmetic.Presburger

/-!
# Presburger arithmetic

The language of $0$, $1$, addition and order, and the decidability of the theory of the natural
numbers in it.
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

namespace Language

namespace Presburger

inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2

inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end Presburger

/-- Language of Presburger arithmetic: $0$, $1$, addition and order. -/
@[reducible]
def presburger : Language where
  Func := Presburger.Func
  Rel := Presburger.Rel

namespace Presburger

instance (k) : DecidableEq (Presburger.Func k) := fun a b ↦ by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> {exact instDecidableFalse}

instance (k) : DecidableEq (Presburger.Rel k) := fun a b ↦ by
  rcases a <;> rcases b <;>
  simp only [reduceCtorEq] <;> try {exact instDecidableTrue} <;> {exact instDecidableFalse}

instance (k) : Encodable (Presburger.Func k) where
  encode
    | .zero => 0
    | .one => 1
    | .add => 0
  decode e :=
    match k, e with
    | 0, 0 => some .zero
    | 0, 1 => some .one
    | 2, 0 => some .add
    | _, _ => none
  encodek x := by rcases x <;> simp

instance (k) : Encodable (Presburger.Rel k) where
  encode
    | .eq => 0
    | .lt => 1
  decode e :=
    match k, e with
    | 2, 0 => some .eq
    | 2, 1 => some .lt
    | _, _ => none
  encodek x := by rcases x <;> simp

instance : presburger.DecidableEq := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : presburger.Encodable := ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance : presburger.Zero := ⟨Func.zero⟩

instance : presburger.One := ⟨Func.one⟩

instance : presburger.Add := ⟨Func.add⟩

instance : presburger.Eq := ⟨Rel.eq⟩

instance : presburger.LT := ⟨Rel.lt⟩

instance : presburger.Finite where
  func := ⟨{⟨0, .zero⟩, ⟨0, .one⟩, ⟨2, .add⟩}, by rintro ⟨k, f⟩; cases f <;> simp⟩
  rel := ⟨{⟨2, .eq⟩, ⟨2, .lt⟩}, by rintro ⟨k, r⟩; cases r <;> simp⟩

instance : presburger.Primcodable where
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
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 < 2 then p.2 + 1 else 0 := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2,     1 => rfl
    |     2, _ + 2 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

lemma mem_range_encode_func_iff {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : presburger.Func k → ℕ) ↔ (k = 0 ∧ f = 0) ∨
    (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) := by
  constructor
  · rintro ⟨f, rfl⟩
    rcases f <;> simp <;> rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Func.zero; rfl
    · use Func.one; rfl
    · use Func.add; rfl

lemma mem_range_encode_rel_iff {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : presburger.Rel k → ℕ) ↔ (k = 2 ∧ r = 0) ∨
    (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨r, rfl⟩
    rcases r <;> simp <;> rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · use Rel.eq; rfl
    · use Rel.lt; rfl

instance : presburger.LORDefinable where
  func := .mkSigma “k f. (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0)”
  rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} := by simpa [models_iff] using! mem_range_encode_func_iff
  rel_iff {k c} := by simpa [models_iff] using! mem_range_encode_rel_iff

end Presburger

end Language

namespace PresburgerArithmetic

open Language

section

variable (M : Type*) [Zero M] [One M] [Add M] [LT M]

/-- A type with $0$, $1$, an addition and an order, read as a structure for `presburger`. -/
instance standardModel : Tarski.Structure presburger M where
  func := fun _ f ↦
    match f with
    | Presburger.Func.zero => fun _ ↦ 0
    | Presburger.Func.one => fun _ ↦ 1
    | Presburger.Func.add => fun v ↦ v 0 + v 1
  rel := fun _ r ↦
    match r with
    | Presburger.Rel.eq => fun v ↦ v 0 = v 1
    | Presburger.Rel.lt => fun v ↦ v 0 < v 1

instance : Tarski.Structure.Eq presburger M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero presburger M := ⟨rfl⟩

instance : Tarski.Structure.One presburger M := ⟨rfl⟩

instance : Tarski.Structure.Add presburger M := ⟨fun _ _ ↦ rfl⟩

instance : Tarski.Structure.LT presburger M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

end

open _root_.Presburger in
/-- The definition of the natural numbers with addition and order in the integers. -/
def definition : PresburgerDefinition presburger where
  domain := .le (.ofInt 0) (.var 0)
  func {k} f :=
    match k, f with
    | _, .zero => .eq (.var 0) (.ofInt 0)
    | _, .one => .eq (.var 0) (.ofInt 1)
    | _, .add => .eq (.var 0) (.var 1 + .var 2)
  rel {k} r :=
    match k, r with
    | _, .eq => .eq (.var 0) (.var 1)
    | _, .lt => .lt (.var 0) (.var 1)

lemma defines_definition : definition.Defines fun x : ℕ ↦ (x : ℤ) where
  injective := Nat.cast_injective
  domain_iff z := by
    constructor
    · intro h
      use z.toNat
      simpa [definition] using h
    · rintro ⟨x, rfl⟩
      simp [definition]
  func_iff {k} f v y := by
    match k, f with
    | _, .zero =>
      change _ ↔ 0 = y
      simp [definition, eq_comm]
    | _, .one =>
      change _ ↔ 1 = y
      simp only [definition, Presburger.Formula.eval_eq]
      simp
      omega
    | _, .add =>
      change _ ↔ v 0 + v 1 = y
      simp only [definition, Presburger.Formula.eval_eq]
      simp
      omega
  rel_iff {k} r v := by
    match k, r with
    | _, .eq =>
      change _ ↔ v 0 = v 1
      simp [definition]
    | _, .lt =>
      change _ ↔ v 0 < v 1
      simp [definition]

/--
The theory of the natural numbers with $0$, $1$, addition and order is decidable.
- [Pre29]
-/
theorem decidable_theory_nat : Entailment.Decidable (Tarski.Structure.theory presburger ℕ) :=
  defines_definition.decidable

end PresburgerArithmetic

end FFL.FirstOrder

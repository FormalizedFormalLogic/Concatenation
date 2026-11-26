module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# Cobham's order on models of $\mathsf{R}_0$

Cobham's order compares every element of a model of $\mathsf{R}_0$ with every numeral.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure
open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {x y : V}

/--
`y` is regular: $0 \le y$, and $v + 1 \le y$ for every $v < y$.
- [Sve08, §3.3]
-/
@[mk_iff]
structure IsRegular (y : V) : Prop where
  zero_le : 0 = y ∨ 0 < y
  add_one_le : ∀ v < y, v + 1 = y ∨ v + 1 < y

/--
`y` is regular: $0 \le y$, and $v + 1 \le y$ for every $v < y$.
- [Sve08, §3.3]
-/
def isRegularDef : 𝚺ᴬ₀.Semisentence 1 := .mkSigma “y. 0 ≤ y ∧ ∀ v < y, v + 1 ≤ y”

instance isRegular_defined : 𝚺ᴬ₀-Predicate[V] IsRegular via isRegularDef := .mk fun v ↦ by
  simp [isRegularDef, isRegular_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

instance isRegular_definable : 𝚺ᴬ₀-Predicate[V] IsRegular := isRegular_defined.to_definable

/--
Cobham's order: $x \le y$, or $y$ is not regular.
- [Sve08, §3.3]
-/
def CobhamLE (x y : V) : Prop := (x = y ∨ x < y) ∨ ¬IsRegular y

@[inherit_doc]
scoped infix:50 " ⊴ " => CobhamLE

/--
Cobham's order: $x \le y$, or $y$ is not regular.
- [Sve08, §3.3]
-/
def cobhamLEDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. x ≤ y ∨ ¬!isRegularDef y”

instance cobhamLE_defined : 𝚺ᴬ₀-Relation[V] CobhamLE via cobhamLEDef := .mk fun v ↦ by
  simp [cobhamLEDef, CobhamLE, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

instance cobhamLE_definable : 𝚺ᴬ₀-Relation[V] CobhamLE := cobhamLE_defined.to_definable

/--
The strict part of Cobham's order.
- [Sve08, §3.3]
-/
def CobhamLT (x y : V) : Prop := x ⊴ y ∧ x ≠ y

/--
The strict part of Cobham's order.
- [Sve08, §3.3]
-/
def cobhamLTDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “x y. !cobhamLEDef x y ∧ x ≠ y”

@[inherit_doc]
scoped infix:50 " ◃ " => CobhamLT

instance cobhamLT_defined : 𝚺ᴬ₀-Relation[V] CobhamLT via cobhamLTDef := .mk fun v ↦ by
  simp [cobhamLTDef, CobhamLT]

instance cobhamLT_definable : 𝚺ᴬ₀-Relation[V] CobhamLT := cobhamLT_defined.to_definable

@[simp, grind .]
lemma cobhamLE_refl (x : V) : x ⊴ x := Or.inl <| Or.inl rfl

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

@[simp, grind =]
lemma numeral_add_one_of_R0 (n : ℕ) : (numeral n : V) + 1 = numeral (n + 1) := by
  simpa using numeral_add_numeral (M := V) n 1

/--
Every numeral is regular.
- [Sve08, §3.3, Lemma 2]
-/
@[grind .]
lemma isRegular_numeral (n : ℕ) : IsRegular (numeral n : V) := by
  constructor
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · right
      simpa using (numeral_lt_numeral_iff (M := V)).mpr hn
  · intro v hv
    rcases lt_numeral_iff.mp hv with ⟨i, rfl⟩
    simp
    omega

/--
Below a numeral, Cobham's order is $\le$.
- [Sve08, §3.3, Lemma 2]
-/
@[grind =]
lemma cobhamLE_numeral_iff {n : ℕ} : x ⊴ numeral n ↔ x = numeral n ∨ x < numeral n := by
  simp [CobhamLE, isRegular_numeral]

lemma exists_eq_numeral_or_numeral_le_of_isRegular (hx : IsRegular x) (k : ℕ) :
    (∃ i < k, x = numeral i) ∨ numeral k = x ∨ numeral k < x := by
  induction k with
  | zero => simpa using hx.zero_le
  | succ k ih =>
    have := hx.add_one_le (numeral k)
    grind

/--
Every element is comparable with every numeral in Cobham's order.
- [Sve08, §3.3, Lemma 2]
-/
lemma cobhamLE_numeral_or (n : ℕ) : x ⊴ numeral n ∨ numeral n ⊴ x := by
  by_cases hx : IsRegular x
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hx n with ⟨i, hi, rfl⟩ | h
    · simp [cobhamLE_numeral_iff, hi]
    · exact .inr <| .inl h
  · exact .inr <| .inr hx

lemma eq_numeral_of_cobhamLE_numeral {n : ℕ} (h : x ⊴ numeral n) :
    ∃ i ≤ n, x = numeral i := by
  rcases cobhamLE_numeral_iff.mp h with rfl | h
  · use n
  · rcases lt_numeral_iff.mp h with ⟨i, rfl⟩
    use i, i.isLt.le

lemma cobhamLE_numeral_of_le {k q : ℕ} {w : V} (hkq : k ≤ q) (h : numeral q ⊴ w) :
    numeral k ⊴ w := by
  by_cases hw : IsRegular w
  · rcases exists_eq_numeral_or_numeral_le_of_isRegular hw k with ⟨i, hi, rfl⟩ | h'
    · simp [CobhamLE, hw] at h
      omega
    · exact Or.inl h'
  · exact Or.inr hw

@[simp, grind =]
lemma numeral_cobhamLE_numeral_iff {k n : ℕ} : (numeral k : V) ⊴ numeral n ↔ k ≤ n := by
  simp [cobhamLE_numeral_iff]
  omega

/--
Below a numeral, the strict part of Cobham's order is $<$.
- [Sve08, §3.3, Lemma 2]
-/
@[grind =]
lemma cobhamLT_numeral_iff {n : ℕ} : CobhamLT x (numeral n) ↔ x < numeral n := by
  have := not_numeral_lt_self (M := V) n
  grind [CobhamLT]

lemma cobhamLT_numeral_iff_exists {n : ℕ} : x ◃ numeral n ↔ ∃ i < n, x = numeral i := by
  simp [cobhamLT_numeral_iff, lt_numeral_iff, Fin.exists_iff]

@[simp, grind =]
lemma nat_cobhamLE_iff {m n : ℕ} : m ⊴ n ↔ m ≤ n := by
  simpa using numeral_cobhamLE_numeral_iff (V := ℕ) (k := m) (n := n)

end FFL.FirstOrder.Arithmetic

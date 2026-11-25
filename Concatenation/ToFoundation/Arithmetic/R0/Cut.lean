module

public import Concatenation.ToFoundation.Arithmetic.R0.Cobham
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Definable cuts in models of $\mathsf{R}_0$

A definable cut on which arithmetic is tame either has a maximum, or is shortened to a cut that is
closed under addition and multiplication and on which a definable family of sets has a limit.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure

variable {M : Type*} [ORingStructure M] {x y z : M}

section pair

/-- The pairing $(a + b + 1) (a + b + 1) + a$. -/
def mkPair (a b : M) : M := (a + b + 1) * (a + b + 1) + a

/-- The pairing $(a + b + 1) (a + b + 1) + a$. -/
def mkPairTerm : ClosedSemiterm ℒₒᵣ 2 := ‘a b. (a + b + 1) * (a + b + 1) + a’

@[simp]
lemma val_subst_mkPairTerm {n : ℕ} {e : Fin n → M} {f : Empty → M}
    {t u : ClosedSemiterm ℒₒᵣ n} :
    (Rew.subst ![t, u] mkPairTerm).val e f = mkPair (t.val e f) (u.val e f) := by
  simp [mkPairTerm, mkPair]

lemma mkPair_inj {a b a' b' : ℕ} : mkPair a b = mkPair a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have : a + b = a' + b' := by
      simp only [mkPair] at h
      rcases lt_trichotomy (a + b) (a' + b') with h' | h' | h'
      · nlinarith
      · exact h'
      · nlinarith
    simp only [mkPair, this] at h
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

lemma mkPair_pos (a b : ℕ) : 0 < mkPair a b := by
  simp [mkPair]

lemma left_lt_mkPair (a b : ℕ) : a < mkPair a b := by
  simp [mkPair]

lemma right_lt_mkPair (a b : ℕ) : b < mkPair a b := by
  simp only [mkPair]
  nlinarith

lemma mkPair_le_mkPair {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    mkPair a b ≤ mkPair a' b' := by
  simp only [mkPair]
  gcongr

lemma mkPair_numeral [M↓[ℒₒᵣ] ⊧* 𝗥₀] (a b : ℕ) :
    mkPair (numeral a : M) (numeral b) = numeral (mkPair a b) := by
  have h : (1 : M) = numeral 1 := by simp
  simp only [mkPair, h, numeral_add_numeral, numeral_mul_numeral]

end pair

section isTame

/-- Cobham's order has the order-theoretic properties of a numeral at `x`. -/
@[mk_iff]
structure IsTame (x : M) : Prop where
  total : ∀ y, x ⊴ y ∨ y ⊴ x
  trans : ∀ y z, z ⊴ y → y ⊴ x → z ⊴ x
  antisymm : ∀ y, x ⊴ y → y ⊴ x → x = y
  zero_le : 0 ⊴ x
  add_one_le : ∀ y, x ⊴ y → x = y ∨ x + 1 ⊴ y
  le_add_one_iff : ∀ y, y ⊴ x + 1 ↔ y ⊴ x ∨ y = x + 1
  not_add_one_le : ¬x + 1 ⊴ x
  add_zero : x + 0 = x
  zero_add : 0 + x = x
  mul_zero : x * 0 = 0
  mul_one : x * 1 = x
  one_mul : 1 * x = x

/-- Cobham's order has the order-theoretic properties of a numeral at `x`. -/
def isTame : ArithmeticSemisentence 1 := “x.
  (∀ y, !cobhamLE x y ∨ !cobhamLE y x) ∧
  (∀ y z, !cobhamLE z y → !cobhamLE y x → !cobhamLE z x) ∧
  (∀ y, !cobhamLE x y → !cobhamLE y x → x = y) ∧
  !cobhamLE 0 x ∧
  (∀ y, !cobhamLE x y → x = y ∨ !cobhamLE (x + 1) y) ∧
  (∀ y, !cobhamLE y (x + 1) ↔ !cobhamLE y x ∨ y = x + 1) ∧
  ¬!cobhamLE (x + 1) x ∧
  x + 0 = x ∧ 0 + x = x ∧ x * 0 = 0 ∧ x * 1 = x ∧ 1 * x = x”

@[simp]
lemma eval_isTame : M ⊧/![x] isTame ↔ IsTame x := by
  simp [isTame, isTame_iff]

/-- Addition and multiplication behave at `x`, `y` and `z` as at numerals. -/
@[mk_iff]
structure IsTame₃ (x y z : M) : Prop where
  add_assoc : x + y + z = x + (y + z)
  mul_assoc : x * y * z = x * (y * z)
  mul_add : x * (y + z) = x * y + x * z
  add_le_add_left : y ⊴ z → x + y ⊴ x + z
  mul_le_mul_left : y ⊴ z → x * y ⊴ x * z
  le_add_right : x ⊴ x + y
  mkPair_le_left : y ⊴ z → mkPair y x ⊴ mkPair z x
  mkPair_le_right : y ⊴ z → mkPair x y ⊴ mkPair x z

/-- Addition and multiplication behave at `x`, `y` and `z` as at numerals. -/
def isTame₃ : ArithmeticSemisentence 3 := “x y z.
  x + y + z = x + (y + z) ∧ x * y * z = x * (y * z) ∧ x * (y + z) = x * y + x * z ∧
  (!cobhamLE y z → !cobhamLE (x + y) (x + z)) ∧ (!cobhamLE y z → !cobhamLE (x * y) (x * z)) ∧
  !cobhamLE x (x + y) ∧
  (!cobhamLE y z → !cobhamLE (!mkPairTerm y x) (!mkPairTerm z x)) ∧
  (!cobhamLE y z → !cobhamLE (!mkPairTerm x y) (!mkPairTerm x z))”

@[simp]
lemma eval_isTame₃ : M ⊧/![x, y, z] isTame₃ ↔ IsTame₃ x y z := by
  simp [isTame₃, isTame₃_iff]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma isTame_numeral (n : ℕ) : IsTame (numeral n : M) where
  total y := (cobhamLE_numeral_or n).symm
  trans y z hz hy := by
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral hy
    obtain ⟨j, hj, rfl⟩ := eq_numeral_of_cobhamLE_numeral hz
    simpa using hj.trans hi
  antisymm y hxy hyx := by
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral hyx
    simpa using le_antisymm (numeral_cobhamLE_numeral_iff.mp hxy) hi
  zero_le := by simpa using numeral_cobhamLE_numeral_iff (M := M) (k := 0) (n := n)
  add_one_le y hy := by
    rw [numeral_add_one]
    rcases cobhamLE_numeral_or (x := y) (n + 1) with h | h
    · obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral h
      simp at hy ⊢
      omega
    · exact .inr h
  le_add_one_iff y := by
    rw [numeral_add_one]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral h
      simp
      omega
    · rintro (h | rfl)
      · obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral h
        simp
        omega
      · simp
  not_add_one_le := by simp [numeral_add_one]
  add_zero := by simpa using numeral_add_numeral (M := M) n 0
  zero_add := by simpa using numeral_add_numeral (M := M) 0 n
  mul_zero := by simpa using numeral_mul_numeral (M := M) n 0
  mul_one := by simpa using numeral_mul_numeral (M := M) n 1
  one_mul := by simpa using numeral_mul_numeral (M := M) 1 n

lemma isTame₃_numeral (k n m : ℕ) : IsTame₃ (numeral k : M) (numeral n) (numeral m) where
  add_assoc := by simp [numeral_add_numeral, Nat.add_assoc]
  mul_assoc := by simp [numeral_mul_numeral, Nat.mul_assoc]
  mul_add := by simp [numeral_mul_numeral, numeral_add_numeral, Nat.mul_add]
  add_le_add_left := by simp [numeral_add_numeral]
  mul_le_mul_left := by
    simp only [numeral_cobhamLE_numeral_iff, numeral_mul_numeral]
    exact Nat.mul_le_mul_left k
  le_add_right := by simp [numeral_add_numeral]
  mkPair_le_left := by
    simp only [numeral_cobhamLE_numeral_iff, mkPair_numeral]
    exact fun h ↦ mkPair_le_mkPair h le_rfl
  mkPair_le_right := by
    simp only [numeral_cobhamLE_numeral_iff, mkPair_numeral]
    exact mkPair_le_mkPair le_rfl

end isTame

section agree

/-- $x \lhd y$ strictly. -/
def CobhamLT (x y : M) : Prop := x ⊴ y ∧ x ≠ y

@[inherit_doc]
scoped infix:50 " ◃ " => CobhamLT

/-- $x \lhd y$ strictly. -/
def cobhamLT : ArithmeticSemisentence 2 := “x y. !cobhamLE x y ∧ x ≠ y”

@[simp]
lemma eval_cobhamLT : M ⊧/![x, y] cobhamLT ↔ x ◃ y := by
  simp [cobhamLT, CobhamLT]

variable {ψ : ArithmeticSemisentence 2} {e i j k m n : M}

/-- The sets defined by `ψ` with the parameters `i` and `j` agree below `m`. -/
def Agree (ψ : ArithmeticSemisentence 2) (m i j : M) : Prop :=
  ∀ e, e ◃ m → (M ⊧/![e, i] ψ ↔ M ⊧/![e, j] ψ)

/-- The sets defined by `ψ` with the parameters `i` and `j` agree below `m`. -/
def agree (ψ : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
  “m i j. ∀ e, !cobhamLT e m → (!ψ e i ↔ !ψ e j)”

@[simp]
lemma eval_agree : M ⊧/![m, i, j] (agree ψ) ↔ Agree ψ m i j := by
  simp [agree, Agree]

/--
The sets defined by `ψ` with the parameters `i` and `j` first differ at `e`, which belongs to the
second one.
-/
@[mk_iff]
structure LeftAt (ψ : ArithmeticSemisentence 2) (e i j : M) : Prop where
  agree : Agree ψ e i j
  left : ¬M ⊧/![e, i] ψ
  right : M ⊧/![e, j] ψ

/--
The sets defined by `ψ` with the parameters `i` and `j` first differ at `e`, which belongs to the
second one.
-/
def leftAt (ψ : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
  “e i j. !(agree ψ) e i j ∧ ¬!ψ e i ∧ !ψ e j”

@[simp]
lemma eval_leftAt : M ⊧/![e, i, j] (leftAt ψ) ↔ LeftAt ψ e i j := by
  simp [leftAt, leftAt_iff]

lemma Agree.symm (h : Agree ψ m i j) : Agree ψ m j i := fun e he ↦ (h e he).symm

lemma Agree.trans (h : Agree ψ m i j) (h' : Agree ψ m j k) : Agree ψ m i k :=
  fun e he ↦ (h e he).trans (h' e he)

end agree

section good

variable {φ : ArithmeticSemisentence 1} {ψ : ArithmeticSemisentence 2}

/--
`x` is good for `φ` and `ψ`: below `x` arithmetic is tame, `φ` holds, and distinct sets defined
by `ψ` have a first difference.
-/
@[mk_iff]
structure IsGood (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (x : M) : Prop where
  isTame : ∀ y, y ⊴ x → IsTame y
  isTame₃ : ∀ w, w ⊴ x → ∀ y z u, y ⊴ w → z ⊴ w → u ⊴ w → IsTame₃ y z u
  eval : ∀ y, y ⊴ x → M ⊧/![y] φ
  agree_or : ∀ m, m ⊴ x → ∀ i j, Agree ψ m i j ∨ ∃ e, e ◃ m ∧ (LeftAt ψ e i j ∨ LeftAt ψ e j i)

/--
`x` is good for `φ` and `ψ`: below `x` arithmetic is tame, `φ` holds, and distinct sets defined
by `ψ` have a first difference.
-/
def isGood (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 := “x.
  (∀ y, !cobhamLE y x → !isTame y) ∧
  (∀ w, !cobhamLE w x → ∀ y z u, !cobhamLE y w → !cobhamLE z w → !cobhamLE u w → !isTame₃ y z u) ∧
  (∀ y, !cobhamLE y x → !φ y) ∧
  ∀ m, !cobhamLE m x → ∀ i j, !(agree ψ) m i j ∨
    ∃ e, !cobhamLT e m ∧ (!(leftAt ψ) e i j ∨ !(leftAt ψ) e j i)”

@[simp]
lemma eval_isGood : M ⊧/![x] (isGood φ ψ) ↔ IsGood φ ψ x := by
  simp [isGood, isGood_iff]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma cobhamLT_numeral_iff {n : ℕ} : x ◃ numeral n ↔ ∃ i < n, x = numeral i := by
  constructor
  · rintro ⟨h, hne⟩
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral h
    use i
    and_intros
    · exact hi.lt_of_ne fun h ↦ hne <| congrArg _ h
    · rfl
  · rintro ⟨i, hi, rfl⟩
    constructor
    · simp [hi.le]
    · simp [hi.ne]

lemma agree_numeral_or (n : ℕ) (i j : M) : Agree ψ (numeral n) i j ∨
    ∃ e, e ◃ numeral n ∧ (LeftAt ψ e i j ∨ LeftAt ψ e j i) := by
  by_cases h : ∃ k < n, ¬(M ⊧/![numeral k, i] ψ ↔ M ⊧/![numeral k, j] ψ)
  · right
    classical
    obtain ⟨hk, hd⟩ := Nat.find_spec h
    have agree : Agree ψ (numeral (Nat.find h)) i j := by
      intro e he
      obtain ⟨l, hl, rfl⟩ := cobhamLT_numeral_iff.mp he
      by_contra H
      exact Nat.find_min h hl ⟨hl.trans hk, H⟩
    use numeral (Nat.find h)
    constructor
    · exact cobhamLT_numeral_iff.mpr ⟨_, hk, rfl⟩
    · by_cases hi : M ⊧/![numeral (Nat.find h), i] ψ
      · right
        exact ⟨agree.symm, by tauto, hi⟩
      · left
        exact ⟨agree, hi, by tauto⟩
  · left
    intro e he
    obtain ⟨k, hk, rfl⟩ := cobhamLT_numeral_iff.mp he
    by_contra H
    exact h ⟨k, hk, H⟩

lemma isGood_numeral (h : ∀ n : ℕ, M ⊧/![numeral n] φ) (n : ℕ) : IsGood φ ψ (numeral n : M) where
  isTame y hy := by
    obtain ⟨i, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hy
    exact isTame_numeral i
  isTame₃ w hw y z u hy hz hu := by
    obtain ⟨i, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hw
    obtain ⟨j, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hy
    obtain ⟨k, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hz
    obtain ⟨l, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hu
    exact isTame₃_numeral j k l
  eval y hy := by
    obtain ⟨i, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hy
    exact h i
  agree_or m hm i j := by
    obtain ⟨k, -, rfl⟩ := eq_numeral_of_cobhamLE_numeral hm
    exact agree_numeral_or k i j

end good

section path

variable {φ : ArithmeticSemisentence 1} {ψ : ArithmeticSemisentence 2} {e i j k m n : M}

/-- `m` is the greatest good element. -/
def IsGreatestGood (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (m : M) : Prop :=
  IsGood φ ψ m ∧ ∀ x, IsGood φ ψ x → x ⊴ m

/-- `m` is the greatest good element. -/
def isGreatestGood (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “m. !(isGood φ ψ) m ∧ ∀ x, !(isGood φ ψ) x → !cobhamLE x m”

@[simp]
lemma eval_isGreatestGood : M ⊧/![m] (isGreatestGood φ ψ) ↔ IsGreatestGood φ ψ m := by
  simp [isGreatestGood, IsGreatestGood]

/--
Cofinally many sets defined by `ψ` with good parameters agree below `m` with the one of parameter
`j`.
-/
def IsCofinal (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (m j : M) : Prop :=
  ∀ k, IsGood φ ψ k → ∃ i, IsGood φ ψ i ∧ k ⊴ i ∧ Agree ψ m i j

/--
Cofinally many sets defined by `ψ` with good parameters agree below `m` with the one of parameter
`j`.
-/
def isCofinal (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 :=
  “m j. ∀ k, !(isGood φ ψ) k → ∃ i, !(isGood φ ψ) i ∧ !cobhamLE k i ∧ !(agree ψ) m i j”

@[simp]
lemma eval_isCofinal : M ⊧/![m, j] (isCofinal φ ψ) ↔ IsCofinal φ ψ m j := by
  simp [isCofinal, IsCofinal]

/-- `j` is leftmost among the cofinal parameters up to agreement below `m`. -/
@[mk_iff]
structure IsLeftmost (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2)
    (m j : M) : Prop where
  isCofinal : IsCofinal φ ψ m j
  not_leftAt : ∀ i, IsCofinal φ ψ m i → ∀ e, e ◃ m → ¬LeftAt ψ e i j

/-- `j` is leftmost among the cofinal parameters up to agreement below `m`. -/
def isLeftmost (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 := “m j.
  !(isCofinal φ ψ) m j ∧ ∀ i, !(isCofinal φ ψ) m i → ∀ e, !cobhamLT e m → ¬!(leftAt ψ) e i j”

@[simp]
lemma eval_isLeftmost : M ⊧/![m, j] (isLeftmost φ ψ) ↔ IsLeftmost φ ψ m j := by
  simp [isLeftmost, isLeftmost_iff]

/-- `j` is leftmost up to agreement below every `m` up to `n`. -/
def IsPath (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (n j : M) : Prop :=
  ∀ m, m ⊴ n → IsLeftmost φ ψ m j

/-- `j` is leftmost up to agreement below every `m` up to `n`. -/
def isPath (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 :=
  “n j. ∀ m, !cobhamLE m n → !(isLeftmost φ ψ) m j”

@[simp]
lemma eval_isPath : M ⊧/![n, j] (isPath φ ψ) ↔ IsPath φ ψ n j := by
  simp [isPath, IsPath]

/-- `e` belongs to the limit of the sets defined by `ψ`. -/
def MemLimit (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (e : M) : Prop :=
  ∃ j, IsPath φ ψ (e + 1) j ∧ M ⊧/![e, j] ψ

/-- `e` belongs to the limit of the sets defined by `ψ`. -/
def memLimit (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “e. ∃ j, !(isPath φ ψ) (e + 1) j ∧ !ψ e j”

@[simp]
lemma eval_memLimit : M ⊧/![e] (memLimit φ ψ) ↔ MemLimit φ ψ e := by
  simp [memLimit, MemLimit]

/-- There is a path of length `n`. -/
def HasPath (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (n : M) : Prop :=
  IsGood φ ψ n ∧ ∃ j, IsPath φ ψ n j

/-- There is a path of length `n`. -/
def hasPath (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “n. !(isGood φ ψ) n ∧ ∃ j, !(isPath φ ψ) n j”

@[simp]
lemma eval_hasPath : M ⊧/![n] (hasPath φ ψ) ↔ HasPath φ ψ n := by
  simp [hasPath, HasPath]

/-- The lengths of paths are closed under the addition of `x`. -/
def IsAddCut (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (x : M) : Prop :=
  HasPath φ ψ x ∧ ∀ y, HasPath φ ψ y → HasPath φ ψ (y + x)

/-- The lengths of paths are closed under the addition of `x`. -/
def isAddCut (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. !(hasPath φ ψ) x ∧ ∀ y, !(hasPath φ ψ) y → !(hasPath φ ψ) (y + x)”

@[simp]
lemma eval_isAddCut : M ⊧/![x] (isAddCut φ ψ) ↔ IsAddCut φ ψ x := by
  simp [isAddCut, IsAddCut]

/-- The elements of `isAddCut φ ψ` are closed under the multiplication by `x`. -/
def IsMulCut (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (x : M) : Prop :=
  IsAddCut φ ψ x ∧ ∀ y, IsAddCut φ ψ y → IsAddCut φ ψ (y * x)

/-- The elements of `isAddCut φ ψ` are closed under the multiplication by `x`. -/
def isMulCut (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. !(isAddCut φ ψ) x ∧ ∀ y, !(isAddCut φ ψ) y → !(isAddCut φ ψ) (y * x)”

@[simp]
lemma eval_isMulCut : M ⊧/![x] (isMulCut φ ψ) ↔ IsMulCut φ ψ x := by
  simp [isMulCut, IsMulCut]

lemma cobhamLE_refl (x : M) : x ⊴ x := Or.inl <| Or.inl rfl

namespace IsGood

lemma tame (hx : IsGood φ ψ x) : IsTame x := hx.isTame x <| cobhamLE_refl x

lemma of_le (hx : IsGood φ ψ x) (h : y ⊴ x) : IsGood φ ψ y where
  isTame z hz := hx.isTame z <| hx.tame.trans y z hz h
  isTame₃ w hw := hx.isTame₃ w <| hx.tame.trans y w hw h
  eval z hz := hx.eval z <| hx.tame.trans y z hz h
  agree_or m hm := hx.agree_or m <| hx.tame.trans y m hm h

lemma exists_le (hx : IsGood φ ψ x) (hy : IsGood φ ψ y) : ∃ z, IsGood φ ψ z ∧ x ⊴ z ∧ y ⊴ z := by
  rcases hx.tame.total y with h | h
  · exact ⟨y, hy, h, cobhamLE_refl y⟩
  · exact ⟨x, hx, cobhamLE_refl x, h⟩

lemma tame₃ (hx : IsGood φ ψ x) (hy : IsGood φ ψ y) (hz : IsGood φ ψ z) : IsTame₃ x y z := by
  obtain ⟨u, hu, hxu, hyu⟩ := hx.exists_le hy
  obtain ⟨v, hv, huv, hzv⟩ := hu.exists_le hz
  exact hv.isTame₃ v (cobhamLE_refl v) x y z (hv.tame.trans u x hxu huv)
    (hv.tame.trans u y hyu huv) hzv

lemma lt_of_lt_of_le (hm : IsGood φ ψ m) (he : e ◃ n) (h : n ⊴ m) : e ◃ m := by
  apply And.intro <| hm.tame.trans n e he.1 h
  rintro rfl
  exact he.2 <| hm.tame.antisymm n he.1 h

lemma lt_add_one_iff (hm : IsGood φ ψ m) : e ◃ m + 1 ↔ e ◃ m ∨ e = m := by
  constructor
  · rintro ⟨h, hne⟩
    by_cases hem : e = m
    · exact .inr hem
    · exact .inl ⟨((hm.tame.le_add_one_iff e).mp h).resolve_right hne, hem⟩
  · have hne : m ≠ m + 1 := fun h ↦ hm.tame.not_add_one_le <| .inl <| .inl h.symm
    rintro (h | rfl)
    · apply And.intro <| (hm.tame.le_add_one_iff e).mpr <| .inl h.1
      rintro rfl
      exact hm.tame.not_add_one_le h.1
    · exact ⟨(hm.tame.le_add_one_iff e).mpr <| .inl <| cobhamLE_refl e, hne⟩

lemma add_one_le (hm : IsGood φ ψ m) (h : e ◃ m) : e + 1 ⊴ m :=
  ((hm.of_le h.1).tame.add_one_le m h.1).resolve_left h.2

end IsGood

lemma Agree.mono (hm : IsGood φ ψ m) (h : n ⊴ m) (hij : Agree ψ m i j) : Agree ψ n i j :=
  fun e he ↦ hij e <| hm.lt_of_lt_of_le he h

lemma LeftAt.congr_left (he : e ◃ n) (h : Agree ψ n j k) (hn : IsGood φ ψ n) (hl : LeftAt ψ e i j) :
    LeftAt ψ e i k :=
  ⟨hl.agree.trans <| h.mono hn he.1, hl.left, (h e he).mp hl.right⟩

lemma IsCofinal.congr (hc : IsCofinal φ ψ n i) (h : Agree ψ n i j) : IsCofinal φ ψ n j :=
  fun k hk ↦
    let ⟨i', hi', hki', ha⟩ := hc k hk
    ⟨i', hi', hki', ha.trans h⟩

lemma IsCofinal.mono (hm : IsGood φ ψ m) (h : n ⊴ m) (hc : IsCofinal φ ψ m i) :
    IsCofinal φ ψ n i :=
  fun k hk ↦
    let ⟨i', hi', hki', ha⟩ := hc k hk
    ⟨i', hi', hki', ha.mono hm h⟩

lemma IsLeftmost.congr (hn : IsGood φ ψ n) (hl : IsLeftmost φ ψ n i) (h : Agree ψ n i j) :
    IsLeftmost φ ψ n j where
  isCofinal := hl.isCofinal.congr h
  not_leftAt i' hi' e he hL := hl.not_leftAt i' hi' e he <| hL.congr_left he h.symm hn

lemma IsLeftmost.agree (hn : IsGood φ ψ n) (hi : IsLeftmost φ ψ n i) (hj : IsLeftmost φ ψ n j) :
    Agree ψ n i j := by
  rcases hn.agree_or n (cobhamLE_refl n) i j with h | ⟨e, he, h | h⟩
  · exact h
  · exact absurd h <| hj.not_leftAt i hi.isCofinal e he
  · exact absurd h <| hi.not_leftAt j hj.isCofinal e he

lemma IsPath.mono (hm : IsGood φ ψ m) (h : n ⊴ m) (hp : IsPath φ ψ m j) : IsPath φ ψ n j :=
  fun k hk ↦ hp k <| hm.tame.trans n k hk h

lemma HasPath.of_le (hm : HasPath φ ψ m) (h : n ⊴ m) : HasPath φ ψ n :=
  let ⟨hm, j, hj⟩ := hm
  ⟨hm.of_le h, j, hj.mono hm h⟩

lemma IsAddCut.of_le (hx : IsAddCut φ ψ x) (h : y ⊴ x) : IsAddCut φ ψ y :=
  have hy := hx.1.of_le h
  ⟨hy, fun z hz ↦ (hx.2 z hz).of_le <| (hz.1.tame₃ hy.1 hx.1.1).add_le_add_left h⟩

lemma IsMulCut.of_le (hx : IsMulCut φ ψ x) (h : y ⊴ x) : IsMulCut φ ψ y :=
  have hy := hx.1.of_le h
  ⟨hy, fun z hz ↦ (hx.2 z hz).of_le <| (hz.1.1.tame₃ hy.1.1 hx.1.1.1).mul_le_mul_left h⟩

lemma IsAddCut.add (hx : IsAddCut φ ψ x) (hy : IsAddCut φ ψ y) : IsAddCut φ ψ (x + y) :=
  ⟨hy.2 x hx.1, fun z hz ↦ by
    rw [← (hz.1.tame₃ hx.1.1 hy.1.1).add_assoc]
    exact hy.2 _ <| hx.2 z hz⟩

lemma IsMulCut.mul (hx : IsMulCut φ ψ x) (hy : IsMulCut φ ψ y) : IsMulCut φ ψ (x * y) :=
  ⟨hy.2 x hx.1, fun z hz ↦ by
    rw [← (hz.1.1.tame₃ hx.1.1.1 hy.1.1.1).mul_assoc]
    exact hy.2 _ <| hx.2 z hz⟩

lemma IsMulCut.add (hx : IsMulCut φ ψ x) (hy : IsMulCut φ ψ y) : IsMulCut φ ψ (x + y) :=
  ⟨hx.1.add hy.1, fun z hz ↦ by
    rw [(hz.1.1.tame₃ hx.1.1.1 hy.1.1.1).mul_add]
    exact (hx.2 z hz).add <| hy.2 z hz⟩

lemma IsMulCut.isGood (hx : IsMulCut φ ψ x) : IsGood φ ψ x := hx.1.1.1

/--
Below the length of a path, the limit agrees with cofinally many of the sets defined by `ψ`.
-/
lemma HasPath.exists_memLimit_iff (hn : HasPath φ ψ n) (hk : IsGood φ ψ k) :
    ∃ j, IsGood φ ψ j ∧ k ⊴ j ∧ ∀ e, e ◃ n → (MemLimit φ ψ e ↔ M ⊧/![e, j] ψ) := by
  obtain ⟨hn, j₀, hj₀⟩ := hn
  obtain ⟨j, hj, hkj, ha⟩ := (hj₀ n <| cobhamLE_refl n).isCofinal k hk
  use j
  apply And.intro hj
  apply And.intro hkj
  intro e he
  rw [ha e he]
  have he' : e + 1 ⊴ n := hn.add_one_le he
  constructor
  · rintro ⟨j₁, hj₁, h⟩
    exact (((hj₁ _ <| cobhamLE_refl _).agree (hn.of_le he') (hj₀ _ he')) e <|
      (hn.of_le he.1).lt_add_one_iff.mpr <| .inr rfl).mp h
  · exact fun h ↦ ⟨j₀, hj₀.mono hn he', h⟩

lemma hasPath_zero [M↓[ℒₒᵣ] ⊧* 𝗥₀] (hφ : ∀ n : ℕ, M ⊧/![numeral n] φ) : HasPath φ ψ (0 : M) := by
  have h₀ : IsGood φ ψ (0 : M) := by simpa using isGood_numeral (M := M) (ψ := ψ) hφ 0
  have hlt (e : M) : ¬e ◃ 0 := by
    rintro ⟨h, hne⟩
    exact hne <| by simpa using eq_numeral_of_cobhamLE_numeral (n := 0) (x := e) (by simpa using h)
  apply And.intro h₀
  use 0
  intro m hm
  obtain rfl : m = 0 := by
    simpa using eq_numeral_of_cobhamLE_numeral (n := 0) (x := m) (by simpa using hm)
  exact ⟨fun k hk ↦ ⟨k, hk, cobhamLE_refl k, fun e he ↦ absurd he <| hlt e⟩,
    fun _ _ e he ↦ absurd he <| hlt e⟩

section

variable (hno : ¬∃ m : M, IsGreatestGood φ ψ m)
include hno

lemma IsGood.add_one (hx : IsGood φ ψ x) : IsGood φ ψ (x + 1) := by
  by_contra hx'
  apply hno
  use x
  apply And.intro hx
  intro y hy
  rcases hx.tame.total y with h | h
  · rcases hx.tame.add_one_le y h with rfl | h
    · exact cobhamLE_refl x
    · exact absurd (hy.of_le h) hx'
  · exact h

lemma HasPath.add_one (hn : HasPath φ ψ n) : HasPath φ ψ (n + 1) := by
  obtain ⟨hn, j, hj⟩ := hn
  have hn' : IsGood φ ψ (n + 1) := hn.add_one hno
  have hle : n ⊴ n + 1 := (hn.tame.le_add_one_iff n).mpr <| .inl <| cobhamLE_refl n
  have hj' : IsLeftmost φ ψ n j := hj n <| cobhamLE_refl n
  have agree {i i' : M} (h : Agree ψ n i i') (hi : M ⊧/![n, i] ψ ↔ M ⊧/![n, i'] ψ) :
      Agree ψ (n + 1) i i' := by
    intro e he
    rcases hn.lt_add_one_iff.mp he with he | rfl
    · exact h e he
    · exact hi
  have path {i : M} (hi : Agree ψ n i j) (hc : IsCofinal φ ψ (n + 1) i)
      (hL : ∀ i', IsCofinal φ ψ (n + 1) i' → ¬LeftAt ψ n i' i) : IsPath φ ψ (n + 1) i := by
    intro m hm
    rcases (hn.tame.le_add_one_iff m).mp hm with hm | rfl
    · exact (hj m hm).congr (hn.of_le hm) <| hi.symm.mono hn hm
    · apply IsLeftmost.mk hc
      intro i' hi' e he h
      rcases hn.lt_add_one_iff.mp he with he | rfl
      · exact hj'.not_leftAt i' (hi'.mono hn' hle) e he <| h.congr_left he hi hn
      · exact hL i' hi' h
  apply And.intro hn'
  by_cases h₀ : ∃ i, Agree ψ n i j ∧ ¬M ⊧/![n, i] ψ ∧ IsCofinal φ ψ (n + 1) i
  · obtain ⟨i, hi, hni, hc⟩ := h₀
    use i
    exact path hi hc fun i' _ h ↦ hni h.right
  · obtain ⟨k₀, hk₀, h₁⟩ : ∃ k₀, IsGood φ ψ k₀ ∧
        ∀ i, IsGood φ ψ i → k₀ ⊴ i → Agree ψ n i j → M ⊧/![n, i] ψ := by
      by_contra! H
      obtain ⟨i, hi, -, hij, hni⟩ := H n hn
      apply h₀
      use i
      apply And.intro hij
      apply And.intro hni
      intro k hk
      obtain ⟨i', hi', hki', hij', hni'⟩ := H k hk
      exact ⟨i', hi', hki', agree (hij'.trans hij.symm) <| by tauto⟩
    obtain ⟨i₀, hi₀, hki₀, hij₀⟩ := hj'.isCofinal k₀ hk₀
    use i₀
    apply path hij₀ _ fun i' hi' h ↦ h₀ ⟨i', h.agree.trans hij₀, h.left, hi'⟩
    · intro k hk
      obtain ⟨k', hk', hkk', hk₀k'⟩ := hk.exists_le hk₀
      obtain ⟨i, hi, hki, hij⟩ := hj'.isCofinal k' hk'
      exact ⟨i, hi, hi.tame.trans k' k hkk' hki, agree (hij.trans hij₀.symm) <|
        iff_of_true (h₁ i hi (hi.tame.trans k' k₀ hk₀k' hki) hij) (h₁ i₀ hi₀ hki₀ hij₀)⟩

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀] (hφ : ∀ n : ℕ, M ⊧/![numeral n] φ)
include hφ

lemma isAddCut_one : IsAddCut φ ψ (1 : M) := by
  apply And.intro _ fun y hy ↦ hy.add_one hno
  have h : (0 : M) + 1 = 1 := by simpa using numeral_add_one (M := M) 0
  exact h ▸ (hasPath_zero hφ).add_one hno

lemma isMulCut_numeral (n : ℕ) : IsMulCut φ ψ (numeral n : M) := by
  have h₁ : IsMulCut φ ψ (1 : M) := ⟨isAddCut_one hno hφ, fun y hy ↦ by
    rwa [hy.1.1.tame.mul_one]⟩
  induction n with
  | zero => simpa using h₁.of_le h₁.isGood.tame.zero_le
  | succ n ih => simpa [numeral_add_one] using ih.add h₁

lemma IsMulCut.mkPair (hx : IsMulCut φ ψ x) (hy : IsMulCut φ ψ y) : IsMulCut φ ψ (mkPair x y) :=
  have h₁ : IsMulCut φ ψ (1 : M) := by simpa using isMulCut_numeral hno hφ 1
  have h := (hx.add hy).add h₁
  (h.mul h).add hx

end

end path

end FFL.FirstOrder.Arithmetic.R0

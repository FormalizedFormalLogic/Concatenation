module

public import Concatenation.ToFoundation.Arithmetic.Pairing
public import Concatenation.ToFoundation.Arithmetic.R0.Cobham

/-!
# Definable cuts in models of $\mathsf{R}_0$

A definable cut on which arithmetic is tame either has a maximum, or is shortened to a cut that is
closed under addition and multiplication and on which a definable family of sets has a limit.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0.Visser

open ORingStructure
open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {x y z : V}

section isTame

/-- Cobham's order has the order-theoretic properties of a numeral at `x`. -/
@[mk_iff]
structure IsTame (x : V) : Prop where
  total : ∀ y, x ≤ᶜ y ∨ y ≤ᶜ x
  trans : ∀ y z, z ≤ᶜ y → y ≤ᶜ x → z ≤ᶜ x
  antisymm : ∀ y, x ≤ᶜ y → y ≤ᶜ x → x = y
  zero_le : 0 ≤ᶜ x
  add_one_le : ∀ y, x ≤ᶜ y → x = y ∨ x + 1 ≤ᶜ y
  le_add_one_iff : ∀ y, y ≤ᶜ x + 1 ↔ y ≤ᶜ x ∨ y = x + 1
  not_add_one_le : ¬x + 1 ≤ᶜ x
  add_zero : x + 0 = x
  zero_add : 0 + x = x
  mul_zero : x * 0 = 0
  mul_one : x * 1 = x
  one_mul : 1 * x = x

/-- Cobham's order has the order-theoretic properties of a numeral at `x`. -/
def isTameDef : ArithmeticSemisentence 1 := “x.
  (∀ y, !cobhamLEDef x y ∨ !cobhamLEDef y x) ∧
  (∀ y z, !cobhamLEDef z y → !cobhamLEDef y x → !cobhamLEDef z x) ∧
  (∀ y, !cobhamLEDef x y → !cobhamLEDef y x → x = y) ∧
  !cobhamLEDef 0 x ∧
  (∀ y, !cobhamLEDef x y → x = y ∨ !cobhamLEDef (x + 1) y) ∧
  (∀ y, !cobhamLEDef y (x + 1) ↔ !cobhamLEDef y x ∨ y = x + 1) ∧
  ¬!cobhamLEDef (x + 1) x ∧
  x + 0 = x ∧ 0 + x = x ∧ x * 0 = 0 ∧ x * 1 = x ∧ 1 * x = x”

instance isTame_defined : ℒₒᵣ-predicate[V] IsTame via isTameDef :=
  ⟨fun v ↦ by simp [isTameDef, isTame_iff]⟩

instance isTame_definable : ℒₒᵣ-predicate[V] IsTame := isTame_defined.to_definable

/-- Addition and multiplication behave at `x`, `y` and `z` as at numerals. -/
@[mk_iff]
structure IsTame₃ (x y z : V) : Prop where
  add_assoc : x + y + z = x + (y + z)
  mul_assoc : x * y * z = x * (y * z)
  mul_add : x * (y + z) = x * y + x * z
  add_le_add_left : y ≤ᶜ z → x + y ≤ᶜ x + z
  mul_le_mul_left : y ≤ᶜ z → x * y ≤ᶜ x * z
  le_add_right : x ≤ᶜ x + y
  mkPair_le_left : y ≤ᶜ z → mkPair y x ≤ᶜ mkPair z x
  mkPair_le_right : y ≤ᶜ z → mkPair x y ≤ᶜ mkPair x z

/-- Addition and multiplication behave at `x`, `y` and `z` as at numerals. -/
def isTame₃Def : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “x y z.
  x + y + z = x + (y + z) ∧ x * y * z = x * (y * z) ∧ x * (y + z) = x * y + x * z ∧
  (!cobhamLEDef y z → !cobhamLEDef (x + y) (x + z)) ∧
  (!cobhamLEDef y z → !cobhamLEDef (x * y) (x * z)) ∧
  !cobhamLEDef x (x + y) ∧
  (!cobhamLEDef y z → !cobhamLEDef (!mkPairTerm y x) (!mkPairTerm z x)) ∧
  (!cobhamLEDef y z → !cobhamLEDef (!mkPairTerm x y) (!mkPairTerm x z))”

instance isTame₃_defined : 𝚺ᴬ₀-Relation₃[V] IsTame₃ via isTame₃Def := .mk fun v ↦ by
  simp [isTame₃Def, isTame₃_iff]

instance isTame₃_definable : 𝚺ᴬ₀-Relation₃[V] IsTame₃ := isTame₃_defined.to_definable

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

@[grind .]
lemma isTame_numeral (n : ℕ) : IsTame (numeral n : V) where
  total y := (cobhamLE_numeral_or n).symm
  trans y z hz hy := by grind [eq_numeral_of_cobhamLE_numeral]
  antisymm y hxy hyx := by grind [eq_numeral_of_cobhamLE_numeral]
  zero_le := by simpa using numeral_cobhamLE_numeral_iff (V := V) (k := 0) (n := n)
  add_one_le y hy := by
    have := cobhamLE_numeral_or (x := y) (n + 1)
    grind [eq_numeral_of_cobhamLE_numeral]
  le_add_one_iff y := by grind [eq_numeral_of_cobhamLE_numeral]
  not_add_one_le := by simp
  add_zero := by simpa using numeral_add_numeral (M := V) n 0
  zero_add := by simpa using numeral_add_numeral (M := V) 0 n
  mul_zero := by simpa using numeral_mul_numeral (M := V) n 0
  mul_one := by simpa using numeral_mul_numeral (M := V) n 1
  one_mul := by simpa using numeral_mul_numeral (M := V) 1 n

@[grind .]
lemma isTame₃_numeral (k n m : ℕ) : IsTame₃ (numeral k : V) (numeral n) (numeral m) := by
  constructor <;> simp +contextual [numeral_add_numeral, numeral_mul_numeral, Nat.add_assoc,
    Nat.mul_assoc, Nat.mul_add, Nat.mul_le_mul_left, mkPair_le_mkPair]

end isTame

section agree

variable {R : V → V → Prop} {ψ : ArithmeticSemisentence 2} {e i j k m n : V}

/-- The sets `R · i` and `R · j` agree below `m`. -/
def Agree (R : V → V → Prop) (m i j : V) : Prop := ∀ e, e <ᶜ m → (R e i ↔ R e j)

/-- The sets defined by `ψ` with the parameters `i` and `j` agree below `m`. -/
def agreeDef (ψ : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
  “m i j. ∀ e, !cobhamLTDef e m → (!ψ e i ↔ !ψ e j)”

/-- The sets `R · i` and `R · j` first differ at `e`, which belongs to the second one. -/
@[mk_iff]
structure LeftAt (R : V → V → Prop) (e i j : V) : Prop where
  agree : Agree R e i j
  left : ¬R e i
  right : R e j

/--
The sets defined by `ψ` with the parameters `i` and `j` first differ at `e`, which belongs to the
second one.
-/
def leftAtDef (ψ : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
  “e i j. !(agreeDef ψ) e i j ∧ ¬!ψ e i ∧ !ψ e j”

variable [ℒₒᵣ-relation[V] R via ψ]

instance agree_defined : ℒₒᵣ-relation₃[V] (Agree R) via agreeDef ψ :=
  ⟨fun v ↦ by simp [agreeDef, Agree]⟩

instance leftAt_defined : ℒₒᵣ-relation₃[V] (LeftAt R) via leftAtDef ψ :=
  ⟨fun v ↦ by simp [leftAtDef, leftAt_iff]⟩

@[grind →]
lemma Agree.symm (h : Agree R m i j) : Agree R m j i := fun e he ↦ (h e he).symm

lemma Agree.trans (h : Agree R m i j) (h' : Agree R m j k) : Agree R m i k :=
  fun e he ↦ (h e he).trans (h' e he)

end agree

section good

variable {P : V → Prop} {R : V → V → Prop} {φ : ArithmeticSemisentence 1}
  {ψ : ArithmeticSemisentence 2}

/--
`x` is good for `P` and `R`: below `x` arithmetic is tame, `P` holds, and distinct sets `R · i`
have a first difference.
-/
@[mk_iff]
structure IsGood (P : V → Prop) (R : V → V → Prop) (x : V) : Prop where
  isTame : ∀ y, y ≤ᶜ x → IsTame y
  isTame₃ : ∀ w, w ≤ᶜ x → ∀ y z u, y ≤ᶜ w → z ≤ᶜ w → u ≤ᶜ w → IsTame₃ y z u
  pred : ∀ y, y ≤ᶜ x → P y
  agree_or : ∀ m, m ≤ᶜ x → ∀ i j, Agree R m i j ∨ ∃ e, e <ᶜ m ∧ (LeftAt R e i j ∨ LeftAt R e j i)

/--
`x` is good for `φ` and `ψ`: below `x` arithmetic is tame, `φ` holds, and distinct sets defined
by `ψ` have a first difference.
-/
def isGoodDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 := “x.
  (∀ y, !cobhamLEDef y x → !isTameDef y) ∧
  (∀ w, !cobhamLEDef w x → ∀ y z u, !cobhamLEDef y w → !cobhamLEDef z w → !cobhamLEDef u w →
    !isTame₃Def y z u) ∧
  (∀ y, !cobhamLEDef y x → !φ y) ∧
  ∀ m, !cobhamLEDef m x → ∀ i j, !(agreeDef ψ) m i j ∨
    ∃ e, !cobhamLTDef e m ∧ (!(leftAtDef ψ) e i j ∨ !(leftAtDef ψ) e j i)”

instance isGood_defined [ℒₒᵣ-predicate[V] P via φ] [ℒₒᵣ-relation[V] R via ψ] :
    ℒₒᵣ-predicate[V] (IsGood P R) via isGoodDef φ ψ :=
  ⟨fun v ↦ by simp [isGoodDef, isGood_iff]⟩

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

private lemma agree_numeral_or (n : ℕ) (i j : V) : Agree R (numeral n) i j ∨
    ∃ e, e <ᶜ numeral n ∧ (LeftAt R e i j ∨ LeftAt R e j i) := by
  by_cases h : ∃ k < n, ¬(R (numeral k) i ↔ R (numeral k) j)
  · right
    classical
    obtain ⟨hk, hd⟩ := Nat.find_spec h
    have agree : Agree R (numeral (Nat.find h)) i j := by
      intro e he
      obtain ⟨l, hl, rfl⟩ := cobhamLT_numeral_iff_exists.mp he
      by_contra H
      exact Nat.find_min h hl ⟨hl.trans hk, H⟩
    use numeral (Nat.find h)
    constructor
    · exact cobhamLT_numeral_iff_exists.mpr ⟨_, hk, rfl⟩
    · by_cases hi : R (numeral (Nat.find h)) i
      · right
        exact ⟨agree.symm, by tauto, hi⟩
      · left
        exact ⟨agree, hi, by tauto⟩
  · left
    intro e he
    obtain ⟨k, hk, rfl⟩ := cobhamLT_numeral_iff_exists.mp he
    by_contra H
    exact h ⟨k, hk, H⟩

lemma isGood_numeral (h : ∀ n : ℕ, P (numeral n)) (n : ℕ) : IsGood P R (numeral n : V) where
  isTame y hy := by grind [eq_numeral_of_cobhamLE_numeral]
  isTame₃ w hw y z u hy hz hu := by grind [eq_numeral_of_cobhamLE_numeral]
  pred y hy := by grind [eq_numeral_of_cobhamLE_numeral]
  agree_or m hm i j := by grind [eq_numeral_of_cobhamLE_numeral, agree_numeral_or]

end good

section path

variable {P : V → Prop} {R : V → V → Prop} {φ : ArithmeticSemisentence 1}
  {ψ : ArithmeticSemisentence 2} {e i j k m n : V}

/-- `m` is the greatest good element. -/
def IsGreatestGood (P : V → Prop) (R : V → V → Prop) (m : V) : Prop :=
  IsGood P R m ∧ ∀ x, IsGood P R x → x ≤ᶜ m

/-- `m` is the greatest good element. -/
def isGreatestGoodDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “m. !(isGoodDef φ ψ) m ∧ ∀ x, !(isGoodDef φ ψ) x → !cobhamLEDef x m”

/-- Cofinally many sets `R · i` with good `i` agree below `m` with `R · j`. -/
def IsCofinal (P : V → Prop) (R : V → V → Prop) (m j : V) : Prop :=
  ∀ k, IsGood P R k → ∃ i, IsGood P R i ∧ k ≤ᶜ i ∧ Agree R m i j

/--
Cofinally many sets defined by `ψ` with good parameters agree below `m` with the one of parameter
`j`.
-/
def isCofinalDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 :=
  “m j. ∀ k, !(isGoodDef φ ψ) k → ∃ i, !(isGoodDef φ ψ) i ∧ !cobhamLEDef k i ∧ !(agreeDef ψ) m i j”

/-- `j` is leftmost among the cofinal parameters up to agreement below `m`. -/
@[mk_iff]
structure IsLeftmost (P : V → Prop) (R : V → V → Prop) (m j : V) : Prop where
  isCofinal : IsCofinal P R m j
  not_leftAt : ∀ i, IsCofinal P R m i → ∀ e, e <ᶜ m → ¬LeftAt R e i j

/-- `j` is leftmost among the cofinal parameters up to agreement below `m`. -/
def isLeftmostDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 := “m j.
  !(isCofinalDef φ ψ) m j ∧
    ∀ i, !(isCofinalDef φ ψ) m i → ∀ e, !cobhamLTDef e m → ¬!(leftAtDef ψ) e i j”

/-- `j` is leftmost up to agreement below every `m` up to `n`. -/
def IsPath (P : V → Prop) (R : V → V → Prop) (n j : V) : Prop :=
  ∀ m, m ≤ᶜ n → IsLeftmost P R m j

/-- `j` is leftmost up to agreement below every `m` up to `n`. -/
def isPathDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 2 :=
  “n j. ∀ m, !cobhamLEDef m n → !(isLeftmostDef φ ψ) m j”

/-- `e` belongs to the limit of the sets `R · j`. -/
def MemLimit (P : V → Prop) (R : V → V → Prop) (e : V) : Prop :=
  ∃ j, IsPath P R (e + 1) j ∧ R e j

/-- `e` belongs to the limit of the sets defined by `ψ`. -/
def memLimitDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “e. ∃ j, !(isPathDef φ ψ) (e + 1) j ∧ !ψ e j”

/-- There is a path of length `n`. -/
def HasPath (P : V → Prop) (R : V → V → Prop) (n : V) : Prop :=
  IsGood P R n ∧ ∃ j, IsPath P R n j

/-- There is a path of length `n`. -/
def hasPathDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “n. !(isGoodDef φ ψ) n ∧ ∃ j, !(isPathDef φ ψ) n j”

/-- The lengths of paths are closed under the addition of `x`. -/
def IsAddCut (P : V → Prop) (R : V → V → Prop) (x : V) : Prop :=
  HasPath P R x ∧ ∀ y, HasPath P R y → HasPath P R (y + x)

/-- The lengths of paths are closed under the addition of `x`. -/
def isAddCutDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. !(hasPathDef φ ψ) x ∧ ∀ y, !(hasPathDef φ ψ) y → !(hasPathDef φ ψ) (y + x)”

/-- The elements of `IsAddCut P R` are closed under the multiplication by `x`. -/
def IsMulCut (P : V → Prop) (R : V → V → Prop) (x : V) : Prop :=
  IsAddCut P R x ∧ ∀ y, IsAddCut P R y → IsAddCut P R (y * x)

/-- The elements of `isAddCutDef φ ψ` are closed under the multiplication by `x`. -/
def isMulCutDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. !(isAddCutDef φ ψ) x ∧ ∀ y, !(isAddCutDef φ ψ) y → !(isAddCutDef φ ψ) (y * x)”

section defined

variable [ℒₒᵣ-predicate[V] P via φ] [ℒₒᵣ-relation[V] R via ψ]

instance isGreatestGood_defined : ℒₒᵣ-predicate[V] (IsGreatestGood P R) via isGreatestGoodDef φ ψ :=
  ⟨fun v ↦ by simp [isGreatestGoodDef, IsGreatestGood]⟩

instance isCofinal_defined : ℒₒᵣ-relation[V] (IsCofinal P R) via isCofinalDef φ ψ :=
  ⟨fun v ↦ by simp [isCofinalDef, IsCofinal]⟩

instance isLeftmost_defined : ℒₒᵣ-relation[V] (IsLeftmost P R) via isLeftmostDef φ ψ :=
  ⟨fun v ↦ by simp [isLeftmostDef, isLeftmost_iff]⟩

instance isPath_defined : ℒₒᵣ-relation[V] (IsPath P R) via isPathDef φ ψ :=
  ⟨fun v ↦ by simp [isPathDef, IsPath]⟩

instance memLimit_defined : ℒₒᵣ-predicate[V] (MemLimit P R) via memLimitDef φ ψ :=
  ⟨fun v ↦ by simp [memLimitDef, MemLimit]⟩

instance hasPath_defined : ℒₒᵣ-predicate[V] (HasPath P R) via hasPathDef φ ψ :=
  ⟨fun v ↦ by simp [hasPathDef, HasPath]⟩

instance isAddCut_defined : ℒₒᵣ-predicate[V] (IsAddCut P R) via isAddCutDef φ ψ :=
  ⟨fun v ↦ by simp [isAddCutDef, IsAddCut]⟩

instance isMulCut_defined : ℒₒᵣ-predicate[V] (IsMulCut P R) via isMulCutDef φ ψ :=
  ⟨fun v ↦ by simp [isMulCutDef, IsMulCut]⟩

end defined

namespace IsGood

@[grind →]
lemma tame (hx : IsGood P R x) : IsTame x := hx.isTame x <| cobhamLE_refl x

@[grind →]
lemma of_le (hx : IsGood P R x) (h : y ≤ᶜ x) : IsGood P R y where
  isTame z hz := hx.isTame z <| hx.tame.trans y z hz h
  isTame₃ w hw := hx.isTame₃ w <| hx.tame.trans y w hw h
  pred z hz := hx.pred z <| hx.tame.trans y z hz h
  agree_or m hm := hx.agree_or m <| hx.tame.trans y m hm h

lemma exists_le (hx : IsGood P R x) (hy : IsGood P R y) : ∃ z, IsGood P R z ∧ x ≤ᶜ z ∧ y ≤ᶜ z := by
  rcases hx.tame.total y with h | h <;> grind

lemma tame₃ (hx : IsGood P R x) (hy : IsGood P R y) (hz : IsGood P R z) : IsTame₃ x y z := by
  obtain ⟨u, hu, hxu, hyu⟩ := hx.exists_le hy
  obtain ⟨v, hv, huv, hzv⟩ := hu.exists_le hz
  exact hv.isTame₃ v (cobhamLE_refl v) x y z (hv.tame.trans u x hxu huv)
    (hv.tame.trans u y hyu huv) hzv

lemma lt_add_one_iff (hm : IsGood P R m) : e <ᶜ m + 1 ↔ e <ᶜ m ∨ e = m := by
  have := hm.tame.le_add_one_iff e
  have := hm.tame.le_add_one_iff m
  have := hm.tame.not_add_one_le
  grind [CobhamLT]

lemma add_one_le (hm : IsGood P R m) (h : e <ᶜ m) : e + 1 ≤ᶜ m :=
  ((hm.of_le h.1).tame.add_one_le m h.1).resolve_left h.2

end IsGood

lemma Agree.mono (hm : IsGood P R m) (h : n ≤ᶜ m) (hij : Agree R m i j) : Agree R n i j := by
  intro e he
  have := hm.tame.trans n e he.1 h
  have := hm.tame.antisymm n
  exact hij e <| by grind [CobhamLT]

lemma LeftAt.congr_left (he : e <ᶜ n) (h : Agree R n j k) (hn : IsGood P R n)
    (hl : LeftAt R e i j) : LeftAt R e i k :=
  ⟨hl.agree.trans <| h.mono hn he.1, hl.left, (h e he).mp hl.right⟩

lemma IsCofinal.congr (hc : IsCofinal P R n i) (h : Agree R n i j) : IsCofinal P R n j :=
  fun k hk ↦
    let ⟨i', hi', hki', ha⟩ := hc k hk
    ⟨i', hi', hki', ha.trans h⟩

lemma IsCofinal.mono (hm : IsGood P R m) (h : n ≤ᶜ m) (hc : IsCofinal P R m i) :
    IsCofinal P R n i :=
  fun k hk ↦
    let ⟨i', hi', hki', ha⟩ := hc k hk
    ⟨i', hi', hki', ha.mono hm h⟩

lemma IsLeftmost.congr (hn : IsGood P R n) (hl : IsLeftmost P R n i) (h : Agree R n i j) :
    IsLeftmost P R n j where
  isCofinal := hl.isCofinal.congr h
  not_leftAt i' hi' e he hL := hl.not_leftAt i' hi' e he <| hL.congr_left he h.symm hn

lemma IsLeftmost.agree (hn : IsGood P R n) (hi : IsLeftmost P R n i) (hj : IsLeftmost P R n j) :
    Agree R n i j := by
  have := hj.not_leftAt i hi.isCofinal
  have := hi.not_leftAt j hj.isCofinal
  grind [hn.agree_or n (cobhamLE_refl n) i j]

lemma IsPath.mono (hm : IsGood P R m) (h : n ≤ᶜ m) (hp : IsPath P R m j) : IsPath P R n j :=
  fun k hk ↦ hp k <| hm.tame.trans n k hk h

@[grind →]
lemma HasPath.of_le (hm : HasPath P R m) (h : n ≤ᶜ m) : HasPath P R n :=
  let ⟨hm, j, hj⟩ := hm
  ⟨hm.of_le h, j, hj.mono hm h⟩

@[grind →]
lemma IsAddCut.of_le (hx : IsAddCut P R x) (h : y ≤ᶜ x) : IsAddCut P R y :=
  have hy := hx.1.of_le h
  ⟨hy, fun z hz ↦ (hx.2 z hz).of_le <| (hz.1.tame₃ hy.1 hx.1.1).add_le_add_left h⟩

@[grind →]
lemma IsMulCut.of_le (hx : IsMulCut P R x) (h : y ≤ᶜ x) : IsMulCut P R y :=
  have hy := hx.1.of_le h
  ⟨hy, fun z hz ↦ (hx.2 z hz).of_le <| (hz.1.1.tame₃ hy.1.1 hx.1.1.1).mul_le_mul_left h⟩

@[grind ←]
lemma IsAddCut.add (hx : IsAddCut P R x) (hy : IsAddCut P R y) : IsAddCut P R (x + y) := by
  apply And.intro (hy.2 x hx.1)
  intro z hz
  rw [← (hz.1.tame₃ hx.1.1 hy.1.1).add_assoc]
  exact hy.2 _ <| hx.2 z hz

@[grind ←]
lemma IsMulCut.mul (hx : IsMulCut P R x) (hy : IsMulCut P R y) : IsMulCut P R (x * y) := by
  apply And.intro (hy.2 x hx.1)
  intro z hz
  rw [← (hz.1.1.tame₃ hx.1.1.1 hy.1.1.1).mul_assoc]
  exact hy.2 _ <| hx.2 z hz

@[grind ←]
lemma IsMulCut.add (hx : IsMulCut P R x) (hy : IsMulCut P R y) : IsMulCut P R (x + y) := by
  apply And.intro (hx.1.add hy.1)
  intro z hz
  rw [(hz.1.1.tame₃ hx.1.1.1 hy.1.1.1).mul_add]
  exact (hx.2 z hz).add <| hy.2 z hz

@[grind →]
lemma IsMulCut.isGood (hx : IsMulCut P R x) : IsGood P R x := hx.1.1.1

/-- Below the length of a path, the limit agrees with cofinally many of the sets `R · j`. -/
lemma HasPath.exists_memLimit_iff (hn : HasPath P R n) (hk : IsGood P R k) :
    ∃ j, IsGood P R j ∧ k ≤ᶜ j ∧ ∀ e, e <ᶜ n → (MemLimit P R e ↔ R e j) := by
  obtain ⟨hn, j₀, hj₀⟩ := hn
  obtain ⟨j, hj, hkj, ha⟩ := (hj₀ n <| cobhamLE_refl n).isCofinal k hk
  use j
  apply And.intro hj
  apply And.intro hkj
  intro e he
  rw [ha e he]
  have he' : e + 1 ≤ᶜ n := hn.add_one_le he
  constructor
  · rintro ⟨j₁, hj₁, h⟩
    exact (((hj₁ _ <| cobhamLE_refl _).agree (hn.of_le he') (hj₀ _ he')) e <|
      (hn.of_le he.1).lt_add_one_iff.mpr <| .inr rfl).mp h
  · exact fun h ↦ ⟨j₀, hj₀.mono hn he', h⟩

section

variable (hno : ∀ m : V, ¬IsGreatestGood P R m)
include hno

lemma IsGood.add_one (hx : IsGood P R x) : IsGood P R (x + 1) := by
  by_contra hx'
  apply hno x
  apply And.intro hx
  intro y hy
  have := hx.tame.total y
  have := hx.tame.add_one_le y
  grind

lemma HasPath.add_one (hn : HasPath P R n) : HasPath P R (n + 1) := by
  obtain ⟨hn, j, hj⟩ := hn
  have hn' : IsGood P R (n + 1) := hn.add_one hno
  have hle : n ≤ᶜ n + 1 := (hn.tame.le_add_one_iff n).mpr <| .inl <| cobhamLE_refl n
  have hj' : IsLeftmost P R n j := hj n <| cobhamLE_refl n
  have agree {i i' : V} (h : Agree R n i i') (hi : R n i ↔ R n i') : Agree R (n + 1) i i' := by
    intro e he
    rcases hn.lt_add_one_iff.mp he with he | rfl
    · exact h e he
    · exact hi
  have path {i : V} (hi : Agree R n i j) (hc : IsCofinal P R (n + 1) i)
      (hL : ∀ i', IsCofinal P R (n + 1) i' → ¬LeftAt R n i' i) : IsPath P R (n + 1) i := by
    intro m hm
    rcases (hn.tame.le_add_one_iff m).mp hm with hm | rfl
    · exact (hj m hm).congr (hn.of_le hm) <| hi.symm.mono hn hm
    · apply IsLeftmost.mk hc
      intro i' hi' e he h
      rcases hn.lt_add_one_iff.mp he with he | rfl
      · exact hj'.not_leftAt i' (hi'.mono hn' hle) e he <| h.congr_left he hi hn
      · exact hL i' hi' h
  apply And.intro hn'
  by_cases h₀ : ∃ i, Agree R n i j ∧ ¬R n i ∧ IsCofinal P R (n + 1) i
  · obtain ⟨i, hi, hni, hc⟩ := h₀
    use i
    exact path hi hc fun i' _ h ↦ hni h.right
  · obtain ⟨k₀, hk₀, h₁⟩ : ∃ k₀, IsGood P R k₀ ∧
        ∀ i, IsGood P R i → k₀ ≤ᶜ i → Agree R n i j → R n i := by
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

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀] (hP : ∀ n : ℕ, P (numeral n))
include hP

lemma isMulCut_numeral (n : ℕ) : IsMulCut P R (numeral n : V) := by
  have h₀ : HasPath P R (0 : V) := by
    have hlt (e : V) : ¬e <ᶜ 0 := by simpa using cobhamLT_numeral_iff_exists (x := e) (n := 0)
    apply And.intro <| by simpa using isGood_numeral (V := V) (R := R) hP 0
    use 0
    intro m hm
    obtain rfl : m = 0 := by
      simpa using eq_numeral_of_cobhamLE_numeral (n := 0) (x := m) (by simpa using hm)
    constructor
    · exact fun k hk ↦ ⟨k, hk, cobhamLE_refl k, fun e he ↦ absurd he <| hlt e⟩
    · exact fun _ _ e he ↦ absurd he <| hlt e
  have h₁ : IsMulCut P R (1 : V) := by
    have h : (0 : V) + 1 = 1 := by simpa using numeral_add_one_of_R0 (V := V) 0
    apply And.intro ⟨h ▸ h₀.add_one hno, fun y hy ↦ hy.add_one hno⟩
    intro y hy
    rwa [hy.1.1.tame.mul_one]
  induction n with
  | zero => simpa using h₁.of_le h₁.isGood.tame.zero_le
  | succ n ih => simpa using ih.add h₁

lemma IsMulCut.mkPair (hx : IsMulCut P R x) (hy : IsMulCut P R y) : IsMulCut P R (mkPair x y) :=
  have h₁ : IsMulCut P R (1 : V) := by simpa using isMulCut_numeral hno hP 1
  have h := (hx.add hy).add h₁
  (h.mul h).add hx

lemma mkPair_le_mkPair_of_isMulCut {a b : V} (ha : IsMulCut P R a) (hb : IsMulCut P R b)
    (hx : x ≤ᶜ a) (hy : y ≤ᶜ b) : mkPair x y ≤ᶜ mkPair a b := by
  have hx' := ha.of_le hx
  have hy' := hb.of_le hy
  exact (ha.mkPair hno hP hb).isGood.tame.trans _ _
    ((hy'.isGood.tame₃ hx'.isGood ha.isGood).mkPair_le_left hx)
    ((ha.isGood.tame₃ hy'.isGood hb.isGood).mkPair_le_right hy)

end

end path

end FFL.FirstOrder.Arithmetic.R0.Visser

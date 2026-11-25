module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Quantifier elimination for Presburger arithmetic

Linear inequalities and congruences with integer coefficients, read in a discretely ordered ring
with division by the positive integers, define a class of sets closed under projection.
-/

@[expose] public section

/--
A discretely ordered commutative ring in which every element has a quotient and a remainder
modulo every positive integer.
-/
class PresburgerRing (R : Type*) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] : Prop where
  one_le_of_pos {x : R} : 0 < x → 1 ≤ x
  exists_eq_mul_add (n : ℕ) (hn : 0 < n) (x : R) : ∃ q : R, ∃ r : ℕ, r < n ∧ x = n * q + r

instance : PresburgerRing ℤ where
  one_le_of_pos h := h
  exists_eq_mul_add n hn x := by
    have h₁ : 0 ≤ x % n := Int.emod_nonneg x (by omega)
    have h₂ : x % n < n := Int.emod_lt_of_pos x (by omega)
    use x / n, (x % n).toNat
    and_intros
    · omega
    · rw [Int.toNat_of_nonneg h₁]
      exact (Int.mul_ediv_add_emod x n).symm

/-- A discretely ordered commutative ring with division by its positive elements is Presburger. -/
lemma PresburgerRing.of_forall_exists {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (h₁ : ∀ x : R, 0 < x → 1 ≤ x)
    (h₂ : ∀ n x : R, 0 < n → ∃ q r, x = n * q + r ∧ 0 ≤ r ∧ r < n) : PresburgerRing R where
  one_le_of_pos := h₁ _
  exists_eq_mul_add n hn x := by
    obtain ⟨q, r, e, h0, hr⟩ := h₂ n x (by exact_mod_cast hn)
    have key : ∀ (n : ℕ) (r : R), 0 ≤ r → r < n → ∃ k < n, r = k := by
      intro n
      induction n with
      | zero =>
        intro r h0 hr
        exact absurd hr (by simpa using h0)
      | succ n ih =>
        intro r h0 hr
        rcases h0.lt_or_eq with hpos | rfl
        · have := h₁ r hpos
          obtain ⟨k, hk, e⟩ := ih (r - 1) (by linarith) (by push_cast at hr; linarith)
          exact ⟨k + 1, by omega, by push_cast; linarith⟩
        · exact ⟨0, by omega, by simp⟩
    obtain ⟨k, hk, rfl⟩ := key n r h0 hr
    exact ⟨q, k, hk, e⟩

namespace Presburger

variable {n m : ℕ} {R : Type*} [CommRing R]

/-- A linear polynomial with integer coefficients in the variables `Fin n`. -/
@[ext]
structure LinearTerm (n : ℕ) where
  /-- The coefficients of the variables. -/
  coeff : Fin n → ℤ
  /-- The constant term. -/
  const : ℤ

namespace LinearTerm

/-- The value of a linear term. -/
def eval (t : LinearTerm n) (v : Fin n → R) : R := ∑ i, (t.coeff i : R) * v i + t.const

instance : Add (LinearTerm n) := ⟨fun s t ↦ ⟨s.coeff + t.coeff, s.const + t.const⟩⟩

instance : Sub (LinearTerm n) := ⟨fun s t ↦ ⟨s.coeff - t.coeff, s.const - t.const⟩⟩

instance : SMul ℤ (LinearTerm n) := ⟨fun a t ↦ ⟨a • t.coeff, a * t.const⟩⟩

/-- The variable `i`. -/
def var (i : Fin n) : LinearTerm n := ⟨Pi.single i 1, 0⟩

/-- The constant `k`. -/
def ofInt (k : ℤ) : LinearTerm n := ⟨0, k⟩

/-- The term without its first variable. -/
def tail (t : LinearTerm (n + 1)) : LinearTerm n := ⟨fun i ↦ t.coeff i.succ, t.const⟩

/-- The term in which the variable `i` is read as the variable `f i`. -/
def rename (f : Fin n → Fin m) (t : LinearTerm n) : LinearTerm m :=
  ⟨fun j ↦ ∑ i, if f i = j then t.coeff i else 0, t.const⟩

variable (s t : LinearTerm n) (v : Fin n → R)

@[simp]
lemma eval_add : (s + t).eval v = s.eval v + t.eval v := by
  change ∑ i, ((s.coeff i + t.coeff i : ℤ) : R) * v i + ((s.const + t.const : ℤ) : R) = _
  simp only [eval, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

@[simp]
lemma eval_sub : (s - t).eval v = s.eval v - t.eval v := by
  change ∑ i, ((s.coeff i - t.coeff i : ℤ) : R) * v i + ((s.const - t.const : ℤ) : R) = _
  simp only [eval, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring

@[simp]
lemma eval_smul (a : ℤ) : (a • t).eval v = a * t.eval v := by
  change ∑ i, ((a * t.coeff i : ℤ) : R) * v i + ((a * t.const : ℤ) : R) = _
  simp only [eval, Int.cast_mul, mul_add, Finset.mul_sum, mul_assoc]

@[simp]
lemma eval_var (i : Fin n) : (var i).eval v = v i := by
  simp [eval, var, Pi.single_apply, ite_mul]

@[simp]
lemma eval_ofInt (k : ℤ) : (ofInt k : LinearTerm n).eval v = k := by
  simp [eval, ofInt]

lemma eval_cons (t : LinearTerm (n + 1)) (x : R) :
    t.eval (Matrix.vecCons x v) = t.coeff 0 * x + t.tail.eval v := by
  simp only [eval, tail, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

@[simp]
lemma eval_rename (f : Fin n → Fin m) (v : Fin m → R) : (t.rename f).eval v = t.eval (v ∘ f) := by
  simp only [eval, rename, Int.cast_sum, Finset.sum_mul, Function.comp_apply]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma eval_zero (t : LinearTerm 0) (v : Fin 0 → R) : t.eval v = t.const := by
  simp [eval]

end LinearTerm

/--
The quantifier-free formulas of Presburger arithmetic in negation normal form: a linear term is
positive, or is or is not divisible by a positive integer.
-/
inductive Formula (n : ℕ) where
  | verum : Formula n
  | falsum : Formula n
  | pos (t : LinearTerm n) : Formula n
  | dvd (b : Bool) (m : ℕ+) (t : LinearTerm n) : Formula n
  | and (φ ψ : Formula n) : Formula n
  | or (φ ψ : Formula n) : Formula n

namespace Formula

open LinearTerm

variable [LinearOrder R]

/-- The truth value of a formula. -/
@[simp]
def eval (v : Fin n → R) : Formula n → Prop
  | verum => True
  | falsum => False
  | pos t => 0 < t.eval v
  | dvd b m t => b = true ↔ ((m : ℕ) : R) ∣ t.eval v
  | and φ ψ => φ.eval v ∧ ψ.eval v
  | or φ ψ => φ.eval v ∨ ψ.eval v

/-- The negation of a formula. -/
def neg : Formula n → Formula n
  | verum => falsum
  | falsum => verum
  | pos t => pos (ofInt 1 - t)
  | dvd b m t => dvd (!b) m t
  | and φ ψ => or φ.neg ψ.neg
  | or φ ψ => and φ.neg ψ.neg

/-- The formula in which the variable `i` is read as the variable `f i`. -/
def rename (f : Fin n → Fin m) : Formula n → Formula m
  | verum => verum
  | falsum => falsum
  | pos t => pos (t.rename f)
  | dvd b m t => dvd b m (t.rename f)
  | and φ ψ => and (φ.rename f) (ψ.rename f)
  | or φ ψ => or (φ.rename f) (ψ.rename f)

/-- The disjunction of a list of formulas. -/
def disj : List (Formula n) → Formula n
  | [] => falsum
  | φ :: l => or φ (disj l)

/-- The conjunction of a list of formulas. -/
def conj : List (Formula n) → Formula n
  | [] => verum
  | φ :: l => and φ (conj l)

/-- The inequality `s < t`. -/
def lt (s t : LinearTerm n) : Formula n := pos (t - s)

/-- The inequality `s ≤ t`. -/
def le (s t : LinearTerm n) : Formula n := pos (t - s + ofInt 1)

/-- The equation `s = t`. -/
def eq (s t : LinearTerm n) : Formula n := and (le s t) (le t s)

variable {v : Fin n → R}

@[simp]
lemma eval_rename (f : Fin n → Fin m) (φ : Formula n) {v : Fin m → R} :
    (φ.rename f).eval v ↔ φ.eval (v ∘ f) := by
  induction φ <;> simp [rename, *]

@[simp]
lemma eval_disj {l : List (Formula n)} : (disj l).eval v ↔ ∃ φ ∈ l, φ.eval v := by
  induction l <;> simp [disj, *]

@[simp]
lemma eval_conj {l : List (Formula n)} : (conj l).eval v ↔ ∀ φ ∈ l, φ.eval v := by
  induction l <;> simp [conj, *]

@[simp]
lemma eval_lt [IsStrictOrderedRing R] (s t : LinearTerm n) :
    (lt s t).eval v ↔ s.eval v < t.eval v := by
  simp [lt]

section

variable [IsStrictOrderedRing R] [PresburgerRing R]

lemma lt_add_one_iff {x y : R} : x < y + 1 ↔ x ≤ y := by
  constructor
  · intro h
    have := PresburgerRing.one_le_of_pos (sub_pos.mpr h)
    linarith
  · intro h
    linarith

@[simp]
lemma eval_neg (φ : Formula n) : φ.neg.eval v ↔ ¬φ.eval v := by
  induction φ with
  | verum => simp [neg]
  | falsum => simp [neg]
  | pos t =>
    have := lt_add_one_iff (x := t.eval v) (y := 0)
    simp only [neg, eval, eval_sub, eval_ofInt, Int.cast_one, sub_pos, not_lt]
    simpa using this
  | dvd b m t => cases b <;> simp [neg]
  | and φ ψ ihφ ihψ => simp [neg, ihφ, ihψ, imp_iff_not_or]
  | or φ ψ ihφ ihψ => simp [neg, ihφ, ihψ]

@[simp]
lemma eval_le (s t : LinearTerm n) : (le s t).eval v ↔ s.eval v ≤ t.eval v := by
  have := lt_add_one_iff (x := s.eval v) (y := t.eval v)
  simp only [le, eval, eval_add, eval_sub, eval_ofInt, Int.cast_one]
  constructor <;> intro h <;> [apply this.mp; have := this.mpr h] <;> linarith

@[simp]
lemma eval_eq (s t : LinearTerm n) : (eq s t).eval v ↔ s.eval v = t.eval v := by
  simp only [eq, eval, eval_le]
  exact le_antisymm_iff.symm

end

/-! ### Elimination of one variable -/

/-- The least common multiple of the moduli of a formula. -/
def modLcm : Formula n → ℕ
  | dvd _ m _ => m
  | and φ ψ => Nat.lcm φ.modLcm ψ.modLcm
  | or φ ψ => Nat.lcm φ.modLcm ψ.modLcm
  | _ => 1

lemma modLcm_pos (φ : Formula n) : 0 < φ.modLcm := by
  induction φ <;> simp [modLcm, *]

/-- The lower bounds `0 < c * x + s` with `0 < c` that a formula puts on its first variable `x`. -/
def lowers : Formula (n + 1) → List (ℕ+ × LinearTerm n)
  | pos t => if h : 0 < t.coeff 0 then [(⟨(t.coeff 0).toNat, by omega⟩, t.tail)] else []
  | and φ ψ => φ.lowers ++ ψ.lowers
  | or φ ψ => φ.lowers ++ ψ.lowers
  | _ => []

/-- The formula that a formula becomes when its first variable is small. -/
def minusInf : Formula (n + 1) → Formula (n + 1)
  | pos t => if 0 < t.coeff 0 then falsum else if t.coeff 0 < 0 then verum else pos t
  | and φ ψ => and φ.minusInf ψ.minusInf
  | or φ ψ => or φ.minusInf ψ.minusInf
  | φ => φ

/-- The formula in which the first variable `x` is replaced by the solution of `a * x = u`. -/
def substDiv (a : ℕ+) (u : LinearTerm n) : Formula (n + 1) → Formula n
  | verum => verum
  | falsum => falsum
  | pos t => pos (t.coeff 0 • u + ((a : ℕ) : ℤ) • t.tail)
  | dvd b m t => dvd b (a * m) (t.coeff 0 • u + ((a : ℕ) : ℤ) • t.tail)
  | and φ ψ => and (φ.substDiv a u) (ψ.substDiv a u)
  | or φ ψ => or (φ.substDiv a u) (ψ.substDiv a u)

/-- The formula without its first variable, which is quantified existentially. -/
def elim (φ : Formula (n + 1)) : Formula n :=
  or (disj <| (List.range φ.modLcm).map fun j : ℕ ↦ φ.minusInf.substDiv 1 (ofInt (j + 1)))
    (disj <| φ.lowers.flatMap fun p ↦ (List.range (p.1 * φ.modLcm)).map fun j : ℕ ↦
      and (dvd true p.1 (ofInt (j + 1) - p.2)) (φ.substDiv p.1 (ofInt (j + 1) - p.2)))

/-- The formula without its first variable, which is quantified universally. -/
def all (φ : Formula (n + 1)) : Formula n := φ.neg.elim.neg

/-- The formula without its first `k` variables, which are quantified existentially. -/
def exsN : (k : ℕ) → Formula (k + n) → Formula n
  | 0, φ => φ.rename (Fin.cast (Nat.zero_add n))
  | k + 1, φ => exsN k (φ.rename (Fin.cast (Nat.add_right_comm k 1 n))).elim

section

variable [IsStrictOrderedRing R] {x x' : R} {a : ℕ+} {u : LinearTerm n} {d : ℕ}

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma cast_toNat {c : ℤ} (hc : 0 < c) : ((c.toNat : ℕ) : R) = (c : R) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hc.le]

lemma eval_substDiv (h : (a : ℕ) * x = u.eval v) (φ : Formula (n + 1)) :
    (φ.substDiv a u).eval v ↔ φ.eval (Matrix.vecCons x v) := by
  have ha : (0 : R) < (a : ℕ) := by exact_mod_cast a.pos
  induction φ with
  | verum => simp [substDiv]
  | falsum => simp [substDiv]
  | pos t =>
    have e : (t.coeff 0 : R) * u.eval v + (a : ℕ) * t.tail.eval v =
        (a : ℕ) * (t.coeff 0 * x + t.tail.eval v) := by
      rw [← h]
      ring
    simp [substDiv, eval_cons, e, mul_pos_iff_of_pos_left ha]
  | dvd b m t =>
    have e : (t.coeff 0 : R) * u.eval v + (a : ℕ) * t.tail.eval v =
        (a : ℕ) * (t.coeff 0 * x + t.tail.eval v) := by
      rw [← h]
      ring
    simp [substDiv, eval_cons, e, mul_dvd_mul_iff_left ha.ne']
  | and φ ψ ihφ ihψ => simp [substDiv, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [substDiv, ihφ, ihψ]

omit [LinearOrder R] [IsStrictOrderedRing R] in
lemma dvd_add_mul_iff {m : ℕ} (h : m ∣ d) (c y k : R) :
    (m : R) ∣ c * (x + d * k) + y ↔ (m : R) ∣ c * x + y := by
  have : (m : R) ∣ c * (d * k) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.cast_dvd_cast h) k) c
  rw [show c * (x + d * k) + y = c * x + y + c * (d * k) by ring]
  exact dvd_add_left this

omit [IsStrictOrderedRing R] in
lemma eval_minusInf_add (φ : Formula (n + 1)) (h : φ.modLcm ∣ d) (k : R) :
    φ.minusInf.eval (Matrix.vecCons (x + d * k) v) ↔ φ.minusInf.eval (Matrix.vecCons x v) := by
  induction φ with
  | verum => simp [minusInf]
  | falsum => simp [minusInf]
  | pos t =>
    simp only [minusInf]
    split_ifs with h₁ h₂
    · simp
    · simp
    · have : t.coeff 0 = 0 := by omega
      simp [eval_cons, this]
  | dvd b m t =>
    have h : (m : ℕ) ∣ d := h
    simp [minusInf, eval_cons, dvd_add_mul_iff h]
  | and φ ψ ihφ ihψ =>
    simp [minusInf, ihφ ((Nat.dvd_lcm_left _ _).trans h), ihψ ((Nat.dvd_lcm_right _ _).trans h)]
  | or φ ψ ihφ ihψ =>
    simp [minusInf, ihφ ((Nat.dvd_lcm_left _ _).trans h), ihψ ((Nat.dvd_lcm_right _ _).trans h)]

lemma eval_of_le (φ : Formula (n + 1)) (h : φ.modLcm ∣ d) (hx : x' ≤ x) {k : R}
    (hk : x = x' + d * k) (hφ : φ.eval (Matrix.vecCons x v))
    (hl : ∀ p ∈ φ.lowers, 0 < ((p.1 : ℕ) : R) * x + p.2.eval v →
      0 < ((p.1 : ℕ) : R) * x' + p.2.eval v) : φ.eval (Matrix.vecCons x' v) := by
  induction φ with
  | verum => trivial
  | falsum => exact hφ
  | pos t =>
    simp only [eval, eval_cons] at hφ ⊢
    by_cases hc : 0 < t.coeff 0
    · have e := cast_toNat (R := R) hc
      have H := hl (⟨(t.coeff 0).toNat, by omega⟩, t.tail) (by simp [lowers, hc])
      change 0 < (((t.coeff 0).toNat : ℕ) : R) * x + _ →
        0 < (((t.coeff 0).toNat : ℕ) : R) * x' + _ at H
      rw [e] at H
      exact H hφ
    · have hc' : (t.coeff 0 : R) ≤ 0 := Int.cast_nonpos.mpr (not_lt.mp hc)
      nlinarith [mul_nonneg (neg_nonneg.mpr hc') (sub_nonneg.mpr hx)]
  | dvd b m t =>
    have h : (m : ℕ) ∣ d := h
    simp only [eval, eval_cons] at hφ ⊢
    rw [hφ, hk, dvd_add_mul_iff h]
  | and φ ψ ihφ ihψ =>
    exact ⟨ihφ ((Nat.dvd_lcm_left _ _).trans h) hφ.1 fun p hp ↦ hl p (by simp [lowers, hp]),
      ihψ ((Nat.dvd_lcm_right _ _).trans h) hφ.2 fun p hp ↦ hl p (by simp [lowers, hp])⟩
  | or φ ψ ihφ ihψ =>
    rcases hφ with hφ | hφ
    · exact .inl <| ihφ ((Nat.dvd_lcm_left _ _).trans h) hφ fun p hp ↦
        hl p (by simp [lowers, hp])
    · exact .inr <| ihψ ((Nat.dvd_lcm_right _ _).trans h) hφ fun p hp ↦
        hl p (by simp [lowers, hp])

omit [IsStrictOrderedRing R] in
lemma eval_minusInf_of_lowers (φ : Formula (n + 1)) (hφ : φ.eval (Matrix.vecCons x v))
    (hl : ∀ p ∈ φ.lowers, ¬0 < ((p.1 : ℕ) : R) * x + p.2.eval v) :
    φ.minusInf.eval (Matrix.vecCons x v) := by
  induction φ with
  | verum => trivial
  | falsum => exact hφ
  | pos t =>
    simp only [minusInf]
    split_ifs with hc h₂
    · have e := cast_toNat (R := R) hc
      have H := hl (⟨(t.coeff 0).toNat, by omega⟩, t.tail) (by simp [lowers, hc])
      change ¬0 < (((t.coeff 0).toNat : ℕ) : R) * x + _ at H
      rw [e] at H
      exact absurd (by simpa [eval_cons] using hφ) H
    · trivial
    · exact hφ
  | dvd b m t => exact hφ
  | and φ ψ ihφ ihψ =>
    exact ⟨ihφ hφ.1 fun p hp ↦ hl p (by simp [lowers, hp]),
      ihψ hφ.2 fun p hp ↦ hl p (by simp [lowers, hp])⟩
  | or φ ψ ihφ ihψ =>
    rcases hφ with hφ | hφ
    · exact .inl <| ihφ hφ fun p hp ↦ hl p (by simp [lowers, hp])
    · exact .inr <| ihψ hφ fun p hp ↦ hl p (by simp [lowers, hp])

lemma exists_minusInf_imp (φ : Formula (n + 1)) (v : Fin n → R) :
    ∃ z : R, ∀ x ≤ z, φ.minusInf.eval (Matrix.vecCons x v) → φ.eval (Matrix.vecCons x v) := by
  induction φ with
  | verum => exact ⟨0, fun _ _ h ↦ h⟩
  | falsum => exact ⟨0, fun _ _ h ↦ h⟩
  | pos t =>
    simp only [minusInf]
    split_ifs with hc h₂
    · exact ⟨0, fun _ _ h ↦ h.elim⟩
    · use -|t.tail.eval v| - 1
      intro x hx _
      have hc' : (t.coeff 0 : R) + 1 ≤ 0 := by exact_mod_cast Int.add_one_le_iff.mpr h₂
      have := neg_abs_le (t.tail.eval v)
      have := abs_nonneg (t.tail.eval v)
      simp only [eval, eval_cons]
      nlinarith [mul_nonneg (neg_nonneg.mpr hc') (neg_nonneg.mpr (show x ≤ 0 by linarith))]
    · exact ⟨0, fun _ _ h ↦ h⟩
  | dvd b m t => exact ⟨0, fun _ _ h ↦ h⟩
  | and φ ψ ihφ ihψ =>
    obtain ⟨z₁, h₁⟩ := ihφ
    obtain ⟨z₂, h₂⟩ := ihψ
    exact ⟨min z₁ z₂, fun x hx h ↦
      ⟨h₁ x (hx.trans (min_le_left _ _)) h.1, h₂ x (hx.trans (min_le_right _ _)) h.2⟩⟩
  | or φ ψ ihφ ihψ =>
    obtain ⟨z₁, h₁⟩ := ihφ
    obtain ⟨z₂, h₂⟩ := ihψ
    exact ⟨min z₁ z₂, fun x hx h ↦
      h.imp (h₁ x (hx.trans (min_le_left _ _))) (h₂ x (hx.trans (min_le_right _ _)))⟩

variable [PresburgerRing R]

/-- A lower bound that holds at `x` holds at some `y ≤ x` congruent to `x` and near the bound. -/
lemma exists_le_of_lower (hd : 0 < d) (c : ℕ+) (y : R) (h : 0 < ((c : ℕ) : R) * x + y) :
    ∃ x' ≤ x, ∃ k : R, ∃ r : ℕ, x = x' + d * k ∧ r < c * d ∧ ((c : ℕ) : R) * x' + y = r + 1 := by
  obtain ⟨q, r, hr, e⟩ := PresburgerRing.exists_eq_mul_add (c * d) (Nat.mul_pos c.pos hd)
    (((c : ℕ) : R) * x + y - 1)
  have hc : (0 : R) < ((c * d : ℕ) : R) := by exact_mod_cast Nat.mul_pos c.pos hd
  have hd' : (0 : R) < (d : R) := by exact_mod_cast hd
  have hr' : (r : R) + 1 ≤ ((c * d : ℕ) : R) := by exact_mod_cast hr
  have h1 := PresburgerRing.one_le_of_pos h
  have hq : 0 ≤ q := by
    by_contra hq
    have := PresburgerRing.one_le_of_pos (neg_pos.mpr (not_le.mp hq))
    nlinarith [mul_le_mul_of_nonneg_left this hc.le]
  use x - d * q
  and_intros
  · nlinarith [mul_nonneg hd'.le hq]
  · use q, r
    and_intros
    · ring
    · exact hr
    · push_cast at e ⊢
      linarith

/--
A formula without its first variable is true exactly when the formula is true for some value of
that variable.
-/
theorem eval_elim (φ : Formula (n + 1)) : φ.elim.eval v ↔ ∃ x : R, φ.eval (Matrix.vecCons x v) := by
  classical
  have hδ := φ.modLcm_pos
  have hδ' : (1 : R) ≤ (φ.modLcm : R) := by exact_mod_cast hδ
  simp only [elim, eval, eval_disj, List.mem_map, List.mem_range, List.mem_flatMap]
  constructor
  · rintro (⟨_, ⟨j, -, rfl⟩, h⟩ | ⟨_, ⟨p, -, j, -, rfl⟩, h₁, h₂⟩)
    · have h := (eval_substDiv (x := ((j : R) + 1)) (by simp) φ.minusInf).mp h
      obtain ⟨z, hz⟩ := φ.exists_minusInf_imp v
      have hK := le_abs_self ((j : R) + 1 - z)
      have hK' := abs_nonneg ((j : R) + 1 - z)
      use (j : R) + 1 + φ.modLcm * -(|(j : R) + 1 - z| + 1)
      apply hz
      · nlinarith [mul_le_mul_of_nonneg_right hδ' (show 0 ≤ |(j : R) + 1 - z| + 1 by linarith)]
      · exact (eval_minusInf_add φ dvd_rfl _).mpr h
    · obtain ⟨x, hx⟩ := h₁.mp rfl
      use x
      apply (eval_substDiv _ φ).mp h₂
      rw [hx]
  · rintro ⟨x, hx⟩
    by_cases hl : ∀ p ∈ φ.lowers, ¬0 < ((p.1 : ℕ) : R) * x + p.2.eval v
    · left
      obtain ⟨q, r, hr, e⟩ := PresburgerRing.exists_eq_mul_add φ.modLcm hδ (x - 1)
      use φ.minusInf.substDiv 1 (ofInt (r + 1))
      and_intros
      · exact ⟨r, hr, rfl⟩
      · apply (eval_substDiv (x := ((r : R) + 1)) (by simp) φ.minusInf).mpr
        apply (eval_minusInf_add φ dvd_rfl q).mp
        rw [show (r : R) + 1 + φ.modLcm * q = x by linarith]
        exact eval_minusInf_of_lowers φ hx hl
    · right
      have H : ∀ p : ℕ+ × LinearTerm n, 0 < ((p.1 : ℕ) : R) * x + p.2.eval v →
          ∃ x' ≤ x, ∃ k : R, ∃ r : ℕ, x = x' + φ.modLcm * k ∧ r < p.1 * φ.modLcm ∧
            ((p.1 : ℕ) : R) * x' + p.2.eval v = r + 1 := fun p hp ↦
        exists_le_of_lower hδ p.1 _ hp
      choose! f hf k r hk hr hfr using H
      have hne : (φ.lowers.toFinset.filter
          fun p ↦ 0 < ((p.1 : ℕ) : R) * x + p.2.eval v).Nonempty := by
        push Not at hl
        obtain ⟨p, hp, h⟩ := hl
        exact ⟨p, by simp [hp, h]⟩
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ f hne
      simp only [Finset.mem_filter, List.mem_toFinset] at hp hmax
      use and (dvd true p.1 (ofInt (r p + 1) - p.2)) (φ.substDiv p.1 (ofInt (r p + 1) - p.2))
      have e : ((p.1 : ℕ) : R) * f p = (ofInt (r p + 1) - p.2 : LinearTerm n).eval v := by
        have := hfr p hp.2
        simp only [eval_sub, eval_ofInt]
        push_cast
        linarith
      and_intros
      · exact ⟨p, hp.1, r p, hr p hp.2, rfl⟩
      · simp only [eval, true_iff]
        exact ⟨f p, e.symm⟩
      · apply (eval_substDiv e φ).mpr
        apply eval_of_le φ dvd_rfl (hf p hp.2) (hk p hp.2) hx
        intro p' hp' h
        have h₁ := hmax p' ⟨hp', h⟩
        have h₂ := hfr p' h
        have h₃ : (0 : R) ≤ ((p'.1 : ℕ) : R) := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h₁ h₃]

@[simp]
lemma eval_all (φ : Formula (n + 1)) : φ.all.eval v ↔ ∀ x : R, φ.eval (Matrix.vecCons x v) := by
  simp [all, eval_elim]

@[simp]
lemma eval_exsN {k : ℕ} (φ : Formula (k + n)) :
    (exsN k φ).eval v ↔ ∃ w : Fin k → R, φ.eval (Fin.append w v) := by
  induction k with
  | zero =>
    simp only [exsN, eval_rename]
    constructor
    · intro h
      use Fin.elim0
      rwa [Fin.elim0_append]
    · rintro ⟨w, h⟩
      rwa [Subsingleton.elim w Fin.elim0, Fin.elim0_append] at h
  | succ k ih =>
    simp only [exsN, ih, eval_elim, eval_rename, Fin.exists_fin_succ_pi]
    rw [exists_comm]
    simp only [Fin.append_cons]
    rfl

lemma natCast_dvd_intCast {m : ℕ} (hm : 0 < m) {k : ℤ} : (m : R) ∣ (k : R) ↔ (m : ℤ) ∣ k := by
  constructor
  · rintro ⟨q, hq⟩
    have hm' : (0 : R) < (m : R) := by exact_mod_cast hm
    have h₁ : 0 ≤ k % m := Int.emod_nonneg k (by omega)
    have h₂ : ((k % m : ℤ) : R) < (m : R) := by exact_mod_cast Int.emod_lt_of_pos k (by omega)
    have e : ((k % m : ℤ) : R) = m * (q - ((k / m : ℤ) : R)) := by
      have : ((m * (k / m) + k % m : ℤ) : R) = k := by rw [Int.mul_ediv_add_emod]
      push_cast at this
      linarith
    apply Int.dvd_of_emod_eq_zero
    by_contra hne
    have h₃ : (0 : R) < ((k % m : ℤ) : R) := by exact_mod_cast lt_of_le_of_ne h₁ (Ne.symm hne)
    have := PresburgerRing.one_le_of_pos <| (mul_pos_iff_of_pos_left hm').mp (e ▸ h₃)
    nlinarith
  · rintro ⟨c, rfl⟩
    exact ⟨c, by push_cast; ring⟩

/-- The truth value of a formula without variables is the same in every Presburger ring. -/
theorem eval_iff_eval_int (φ : Formula 0) (v : Fin 0 → R) (w : Fin 0 → ℤ) :
    φ.eval v ↔ φ.eval w := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | pos t => simp [LinearTerm.eval_zero]
  | dvd b m t => simp [LinearTerm.eval_zero, natCast_dvd_intCast m.pos]
  | and φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [ihφ, ihψ]

end

end Formula

end Presburger

module

public import Concatenation.Semantics.Standard
public import Concatenation.TC.FiniteModel
public import Concatenation.ToFoundation.Arithmetic.R0.LocallyFinitelySatisfiable
public import Concatenation.WTC.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.List

/-!
# $\mathsf{WTC}$ does not interpret $\mathsf{TC}$

$\mathsf{WTC}$ is locally finitely satisfiable, so it interprets neither $\mathsf{TC}$ nor
$\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

namespace WTC

/--
The nonempty binary strings of length at most `N`, and an absorbing element for the longer ones.
-/
inductive Truncation (N : ℕ) : Type
  | string (x : FreeSemigroup Bool) (hx : x.length ≤ N) : Truncation N
  | long : Truncation N

namespace Truncation

variable {N : ℕ} {a b c : Truncation N} {x y u : FreeSemigroup Bool}

instance : Nonempty (Truncation N) := ⟨long⟩

instance : Finite (Truncation N) :=
  have : Finite {l : List Bool // l.length ≤ N} := List.finite_length_le Bool N
  let f : Truncation N → Option {l : List Bool // l.length ≤ N}
    | string x hx => some ⟨x.toList, hx⟩
    | long => none
  .of_injective f <| by
    rintro (_ | _) (_ | _) <;> simp [f, FreeSemigroup.toList_inj, Subtype.ext_iff]

/-- The string `x`, if it is of length at most `N`, and the absorbing element otherwise. -/
def of (N : ℕ) (x : FreeSemigroup Bool) : Truncation N :=
  if h : x.length ≤ N then string x h else long

instance : ConcatenationStructure (Truncation N) where
  zero := of N 0
  one := of N 1
  append
    | string x _, string y _ => of N (x * y)
    | _, _ => long

lemma zero_eq : (0 : Truncation N) = of N 0 := rfl

lemma one_eq : (1 : Truncation N) = of N 1 := rfl

@[simp]
lemma long_append (a : Truncation N) : long ++ a = long := rfl

@[simp]
lemma append_long (a : Truncation N) : a ++ long = long := by cases a <;> rfl

lemma of_of_le (h : x.length ≤ N) : of N x = string x h := by simp [of, h]

lemma of_of_lt (h : N < x.length) : of N x = long := by simp [of, h]

lemma of_append_of (x y : FreeSemigroup Bool) : of N x ++ of N y = of N (x * y) := by
  have h : (x * y).length = x.length + y.length := FreeSemigroup.length_mul x y
  rcases le_or_gt x.length N with hx | hx
  · rcases le_or_gt y.length N with hy | hy
    · rw [of_of_le hx, of_of_le hy]
      rfl
    · rw [of_of_lt hy, append_long, of_of_lt <| by omega]
  · rw [of_of_lt hx, long_append, of_of_lt <| by omega]

lemma of_inj (hx : x.length ≤ N) : of N x = of N y ↔ x = y := by
  by_cases hy : y.length ≤ N
  · simp [of, hx, hy]
  · simp only [of, hx, hy]
    grind

lemma exists_of (a : Truncation N) : ∃ x, a = of N x := by
  cases a with
  | string x hx => exact ⟨x, (of_of_le hx).symm⟩
  | long =>
    use ⟨false, List.replicate N false⟩
    exact (of_of_lt <| by simp [FreeSemigroup.length]).symm

@[simp]
lemma ofFreeSemigroup_eq (u : FreeSemigroup Bool) :
    (ConcatenationStructure.ofFreeSemigroup u : Truncation N) = of N u := by
  have h₀ (b : Bool) : (if b then 1 else 0 : Truncation N) = of N (FreeSemigroup.of b) := by
    cases b <;> rfl
  have h (l : List Bool) (x : FreeSemigroup Bool) :
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (of N x) = of N ⟨x.head, x.tail ++ l⟩ := by
    induction l generalizing x with
    | nil => simp
    | cons b l ih =>
      rw [List.foldl_cons, h₀, of_append_of, ih]
      congr 2
      simp [FreeSemigroup.of]
  rw [ConcatenationStructure.ofFreeSemigroup, h₀, h]
  simp [FreeSemigroup.of]

protected lemma append_assoc (a b c : Truncation N) : a ++ b ++ c = a ++ (b ++ c) := by
  obtain ⟨x, rfl⟩ := exists_of a
  obtain ⟨y, rfl⟩ := exists_of b
  obtain ⟨z, rfl⟩ := exists_of c
  simp only [of_append_of, mul_assoc]

lemma exists_of_append_eq (hu : u.length ≤ N) (h : a ++ b = of N u) :
    ∃ x y, a = of N x ∧ b = of N y ∧ x * y = u := by
  obtain ⟨x, rfl⟩ := exists_of a
  obtain ⟨y, rfl⟩ := exists_of b
  exact ⟨x, y, rfl, rfl, ((of_inj hu).mp <| by rw [← of_append_of, h]).symm⟩

lemma exists_of_isSubstring (hu : u.length ≤ N) (h : IsSubstring a (of N u)) :
    ∃ x, x.length ≤ N ∧ a = of N x := by
  rcases h with rfl | ⟨b, h⟩ | ⟨b, h⟩ | ⟨b, c, h⟩ | ⟨b, c, h⟩
  · exact ⟨u, hu, rfl⟩
  · obtain ⟨x, y, -, rfl, rfl⟩ := exists_of_append_eq hu h.symm
    rw [FreeSemigroup.length_mul] at hu
    exact ⟨y, by omega, rfl⟩
  · obtain ⟨x, y, rfl, -, rfl⟩ := exists_of_append_eq hu h.symm
    rw [FreeSemigroup.length_mul] at hu
    exact ⟨x, by omega, rfl⟩
  · obtain ⟨_, z, h', -, rfl⟩ := exists_of_append_eq hu h.symm
    obtain ⟨x, y, -, rfl, rfl⟩ := exists_of_append_eq (by simp at hu; omega) h'
    exact ⟨y, by simp at hu; omega, rfl⟩
  · obtain ⟨z, _, -, h', rfl⟩ := exists_of_append_eq hu h.symm
    obtain ⟨x, y, rfl, -, rfl⟩ := exists_of_append_eq (by simp at hu; omega) h'
    exact ⟨x, by simp at hu; omega, rfl⟩

lemma editor (hu : u.length ≤ N) {d : Truncation N} (h : a ++ b = c ++ d)
    (hs : IsSubstring (a ++ b) (of N u)) :
    (a = c ∧ b = d) ∨ ∃ w, (a ++ w = c ∧ b = w ++ d) ∨ (a = c ++ w ∧ w ++ b = d) := by
  obtain ⟨v, hv, hab⟩ := exists_of_isSubstring hu hs
  obtain ⟨x, y, rfl, rfl, rfl⟩ := exists_of_append_eq hv hab
  obtain ⟨z, w, rfl, rfl, hzw⟩ := exists_of_append_eq hv (h.symm.trans hab)
  rcases FreeSemigroup.mul_eq_mul_iff.mp hzw.symm with ⟨rfl, rfl⟩ | ⟨t, h⟩
  · simp
  · right
    use of N t
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [of_append_of]

lemma append_ne_of (hu : u.length = 1) (hN : 1 ≤ N) : a ++ b ≠ of N u := by
  intro h
  obtain ⟨x, y, -, -, rfl⟩ := exists_of_append_eq (hu.le.trans hN) h
  rw [FreeSemigroup.length_mul] at hu
  have hx : 0 < x.length := Nat.succ_pos _
  have hy : 0 < y.length := Nat.succ_pos _
  omega

lemma zero_ne_one (hN : 1 ≤ N) : (0 : Truncation N) ≠ 1 := by
  rw [zero_eq, one_eq, Ne, of_inj (by simpa [zero_eq_of_false] using hN)]
  simp [zero_eq_of_false, one_eq_of_true, FreeSemigroup.of]

end Truncation

/--
$\mathsf{WTC}$ is locally finitely satisfiable.
- [Hor11, §3, Corollary 3.16]
- [Hor12, §4, Theorem 4.10]
-/
theorem locallyFinitelySatisfiable : (𝗪𝗧𝗖 : ConcatenationTheory).LocallyFinitelySatisfiable := by
  apply Theory.LocallyFinitelySatisfiable.of_eventually Truncation
  rintro σ ⟨⟩
  case equal h =>
    have (N : ℕ) : (Truncation N)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact .of_forall fun N ↦ models_theory_iff.mp (this N) _ h
  case concatAssoc u => simp [models_iff, Truncation.append_assoc]
  case editor u =>
    filter_upwards [Filter.eventually_ge_atTop u.length] with N hN
    simpa [models_iff] using fun a b c d ↦ Truncation.editor (N := N) hN
  case concatNeZero =>
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simpa [models_iff, Truncation.zero_eq] using fun a b ↦ Truncation.append_ne_of rfl hN
  case concatNeOne =>
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simpa [models_iff, Truncation.one_eq] using fun a b ↦ Truncation.append_ne_of rfl hN
  case zeroNeOne =>
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    simpa [models_iff] using Truncation.zero_ne_one hN

end WTC

/--
$\mathsf{WTC}$ does not interpret $\mathsf{TC}$.
- [Hor11, §3, Corollary 3.17]
- [Hor12, §4, Corollary 4.11]
-/
theorem isEmpty_WTC_interprets_TC : IsEmpty (𝗪𝗧𝗖 ⊳ 𝗧𝗖) :=
  DirectInterpretation.isEmpty_of_not_hasFiniteModel WTC.locallyFinitelySatisfiable
    finiteAxiomatizable_TC not_hasFiniteModel_TC

theorem isEmpty_WTC_interprets_Q : IsEmpty (𝗪𝗧𝗖 ⊳ 𝗤) :=
  DirectInterpretation.isEmpty_of_not_hasFiniteModel WTC.locallyFinitelySatisfiable
    Arithmetic.RobinsonQ.finiteAxiomatizable Arithmetic.RobinsonQ.not_hasFiniteModel

theorem isEmpty_R0_interprets_TC : IsEmpty (𝗥₀ ⊳ 𝗧𝗖) :=
  DirectInterpretation.isEmpty_of_not_hasFiniteModel Arithmetic.R0.locallyFinitelySatisfiable
    finiteAxiomatizable_TC not_hasFiniteModel_TC

end FFL.FirstOrder.Concatenation

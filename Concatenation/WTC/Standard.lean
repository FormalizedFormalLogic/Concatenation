module

public import Concatenation.TC.Substring
public import Concatenation.ToFoundation.Arithmetic.R0.LocallyFinitelySatisfiable
public import Concatenation.WTC.Basic
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Set.Finite.List

/-!
# Standard strings and $\Sigma_1$-completeness of $\mathsf{WTC}$

The standard strings form an initial part of every model of $\mathsf{WTC}$, so that $\mathsf{WTC}$
is $\Sigma_1$-complete; $\mathsf{WTC}$ is locally finitely satisfiable, so it does not interpret
$\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

namespace WTC

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {a b c u v : FreeSemigroup Bool} {s t x y z : M}

@[simp]
lemma ofFreeSemigroup_zero : (ofFreeSemigroup (0 : FreeSemigroup Bool) : M) = 0 := rfl

@[simp]
lemma ofFreeSemigroup_one : (ofFreeSemigroup (1 : FreeSemigroup Bool) : M) = 1 := rfl

lemma ofFreeSemigroup_append_of_isAtom (u : FreeSemigroup Bool) (hc : IsAtom c) :
    (ofFreeSemigroup (u ++ c) : M) = ofFreeSemigroup u ++ ofFreeSemigroup c := by
  rcases hc with rfl | rfl <;>
    simp [ofFreeSemigroup, stringValue, HMul.hMul, Mul.mul, zero_eq_of_false, one_eq_of_true,
      FreeSemigroup.of]

/-- Induction on a nonempty binary string by its last letter. -/
@[elab_as_elim]
lemma atom_append_induction {motive : FreeSemigroup Bool → Prop} (u : FreeSemigroup Bool)
    (atom : ∀ c, IsAtom c → motive c)
    (append : ∀ u c, IsAtom c → motive u → motive (u ++ c)) : motive u := by
  have h (b : Bool) : IsAtom (FreeSemigroup.of b) := by
    cases b
    · exact isAtom_zero
    · exact isAtom_one
  rcases u with ⟨b, l⟩
  induction l using List.reverseRecOn with
  | nil => exact atom _ <| h b
  | append_singleton l d ih => exact append _ _ (h d) ih

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

lemma append_assoc (u : FreeSemigroup Bool) (h : IsSubstring (x ++ y ++ z) (ofFreeSemigroup u) ∨
    IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup u)) : x ++ y ++ z = x ++ (y ++ z) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCAxiom.concatAssoc u)
  exact this x y z h

lemma editor (u : FreeSemigroup Bool) (h : x ++ y = s ++ t)
    (hu : IsSubstring (x ++ y) (ofFreeSemigroup u)) : (x = s ∧ y = t) ∨
    ∃ w, (x ++ w = s ∧ y = w ++ t) ∨ (x = s ++ w ∧ w ++ y = t) := by
  have := by simpa [models_iff] using Theory.models M _ (IsWTCAxiom.editor u)
  exact this x y s t h hu

lemma append_ne_zero (x y : M) : x ++ y ≠ 0 := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCAxiom.concatNeZero
  exact this x y

lemma append_ne_one (x y : M) : x ++ y ≠ 1 := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCAxiom.concatNeOne
  exact this x y

protected lemma zero_ne_one : (0 : M) ≠ 1 := by
  simpa [models_iff] using Theory.models M _ IsWTCAxiom.zeroNeOne

lemma append_ne_ofFreeSemigroup (hc : IsAtom c) : x ++ y ≠ ofFreeSemigroup c := by
  rcases hc with rfl | rfl
  · exact append_ne_zero x y
  · exact append_ne_one x y

@[simp]
lemma ofFreeSemigroup_mul (u v : FreeSemigroup Bool) :
    (ofFreeSemigroup (u * v) : M) = ofFreeSemigroup u ++ ofFreeSemigroup v := by
  induction v using atom_append_induction with
  | atom c hc => exact ofFreeSemigroup_append_of_isAtom u hc
  | append v c hc ih =>
    have h := ofFreeSemigroup_append_of_isAtom (M := M) (u * v) hc
    rw [append_eq_mul, ih] at h
    rw [append_eq_mul, ← mul_assoc, h, ← append_eq_mul v, ofFreeSemigroup_append_of_isAtom v hc]
    apply append_assoc (u * v * c)
    left
    rw [h]

lemma ofFreeSemigroup_injective :
    Function.Injective (ofFreeSemigroup : FreeSemigroup Bool → M) := by
  intro u
  induction u using atom_append_induction with
  | atom c hc =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd =>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · rfl
      · exact absurd h WTC.zero_ne_one
      · exact absurd h.symm WTC.zero_ne_one
      · rfl
    | append v d hd => exact absurd (by simpa using h.symm) (append_ne_ofFreeSemigroup (M := M) hc)
  | append u c hc ih =>
    intro v h
    induction v using atom_append_induction with
    | atom d hd => exact absurd (by simpa using h) (append_ne_ofFreeSemigroup (M := M) hd)
    | append v d hd =>
      simp only [append_eq_mul, ofFreeSemigroup_mul] at h
      rcases editor (u * c) h (by simp) with ⟨h₁, h₂⟩ | ⟨w, ⟨-, h⟩ | ⟨-, h⟩⟩
      · rw [ih h₁]
        rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
        · rfl
        · exact absurd h₂ WTC.zero_ne_one
        · exact absurd h₂.symm WTC.zero_ne_one
        · rfl
      · exact absurd h.symm (append_ne_ofFreeSemigroup hc)
      · exact absurd h (append_ne_ofFreeSemigroup hd)

@[simp]
lemma ofFreeSemigroup_inj : (ofFreeSemigroup u : M) = ofFreeSemigroup v ↔ u = v :=
  ofFreeSemigroup_injective.eq_iff

/--
If a concatenation is standard, then so are both parts.
- [Hor12, §3, Lemma 3.11]
-/
lemma exists_of_append_eq_ofFreeSemigroup (h : x ++ y = ofFreeSemigroup u) :
    ∃ a b, x = ofFreeSemigroup a ∧ y = ofFreeSemigroup b ∧ u = a * b := by
  induction u using atom_append_induction generalizing y with
  | atom c hc => exact absurd h (append_ne_ofFreeSemigroup hc)
  | append u c hc ih =>
    simp only [append_eq_mul, ofFreeSemigroup_mul] at h
    rcases editor (u * c) h (by simp [h]) with ⟨rfl, rfl⟩ | ⟨w, ⟨hw, rfl⟩ | ⟨-, hw⟩⟩
    · use u, c
      simp
    · obtain ⟨a, b, rfl, rfl, rfl⟩ := ih hw
      use a, b * c
      simp [mul_assoc]
    · exact absurd hw (append_ne_ofFreeSemigroup hc)

/--
The substrings of a standard string are the values of its substrings.
- [Hor12, §3, Lemma 3.11]
-/
lemma isSubstring_ofFreeSemigroup_iff :
    IsSubstring x (ofFreeSemigroup u) ↔ ∃ v, x = ofFreeSemigroup v ∧ IsSubstring v u := by
  constructor
  · intro h
    apply h.of_forall_append (P := fun x ↦ ∃ v, x = ofFreeSemigroup v ∧ IsSubstring v u) _
      ⟨u, rfl, .refl u⟩
    rintro x y ⟨v, h, hv⟩
    obtain ⟨a, b, rfl, rfl, rfl⟩ := exists_of_append_eq_ofFreeSemigroup h
    exact ⟨⟨a, rfl, (isSubstring_append_left a b).trans hv⟩,
      ⟨b, rfl, (isSubstring_append_right a b).trans hv⟩⟩
  · rintro ⟨v, rfl, h⟩
    rcases isSubstring_iff.mp h with rfl | ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, b, rfl⟩ <;> simp

@[simp]
lemma isSubstring_ofFreeSemigroup_ofFreeSemigroup_iff :
    IsSubstring (ofFreeSemigroup u : M) (ofFreeSemigroup v) ↔ IsSubstring u v := by
  simp [isSubstring_ofFreeSemigroup_iff]

@[simp]
lemma isAtom_ofFreeSemigroup_iff : IsAtom (ofFreeSemigroup u : M) ↔ IsAtom u := by
  rw [IsAtom, IsAtom, ← ofFreeSemigroup_zero, ← ofFreeSemigroup_one, ofFreeSemigroup_inj,
    ofFreeSemigroup_inj]

@[simp]
lemma isTally_ofFreeSemigroup_iff :
    IsTally (ofFreeSemigroup c : M) (ofFreeSemigroup u) ↔ IsTally c u := by
  constructor
  · intro h v hv hvu
    simpa using h (ofFreeSemigroup v) (by simpa) (by simpa)
  · intro h y hy hyu
    obtain ⟨v, rfl, hvu⟩ := isSubstring_ofFreeSemigroup_iff.mp hyu
    rw [h v (isAtom_ofFreeSemigroup_iff.mp hy) hvu]

end WTC

section sigma1

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {ξ : Type*} {n : ℕ}

/-- The substring relation as an operator. -/
def substringOperator (L : Language) [L.Eq] [L.Concat] : Semiformula.Operator L 2 := ⟨isSubstring⟩

@[simp]
lemma val_substringOperator {v : Fin 2 → M} :
    (substringOperator ℒ⌢).val v ↔ IsSubstring (v 0) (v 1) := by
  rw [Matrix.fun_eq_vec_two (v := v)]
  exact eval_isSubstring

/--
Quantifiers bounded by the substring relation. `ℬ[⊑, L].PrenexHierarchy 𝚺 0` is the class
of $\Sigma_0$ formulas, and `ℬ[⊑, L].PrenexHierarchy 𝚺 1` the class of $\Sigma_1$ formulas.
- [Hor11, §3]
- [Hor12, §3]
-/
def substringBounding (L : Language) [L.Eq] [L.Concat] : Bounding L := ⟨{substringOperator L}⟩

@[inherit_doc]
scoped notation "ℬ[⊑, " L "]" => substringBounding L

@[simp]
lemma mem_substringBounding_iff {R : Semiformula.Operator ℒ⌢ 2} :
    R ∈ ℬ[⊑, ℒ⌢] ↔ R = substringOperator ℒ⌢ := Iff.rfl

namespace WTC

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] {e : Fin n → FreeSemigroup Bool} {ε : ξ → FreeSemigroup Bool}
  {φ : Semiformula ℒ⌢ ξ n}

lemma val_ofFreeSemigroup (t : Semiterm ℒ⌢ ξ n) :
    t.val (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) = (ofFreeSemigroup (t.val e ε) : M) := by
  induction t with
  | bvar => simp
  | fvar => simp
  | @func k f v ih =>
    match k, f with
    | _, Language.Zero.zero => simp
    | _, Language.One.one => simp
    | _, Language.Concat.concat => simp [ih]

/-- $\Sigma_0$ formulas are absolute for the standard strings. -/
lemma eval_ofFreeSemigroup_iff_of_closure (hφ : ℬ[⊑, ℒ⌢].Closure φ) :
    φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) ↔ φ.Eval e ε := by
  induction hφ with
  | verum => simp
  | falsum => simp
  | @rel _ k r v =>
    match k, r with
    | _, Language.Eq.eq => simp [val_ofFreeSemigroup]
  | @nrel _ k r v =>
    match k, r with
    | _, Language.Eq.eq => simp [val_ofFreeSemigroup]
  | and _ _ ihφ ihψ => simp [ihφ, ihψ]
  | or _ _ ihφ ihψ => simp [ihφ, ihψ]
  | ball hR ht _ ih =>
    obtain rfl := mem_substringBounding_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    simp [val_ofFreeSemigroup, isSubstring_ofFreeSemigroup_iff, ← ih, Matrix.comp_vecCons'']
    grind
  | bexs hR ht _ ih =>
    obtain rfl := mem_substringBounding_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    simp [val_ofFreeSemigroup, isSubstring_ofFreeSemigroup_iff, ← ih, Matrix.comp_vecCons'']

/--
A $\Sigma_1$ formula true of some strings in the standard model is true of their values in every
model of $\mathsf{WTC}$.
- [Hor12, §3, Theorem 3.13]
-/
lemma eval_ofFreeSemigroup_of_hierarchy (hφ : ℬ[⊑, ℒ⌢].Hierarchy 𝚺 1 φ) (h : φ.Eval e ε) :
    φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) := by
  revert e
  apply Bounding.Hierarchy.sigma_succ_induction (s := 0) (P := fun n φ ↦ ∀ {e : Fin n → _},
    φ.Eval e ε → φ.Eval (M := M) (ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε))
  case a => exact hφ
  case hPi =>
    intro n φ hφ e
    exact (eval_ofFreeSemigroup_iff_of_closure <| Bounding.Hierarchy.zero_iff_bounded.mp hφ).mpr
  case hAnd => simp; grind
  case hOr => simp; grind
  case hBall =>
    rintro R rfl n t φ _ ih e h
    have h : ∀ v, IsSubstring v (t.val e ε) → φ.Eval (v :> e) ε := by simpa using h
    suffices ∀ x : M, IsSubstring x (ofFreeSemigroup (t.val e ε)) →
        φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by
      simpa [val_ofFreeSemigroup]
    intro x hx
    obtain ⟨v, rfl, hv⟩ := isSubstring_ofFreeSemigroup_iff.mp hx
    simpa [Matrix.comp_vecCons''] using ih <| h v hv
  case hBexs =>
    rintro R rfl n t φ _ ih e h
    obtain ⟨v, hv, h⟩ : ∃ v, IsSubstring v (t.val e ε) ∧ φ.Eval (v :> e) ε := by simpa using h
    suffices ∃ x : M, IsSubstring x (ofFreeSemigroup (t.val e ε)) ∧
        φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by
      simpa [val_ofFreeSemigroup]
    use ofFreeSemigroup v
    simpa [Matrix.comp_vecCons'', hv] using ih h
  case hExs =>
    intro n φ _ ih e h
    obtain ⟨v, h⟩ : ∃ v, φ.Eval (v :> e) ε := by simpa using h
    suffices ∃ x : M, φ.Eval (x :> ofFreeSemigroup ∘ e) (ofFreeSemigroup ∘ ε) by simpa
    use ofFreeSemigroup v
    simpa [Matrix.comp_vecCons''] using ih h

end WTC

lemma sigma1_completeness_of_hierarchy {T : ConcatenationTheory} [𝗪𝗧𝗖 ⪯ T]
    {σ : ConcatenationSentence}
    (hσ : ℬ[⊑, ℒ⌢].Hierarchy 𝚺 1 σ) (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : T ⊢ σ := by
  have : 𝗘𝗤 ℒ⌢ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖) inferInstance inferInstance
  apply complete.{0}
  intro M _ _
  have : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ModelsTheory.of_provably_subtheory M 𝗪𝗧𝗖 T inferInstance
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    WTC.eval_ofFreeSemigroup_of_hierarchy (M := M) hσ (models_iff.mp h)

/--
$\mathsf{WTC}$, and hence every extension of it, proves the $\Sigma_1$ sentences true of the
nonempty binary strings.
- [Hor11, §3, Theorem 3.8]
- [Hor12, §3, Theorem 3.13]
-/
theorem sigma1_completeness {T : ConcatenationTheory} [𝗪𝗧𝗖 ⪯ T] {σ : ConcatenationSentence}
    (hσ : ℬ[⊑, ℒ⌢].PrenexHierarchy 𝚺 1 σ) (h : (FreeSemigroup Bool)↓[ℒ⌢] ⊧ σ) : T ⊢ σ :=
  sigma1_completeness_of_hierarchy hσ.hierarchy h

end sigma1

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
  apply stringValue_eq_of_map_append
  · rintro (_ | _) <;> rfl
  · exact fun x y ↦ (of_append_of x y).symm

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
  apply h.of_forall_append (P := fun a ↦ ∃ x, x.length ≤ N ∧ a = of N x) _ ⟨u, hu, rfl⟩
  rintro a b ⟨u, hu, h⟩
  obtain ⟨x, y, rfl, rfl, rfl⟩ := exists_of_append_eq hu h
  rw [FreeSemigroup.length_mul] at hu
  exact ⟨⟨x, by omega, rfl⟩, ⟨y, by omega, rfl⟩⟩

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
theorem WTC.notInterprets_TC : 𝗪𝗧𝗖 ⋫ 𝗧𝗖 :=
  DirectInterpretation.notInterprets_of_not_hasFiniteModel WTC.locallyFinitelySatisfiable
    finiteAxiomatizable_TC not_hasFiniteModel_TC

theorem WTC.notInterprets_Q : 𝗪𝗧𝗖 ⋫ 𝗤 :=
  DirectInterpretation.notInterprets_of_not_hasFiniteModel WTC.locallyFinitelySatisfiable
    Arithmetic.RobinsonQ.finiteAxiomatizable Arithmetic.RobinsonQ.not_hasFiniteModel

theorem R0_notInterprets_TC : 𝗥₀ ⋫ 𝗧𝗖 :=
  DirectInterpretation.notInterprets_of_not_hasFiniteModel Arithmetic.R0.locallyFinitelySatisfiable
    finiteAxiomatizable_TC not_hasFiniteModel_TC

end FFL.FirstOrder.Concatenation

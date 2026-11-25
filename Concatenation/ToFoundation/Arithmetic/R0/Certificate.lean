module

public import Concatenation.ToFoundation.Arithmetic.R0.Cut
public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# Certificates of finite models

A certificate codes a finite model together with its satisfaction relation for finitely many
formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure

variable {M : Type*} [ORingStructure M] {c j k x y z p : M}

/-- $p = \langle k, x \rangle + 1$. -/
def IsNode (p k x : M) : Prop := ∃ q, q < p ∧ M ⊧/![q, k, x] pairDef.val ∧ p = q + 1

/-- $p = \langle k, x \rangle + 1$. -/
def isNode : ArithmeticSemisentence 3 := “p k x. ∃ q < p, !pairDef q k x ∧ p = q + 1”

@[simp]
lemma eval_isNode : M ⊧/![p, k, x] isNode ↔ IsNode p k x := by
  simp [isNode, IsNode]

/-- The fact of tag `k` about `x`, `y` and `z` belongs to `c`. -/
@[mk_iff]
structure Fact (c k x y z : M) : Prop where
  lt₁ : x < c
  lt₂ : y < c
  lt₃ : z < c
  mem : M ⊧/![mkPair k (mkPair x (mkPair y z)), c] bitDef.val

/-- The fact of tag `k` about `x`, `y` and `z` belongs to `c`. -/
def fact : ArithmeticSemisentence 5 := “c k x y z. x < c ∧ y < c ∧ z < c ∧
  !bitDef (!mkPairTerm k (!mkPairTerm x (!mkPairTerm y z))) c”

@[simp]
lemma eval_fact : M ⊧/![c, k, x, y, z] fact ↔ Fact c k x y z := by
  simp [fact, fact_iff]

@[simp]
lemma eval_val_comp_fact {n : ℕ} {e : Fin n → M} {t₁ t₂ t₃ t₄ t₅ : ClosedSemiterm ℒₒᵣ n} :
    Semiformula.Eval (Semiterm.val e Empty.elim ∘ ![t₁, t₂, t₃, t₄, t₅]) Empty.elim fact ↔
      Fact (t₁.val e Empty.elim) (t₂.val e Empty.elim) (t₃.val e Empty.elim)
        (t₄.val e Empty.elim) (t₅.val e Empty.elim) := by
  rw [← eval_fact]
  exact iff_of_eq <| congrArg (Semiformula.Eval · Empty.elim fact) <| funext fun i ↦
    match i with | 0 | 1 | 2 | 3 | 4 => rfl

/--
The clauses of a certificate `c` of level `j` on the domain (tag 2), the environments (tag 3) and
the functions (tag 8), the equality (tag 7) and the axioms `A` (tag 4).
-/
@[mk_iff]
structure IsCertificate₁ (A : ArithmeticSemisentence 2) (E : ℕ) (c j : M) : Prop where
  dom_zero : Fact c (numeral 2) 0 0 0
  env_zero : Fact c (numeral 3) 0 0 0
  env_succ : ∀ n < c, ∀ s < c, ∀ a < c, n ⊴ j → Fact c (numeral 3) n s 0 →
    Fact c (numeral 2) a 0 0 → Fact c (numeral 3) (n + 1) (mkPair a s) 0
  fn_total : ∀ k < c, ∀ f < c, ∀ d < c, k ⊴ j → f ⊴ j → Fact c (numeral 3) k d 0 →
    ∃ a < c, a ⊴ mkPair (mkPair 1 (mkPair k f)) d ∧ Fact c (numeral 2) a 0 0 ∧
      Fact c (numeral 8) (mkPair k f) d a
  fn_unique : ∀ x < c, ∀ d < c, ∀ a < c, ∀ b < c, Fact c (numeral 8) x d a →
    Fact c (numeral 8) x d b → a = b
  eq_iff : ∀ a < c, ∀ b < c, Fact c (numeral 2) a 0 0 → Fact c (numeral 2) b 0 0 →
    (Fact c (numeral 7) (mkPair (numeral 2) (numeral E)) (mkPair a (mkPair b 0)) 0 ↔ a = b)
  ax : ∀ p < c, ∀ w < c, p ⊴ j → w ⊴ j → M ⊧/![p, w] A → Fact c (numeral 4) p 0 0

/--
The clauses of a certificate `c` of level `j` on the domain (tag 2), the environments (tag 3) and
the functions (tag 8), the equality (tag 7) and the axioms `A` (tag 4).
-/
def isCertificate₁ (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 := “c j.
  !fact c 2 0 0 0 ∧ !fact c 3 0 0 0 ∧
  (∀ n < c, ∀ s < c, ∀ a < c, !cobhamLE n j → !fact c 3 n s 0 → !fact c 2 a 0 0 →
    !fact c 3 (n + 1) (!mkPairTerm a s) 0) ∧
  (∀ k < c, ∀ f < c, ∀ d < c, !cobhamLE k j → !cobhamLE f j → !fact c 3 k d 0 →
    ∃ a < c, !cobhamLE a (!mkPairTerm (!mkPairTerm 1 (!mkPairTerm k f)) d) ∧ !fact c 2 a 0 0 ∧
      !fact c 8 (!mkPairTerm k f) d a) ∧
  (∀ x < c, ∀ d < c, ∀ a < c, ∀ b < c, !fact c 8 x d a → !fact c 8 x d b → a = b) ∧
  (∀ a < c, ∀ b < c, !fact c 2 a 0 0 → !fact c 2 b 0 0 →
    (!fact c 7 (!mkPairTerm 2 ↑E) (!mkPairTerm a (!mkPairTerm b 0)) 0 ↔ a = b)) ∧
  ∀ p < c, ∀ w < c, !cobhamLE p j → !cobhamLE w j → !A p w → !fact c 4 p 0 0”

variable {A : ArithmeticSemisentence 2} {E : ℕ}

@[simp]
lemma eval_isCertificate₁ : M ⊧/![c, j] (isCertificate₁ A E) ↔ IsCertificate₁ A E c j := by
  simp [isCertificate₁, isCertificate₁_iff]

lemma hierarchy_isCertificate₁ (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 (isCertificate₁ A E) := by
  have hA' : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 0 A := hA.of_zero
  simp [isCertificate₁, hA', fact, cobhamLE, isRegular]

/-- The clauses of a certificate `c` of level `j` on the values of terms (tags 5 and 6). -/
@[mk_iff]
structure IsCertificate₂ (c j : M) : Prop where
  bvar_zero : ∀ t < c, ∀ n < c, ∀ s < c, ∀ a < c, IsNode t 0 0 → t ⊴ j →
    Fact c (numeral 3) n s 0 → Fact c (numeral 2) a 0 0 →
    Fact c (numeral 3) (n + 1) (mkPair a s) 0 → Fact c (numeral 5) t (mkPair a s) a
  bvar_succ : ∀ t < c, ∀ u < c, ∀ i < c, ∀ n < c, ∀ s < c, ∀ a < c, ∀ b < c, IsNode t 0 i →
    IsNode u 0 (i + 1) → u ⊴ j → Fact c (numeral 3) (n + 1) (mkPair b s) 0 →
    Fact c (numeral 2) b 0 0 → Fact c (numeral 5) t s a → Fact c (numeral 5) u (mkPair b s) a
  func : ∀ t < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ f < c, ∀ v < c, ∀ s < c, ∀ d < c, ∀ a < c,
    IsNode t (numeral 2) x → M ⊧/![x, k, y] pairDef.val → M ⊧/![y, f, v] pairDef.val → t ⊴ j →
    Fact c (numeral 6) v s d → Fact c (numeral 8) (mkPair k f) d a → Fact c (numeral 5) t s a
  vec_nil : ∀ n < c, ∀ s < c, Fact c (numeral 3) n s 0 → Fact c (numeral 6) 0 s 0
  vec_cons : ∀ w < c, ∀ t < c, ∀ v < c, ∀ s < c, ∀ a < c, ∀ d < c, IsNode w t v → w ⊴ j →
    Fact c (numeral 5) t s a → Fact c (numeral 6) v s d → Fact c (numeral 6) w s (mkPair a d)

/-- The clauses of a certificate `c` of level `j` on the values of terms (tags 5 and 6). -/
def isCertificate₂ : ArithmeticSemisentence 2 := “c j.
  (∀ t < c, ∀ n < c, ∀ s < c, ∀ a < c, !isNode t 0 0 → !cobhamLE t j → !fact c 3 n s 0 →
    !fact c 2 a 0 0 → !fact c 3 (n + 1) (!mkPairTerm a s) 0 → !fact c 5 t (!mkPairTerm a s) a) ∧
  (∀ t < c, ∀ u < c, ∀ i < c, ∀ n < c, ∀ s < c, ∀ a < c, ∀ b < c, !isNode t 0 i →
    !isNode u 0 (i + 1) → !cobhamLE u j → !fact c 3 (n + 1) (!mkPairTerm b s) 0 →
    !fact c 2 b 0 0 → !fact c 5 t s a → !fact c 5 u (!mkPairTerm b s) a) ∧
  (∀ t < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ f < c, ∀ v < c, ∀ s < c, ∀ d < c, ∀ a < c,
    !isNode t 2 x → !pairDef x k y → !pairDef y f v → !cobhamLE t j → !fact c 6 v s d →
    !fact c 8 (!mkPairTerm k f) d a → !fact c 5 t s a) ∧
  (∀ n < c, ∀ s < c, !fact c 3 n s 0 → !fact c 6 0 s 0) ∧
  ∀ w < c, ∀ t < c, ∀ v < c, ∀ s < c, ∀ a < c, ∀ d < c, !isNode w t v → !cobhamLE w j →
    !fact c 5 t s a → !fact c 6 v s d → !fact c 6 w s (!mkPairTerm a d)”

@[simp]
lemma eval_isCertificate₂ : M ⊧/![c, j] isCertificate₂ ↔ IsCertificate₂ c j := by
  simp [isCertificate₂, isCertificate₂_iff]

lemma hierarchy_isCertificate₂ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 isCertificate₂ := by
  simp [isCertificate₂, isNode, fact, cobhamLE, isRegular]

/-- The clauses of a certificate `c` on satisfaction (tag 4). -/
@[mk_iff]
structure IsCertificate₃ (c : M) : Prop where
  and : ∀ p < c, ∀ x < c, ∀ q < c, ∀ r < c, ∀ s < c, IsNode p (numeral 4) x →
    M ⊧/![x, q, r] pairDef.val → Fact c (numeral 4) p s 0 →
    Fact c (numeral 4) q s 0 ∧ Fact c (numeral 4) r s 0
  or : ∀ p < c, ∀ x < c, ∀ q < c, ∀ r < c, ∀ s < c, IsNode p (numeral 5) x →
    M ⊧/![x, q, r] pairDef.val → Fact c (numeral 4) p s 0 →
    Fact c (numeral 4) q s 0 ∨ Fact c (numeral 4) r s 0
  all : ∀ p < c, ∀ q < c, ∀ s < c, ∀ a < c, IsNode p (numeral 6) q → Fact c (numeral 4) p s 0 →
    Fact c (numeral 2) a 0 0 → Fact c (numeral 4) q (mkPair a s) 0
  exs : ∀ p < c, ∀ q < c, ∀ s < c, IsNode p (numeral 7) q → Fact c (numeral 4) p s 0 →
    ∃ a < c, a ⊴ mkPair (mkPair 0 q) s ∧ Fact c (numeral 2) a 0 0 ∧
      Fact c (numeral 4) q (mkPair a s) 0
  falsum : ∀ p < c, ∀ s < c, IsNode p (numeral 3) 0 → ¬Fact c (numeral 4) p s 0
  rel : ∀ p < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ R < c, ∀ v < c, ∀ s < c, ∀ d < c,
    IsNode p 0 x → M ⊧/![x, k, y] pairDef.val → M ⊧/![y, R, v] pairDef.val →
    Fact c (numeral 4) p s 0 → Fact c (numeral 6) v s d → Fact c (numeral 7) (mkPair k R) d 0
  nrel : ∀ p < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ R < c, ∀ v < c, ∀ s < c, ∀ d < c,
    IsNode p 1 x → M ⊧/![x, k, y] pairDef.val → M ⊧/![y, R, v] pairDef.val →
    Fact c (numeral 4) p s 0 → Fact c (numeral 6) v s d → ¬Fact c (numeral 7) (mkPair k R) d 0

/-- The clauses of a certificate `c` on satisfaction (tag 4). -/
def isCertificate₃ : ArithmeticSemisentence 1 := “c.
  (∀ p < c, ∀ x < c, ∀ q < c, ∀ r < c, ∀ s < c, !isNode p 4 x → !pairDef x q r →
    !fact c 4 p s 0 → !fact c 4 q s 0 ∧ !fact c 4 r s 0) ∧
  (∀ p < c, ∀ x < c, ∀ q < c, ∀ r < c, ∀ s < c, !isNode p 5 x → !pairDef x q r →
    !fact c 4 p s 0 → !fact c 4 q s 0 ∨ !fact c 4 r s 0) ∧
  (∀ p < c, ∀ q < c, ∀ s < c, ∀ a < c, !isNode p 6 q → !fact c 4 p s 0 → !fact c 2 a 0 0 →
    !fact c 4 q (!mkPairTerm a s) 0) ∧
  (∀ p < c, ∀ q < c, ∀ s < c, !isNode p 7 q → !fact c 4 p s 0 →
    ∃ a < c, !cobhamLE a (!mkPairTerm (!mkPairTerm 0 q) s) ∧ !fact c 2 a 0 0 ∧
      !fact c 4 q (!mkPairTerm a s) 0) ∧
  (∀ p < c, ∀ s < c, !isNode p 3 0 → ¬!fact c 4 p s 0) ∧
  (∀ p < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ R < c, ∀ v < c, ∀ s < c, ∀ d < c,
    !isNode p 0 x → !pairDef x k y → !pairDef y R v → !fact c 4 p s 0 → !fact c 6 v s d →
    !fact c 7 (!mkPairTerm k R) d 0) ∧
  ∀ p < c, ∀ x < c, ∀ k < c, ∀ y < c, ∀ R < c, ∀ v < c, ∀ s < c, ∀ d < c,
    !isNode p 1 x → !pairDef x k y → !pairDef y R v → !fact c 4 p s 0 → !fact c 6 v s d →
    ¬!fact c 7 (!mkPairTerm k R) d 0”

@[simp]
lemma eval_isCertificate₃ : M ⊧/![c] isCertificate₃ ↔ IsCertificate₃ c := by
  simp [isCertificate₃, isCertificate₃_iff]

lemma hierarchy_isCertificate₃ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 isCertificate₃ := by
  simp [isCertificate₃, isNode, fact, cobhamLE, isRegular]

/--
`c` is a certificate of level `j`: it codes a finite model of the sentences `p` with
$A(p, w)$ for some `w`, `p` and `w` being at most `j`, where `E` is the code of the equality
symbol.
-/
@[mk_iff]
structure IsCertificate (A : ArithmeticSemisentence 2) (E : ℕ) (c j : M) : Prop extends
  IsCertificate₁ A E c j, IsCertificate₂ c j, IsCertificate₃ c

/--
`c` is a certificate of level `j`: it codes a finite model of the sentences `p` with
$A(p, w)$ for some `w`, `p` and `w` being at most `j`, where `E` is the code of the equality
symbol.
-/
def isCertificate (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 :=
  “c j. !(isCertificate₁ A E) c j ∧ !isCertificate₂ c j ∧ !isCertificate₃ c”

@[simp]
lemma eval_isCertificate : M ⊧/![c, j] (isCertificate A E) ↔ IsCertificate A E c j := by
  simp [isCertificate, isCertificate_iff]

lemma hierarchy_isCertificate (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 (isCertificate A E) := by
  simp [isCertificate, hierarchy_isCertificate₁ hA, hierarchy_isCertificate₂,
    hierarchy_isCertificate₃]

section nat

@[simp]
lemma nat_cobhamLE_iff {m n : ℕ} : m ⊴ n ↔ m ≤ n := by
  simpa using numeral_cobhamLE_numeral_iff (M := ℕ) (k := m) (n := n)

@[simp]
lemma nat_eval_pairDef {q m n : ℕ} : ℕ ⊧/![q, m, n] pairDef.val ↔ q = Nat.pair m n := by
  simpa using eval_pairDef_numeral_iff (M := ℕ) (p := q) m n

@[simp]
lemma nat_isNode_iff {p k x : ℕ} : IsNode p k x ↔ p = Nat.pair k x + 1 := by
  constructor
  · rintro ⟨q, -, hq, rfl⟩
    rw [nat_eval_pairDef.mp hq]
  · rintro rfl
    exact ⟨Nat.pair k x, Nat.lt_succ_self _, nat_eval_pairDef.mpr rfl, rfl⟩

lemma nat_fact_iff {c k x y z : ℕ} :
    Fact c k x y z ↔ x < c ∧ y < c ∧ z < c ∧ mkPair k (mkPair x (mkPair y z)) ∈ c := by
  simp [fact_iff]

lemma exists_forall_mem_iff {s : Set ℕ} (hs : s.Finite) : ∃ c : ℕ, ∀ e : ℕ, e ∈ c ↔ e ∈ s := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨insert a c, fun e ↦ by simp [hc]⟩

end nat

section envCode

/-- The code of the environment `v`. -/
def envCode : {n : ℕ} → (Fin n → M) → M
  | 0, _ => 0
  | _ + 1, v => mkPair (v 0) (envCode fun i ↦ v i.succ)

@[simp]
lemma envCode_zero {v : Fin 0 → M} : envCode v = 0 := rfl

@[simp]
lemma envCode_cons {n : ℕ} {a : M} {v : Fin n → M} :
    envCode (a :> v) = mkPair a (envCode v) := by
  simp [envCode]

lemma lt_envCode {n : ℕ} {v : Fin n → ℕ} (i : Fin n) : v i < envCode v := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact left_lt_mkPair _ _
    | succ i => exact (ih (v := fun i ↦ v i.succ) i).trans <| right_lt_mkPair _ _

lemma eq_of_envCode_eq {n m : ℕ} {v : Fin n → ℕ} {w : Fin m → ℕ} (h : envCode v = envCode w) :
    n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => exact absurd h (mkPair_pos _ _).ne
  | succ n ih =>
    cases m with
    | zero => exact absurd h (mkPair_pos _ _).ne'
    | succ m => exact congrArg _ <| ih (mkPair_inj.mp h).2

lemma envCode_injective {n : ℕ} : Function.Injective (envCode : (Fin n → ℕ) → ℕ) := by
  induction n with
  | zero => exact fun _ _ _ ↦ Subsingleton.elim _ _
  | succ n ih =>
    intro v w h
    obtain ⟨h₀, h₁⟩ := mkPair_inj.mp h
    funext i
    cases i using Fin.cases with
    | zero => exact h₀
    | succ i => exact congrFun (ih h₁) i

@[simp]
lemma envCode_inj {n : ℕ} {v w : Fin n → ℕ} : envCode v = envCode w ↔ v = w :=
  envCode_injective.eq_iff

end envCode

end FFL.FirstOrder.Arithmetic.R0

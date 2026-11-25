module

public import Concatenation.ToFoundation.Arithmetic.R0.Cut
public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Arithmetic.Exponential.Bit

/-!
# Certificates of finite models

A certificate codes a finite model, whose elements are named by the numbers, together with its
satisfaction relation for finitely many formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure Encodable

section certificate

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
  lt : j < c
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
  j < c ∧ !fact c 2 0 0 0 ∧ !fact c 3 0 0 0 ∧
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

end certificate

section naming

/-- The name of the witness of the existential formula with the kernel of code `p`. -/
def witnessName (p s : ℕ) : ℕ := mkPair (mkPair 0 p) s

/-- The name of the value of the function symbol of code `f` and arity `k`. -/
def funcName (k f d : ℕ) : ℕ := mkPair (mkPair 1 (mkPair k f)) d

variable {L : Language} [L.Encodable] {S : Type*} [Nonempty S] [Tarski.Structure L S]

/--
`val` names the elements of `S` by the numbers: it maps the names of witnesses to witnesses and
the names of values to values.
-/
structure IsNaming (L : Language) [L.Encodable] {S : Type*} [Nonempty S] [Tarski.Structure L S]
    (val : ℕ → S) : Prop where
  witness : ∀ {n} (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
    (∃ a, S ⊧/(a :> val ∘ v) φ) → S ⊧/(val (witnessName (encode φ) (envCode v)) :> val ∘ v) φ
  func : ∀ {k} (f : L.Func k) (v : Fin k → ℕ),
    val (funcName k (encode f) (envCode v)) = Tarski.Structure.func f (val ∘ v)

lemma exists_strongRec (g : ℕ → (ℕ → S) → S) :
    ∃ val : ℕ → S, ∀ e, ∃ u : ℕ → S, (∀ i < e, u i = val i) ∧ val e = g e u := by
  classical
  have a : S := Classical.arbitrary S
  let val : ℕ → S := Nat.lt_wfRel.wf.fix fun e ih ↦ g e fun i ↦ if h : i < e then ih i h else a
  use val
  intro e
  use fun i ↦ if i < e then val i else a
  constructor
  · intro i hi
    simp [hi]
  · exact Nat.lt_wfRel.wf.fix_eq _ e

variable (L S) in
lemma exists_isNaming : ∃ val : ℕ → S, IsNaming L val := by
  have (e : ℕ) (u : ℕ → S) : ∃ b : S,
      (∀ n (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
        e = witnessName (encode φ) (envCode v) → (∃ a, S ⊧/(a :> u ∘ v) φ) →
          S ⊧/(b :> u ∘ v) φ) ∧
      ∀ k (f : L.Func k) (v : Fin k → ℕ), e = funcName k (encode f) (envCode v) →
        b = Tarski.Structure.func f (u ∘ v) := by
    by_cases h₁ : ∃ n, ∃ (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
        e = witnessName (encode φ) (envCode v)
    · obtain ⟨n, φ, v, rfl⟩ := h₁
      have h (b : S) (hb : (∃ a, S ⊧/(a :> u ∘ v) φ) → S ⊧/(b :> u ∘ v) φ) : ∃ b : S,
          (∀ n' (φ' : Semisentence L (n' + 1)) (v' : Fin n' → ℕ),
            witnessName (encode φ) (envCode v) = witnessName (encode φ') (envCode v') →
              (∃ a, S ⊧/(a :> u ∘ v') φ') → S ⊧/(b :> u ∘ v') φ') ∧
          ∀ k (f : L.Func k) (v' : Fin k → ℕ),
            witnessName (encode φ) (envCode v) = funcName k (encode f) (envCode v') →
            b = Tarski.Structure.func f (u ∘ v') := by
        use b
        constructor
        · intro n' φ' v' h
          simp only [witnessName, mkPair_inj, true_and] at h
          obtain ⟨hφ, hv⟩ := h
          obtain rfl := eq_of_envCode_eq hv
          obtain rfl := encode_injective hφ
          obtain rfl := envCode_injective hv
          exact hb
        · intro k f v' h
          simp [witnessName, funcName, mkPair_inj] at h
      by_cases hb : ∃ a, S ⊧/(a :> u ∘ v) φ
      · obtain ⟨b, hb⟩ := hb
        exact h b fun _ ↦ hb
      · exact h (Classical.arbitrary S) fun h ↦ absurd h hb
    · by_cases h₂ : ∃ k, ∃ (f : L.Func k) (v : Fin k → ℕ), e = funcName k (encode f) (envCode v)
      · obtain ⟨k, f, v, rfl⟩ := h₂
        use Tarski.Structure.func f (u ∘ v)
        constructor
        · exact fun n φ v h ↦ absurd ⟨n, φ, v, h⟩ h₁
        · intro k' f' v' h
          simp only [funcName, mkPair_inj, true_and] at h
          obtain ⟨⟨rfl, hf⟩, hv⟩ := h
          obtain rfl := encode_injective hf
          obtain rfl := envCode_injective hv
          rfl
      · use Classical.arbitrary S
        exact ⟨fun n φ v h ↦ absurd ⟨n, φ, v, h⟩ h₁, fun k f v h ↦ absurd ⟨k, f, v, h⟩ h₂⟩
  choose g hg₁ hg₂ using this
  obtain ⟨val, hval⟩ := exists_strongRec g
  have comp {n e : ℕ} {u : ℕ → S} (hu : ∀ i < e, u i = val i) (v : Fin n → ℕ)
      (h : envCode v < e) : u ∘ v = val ∘ v :=
    funext fun i ↦ hu (v i) <| (lt_envCode i).trans h
  use val
  constructor
  · intro n φ v h
    obtain ⟨u, hu, he⟩ := hval <| witnessName (encode φ) (envCode v)
    have := comp hu v <| right_lt_mkPair _ _
    rw [he, ← this]
    exact hg₁ _ u n φ v rfl <| this ▸ h
  · intro k f v
    obtain ⟨u, hu, he⟩ := hval <| funcName k (encode f) (envCode v)
    have := comp hu v <| right_lt_mkPair _ _
    rw [he, ← this]
    exact hg₂ _ u k f v rfl

/-- `a` is the least name of an element. -/
def IsCanonical (val : ℕ → S) (a : ℕ) : Prop := ∀ b < a, val b ≠ val a

/-- `s` codes an environment of `n` least names. -/
def IsEnv (val : ℕ → S) (n s : ℕ) : Prop :=
  ∃ v : Fin n → ℕ, (∀ i, IsCanonical val (v i)) ∧ s = envCode v

variable {val : ℕ → S} {a b n s : ℕ}

omit [Nonempty S] in
lemma IsCanonical.zero : IsCanonical val 0 := by
  simp [IsCanonical]

omit [Nonempty S] in
lemma IsCanonical.eq (ha : IsCanonical val a) (hb : IsCanonical val b) (h : val a = val b) :
    a = b := by
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h <| hb a h'
  · exact h'
  · exact absurd h.symm <| ha b h'

omit [Nonempty S] in
variable (val) in
lemma exists_isCanonical (a : ℕ) : ∃ b ≤ a, IsCanonical val b ∧ val b = val a := by
  classical
  have h : ∃ b, val b = val a := ⟨a, rfl⟩
  exact ⟨Nat.find h, Nat.find_min' h rfl,
    fun b hb H ↦ Nat.find_min h hb (H.trans <| Nat.find_spec h), Nat.find_spec h⟩

omit [Nonempty S] in
variable (val) in
lemma exists_isCanonical_le [Finite S] : ∃ D, ∀ a, IsCanonical val a → a ≤ D := by
  have : {a | IsCanonical val a}.Finite :=
    Set.Finite.of_finite_image (Set.toFinite (val '' _)) fun a ha b hb ↦ IsCanonical.eq ha hb
  obtain ⟨D, hD⟩ := this.bddAbove
  exact ⟨D, fun a ha ↦ hD ha⟩

omit [Nonempty S] in
lemma IsEnv.cons (ha : IsCanonical val a) (hs : IsEnv val n s) :
    IsEnv val (n + 1) (mkPair a s) := by
  obtain ⟨v, hv, rfl⟩ := hs
  use a :> v
  simpa [Fin.forall_fin_succ] using ⟨ha, hv⟩

omit [Nonempty S] in
variable (val) in
lemma exists_isEnv_le [Finite S] (N : ℕ) : ∃ B, ∀ n ≤ N, ∀ s, IsEnv val n s → s ≤ B := by
  obtain ⟨D, hD⟩ := exists_isCanonical_le val
  have (n : ℕ) : ∃ B, ∀ s, IsEnv val n s → s ≤ B := by
    induction n with
    | zero => exact ⟨0, by rintro _ ⟨v, -, rfl⟩; simp⟩
    | succ n ih =>
      obtain ⟨B, hB⟩ := ih
      use mkPair D B
      rintro _ ⟨v, hv, rfl⟩
      exact mkPair_le_mkPair (hD _ <| hv 0) <| hB _ ⟨_, fun i ↦ hv i.succ, rfl⟩
  choose B hB using this
  induction N with
  | zero => exact ⟨B 0, fun n hn s hs ↦ by obtain rfl := Nat.le_zero.mp hn; exact hB 0 s hs⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    use max C (B (N + 1))
    intro n hn s hs
    rcases Nat.le_succ_iff.mp hn with hn | rfl
    · exact (hC n hn s hs).trans <| le_max_left _ _
    · exact (hB _ s hs).trans <| le_max_right _ _

section inversion

variable {L : Language} [L.Encodable] {n : ℕ} {p q r k f v : ℕ} {φ : Semisentence L n}

lemma exists_eq_and (h : encode φ = Nat.pair 4 (Nat.pair q r) + 1) :
    ∃ φ₁ φ₂, φ = φ₁ ⋏ φ₂ ∧ encode φ₁ = q ∧ encode φ₂ = r := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋎ _ | ∀¹ _ | ∃¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, Semiformula.encode_verum,
      Semiformula.encode_falsum, Semiformula.encode_or, Semiformula.encode_all,
      Semiformula.encode_ex, Nat.pair_eq_pair] at h
  | φ₁ ⋏ φ₂ =>
    simp only [Semiformula.encode_and, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, φ₂, rfl, h.2⟩

lemma exists_eq_or (h : encode φ = Nat.pair 5 (Nat.pair q r) + 1) :
    ∃ φ₁ φ₂, φ = φ₁ ⋎ φ₂ ∧ encode φ₁ = q ∧ encode φ₂ = r := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | ∀¹ _ | ∃¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, Semiformula.encode_verum,
      Semiformula.encode_falsum, Semiformula.encode_and, Semiformula.encode_all,
      Semiformula.encode_ex, Nat.pair_eq_pair] at h
  | φ₁ ⋎ φ₂ =>
    simp only [Semiformula.encode_or, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, φ₂, rfl, h.2⟩

lemma exists_eq_all (h : encode φ = Nat.pair 6 q + 1) : ∃ φ₁, φ = ∀¹ φ₁ ∧ encode φ₁ = q := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∃¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, Semiformula.encode_verum,
      Semiformula.encode_falsum, Semiformula.encode_and, Semiformula.encode_or,
      Semiformula.encode_ex, Nat.pair_eq_pair] at h
  | ∀¹ φ₁ =>
    simp only [Semiformula.encode_all, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, rfl, h.2⟩

lemma exists_eq_exs (h : encode φ = Nat.pair 7 q + 1) : ∃ φ₁, φ = ∃¹ φ₁ ∧ encode φ₁ = q := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, Semiformula.encode_verum,
      Semiformula.encode_falsum, Semiformula.encode_and, Semiformula.encode_or,
      Semiformula.encode_all, Nat.pair_eq_pair] at h
  | ∃¹ φ₁ =>
    simp only [Semiformula.encode_ex, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    exact ⟨φ₁, rfl, h.2⟩

lemma eq_falsum (h : encode φ = Nat.pair 3 0 + 1) : φ = ⊥ := by
  match φ with
  | .rel _ _ | .nrel _ _ | ⊤ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_nrel, Semiformula.encode_verum,
      Semiformula.encode_ex, Semiformula.encode_and, Semiformula.encode_or,
      Semiformula.encode_all, Nat.pair_eq_pair] at h
  | ⊥ => rfl

lemma exists_eq_rel (h : encode φ = Nat.pair 0 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (R : L.Rel k) (t : Fin k → ClosedSemiterm L n), φ = .rel R t ∧ encode R = f ∧
      Matrix.vecToNat (fun i ↦ encode (t i)) = v := by
  match φ with
  | .nrel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ =>
    simp [Semiformula.encode_nrel, Semiformula.encode_verum, Semiformula.encode_falsum,
      Semiformula.encode_ex, Semiformula.encode_and, Semiformula.encode_or,
      Semiformula.encode_all, Nat.pair_eq_pair] at h
  | .rel R t =>
    simp only [Semiformula.encode_rel, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨R, t, rfl, h⟩

lemma exists_eq_nrel (h : encode φ = Nat.pair 1 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (R : L.Rel k) (t : Fin k → ClosedSemiterm L n), φ = .nrel R t ∧ encode R = f ∧
      Matrix.vecToNat (fun i ↦ encode (t i)) = v := by
  match φ with
  | .rel _ _ | ⊤ | ⊥ | _ ⋏ _ | _ ⋎ _ | ∀¹ _ | ∃¹ _ =>
    simp [Semiformula.encode_rel, Semiformula.encode_verum, Semiformula.encode_falsum,
      Semiformula.encode_ex, Semiformula.encode_and, Semiformula.encode_or,
      Semiformula.encode_all, Nat.pair_eq_pair] at h
  | .nrel R t =>
    simp only [Semiformula.encode_nrel, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨R, t, rfl, h⟩

variable {t : ClosedSemiterm L n}

lemma exists_eq_bvar {i : ℕ} (h : encode t = Nat.pair 0 i + 1) : ∃ x : Fin n, t = #x ∧ x = i := by
  match t with
  | #x =>
    simp only [Semiterm.encode_eq_toNat, Semiterm.toNat, Nat.add_right_cancel_iff,
      Nat.pair_eq_pair] at h
    exact ⟨x, rfl, h.2⟩
  | .func _ _ => simp [Semiterm.encode_eq_toNat, Semiterm.toNat, Nat.pair_eq_pair] at h

lemma exists_eq_func (h : encode t = Nat.pair 2 (Nat.pair k (Nat.pair f v)) + 1) :
    ∃ (F : L.Func k) (u : Fin k → ClosedSemiterm L n), t = .func F u ∧ encode F = f ∧
      Matrix.vecToNat (fun i ↦ encode (u i)) = v := by
  match t with
  | #x => simp [Semiterm.encode_eq_toNat, Semiterm.toNat, Nat.pair_eq_pair] at h
  | .func F u =>
    simp only [Semiterm.encode_eq_toNat, Semiterm.toNat, Nat.add_right_cancel_iff,
      Nat.pair_eq_pair] at h
    obtain ⟨-, rfl, h⟩ := h
    exact ⟨F, u, rfl, h⟩

end inversion

section model

/--
The facts of the certificate of level `j` that `val` gives; `B` is the bound on the numbers that
occur in them.
-/
def ModelFact (L : Language) [L.Encodable] {S : Type*} [Nonempty S] [Tarski.Structure L S]
    (val : ℕ → S) (j B : ℕ) : ℕ → ℕ → ℕ → ℕ → Prop
  | 2, x, y, z => IsCanonical val x ∧ y = 0 ∧ z = 0
  | 3, x, y, z => x ≤ j + 3 ∧ IsEnv val x y ∧ z = 0
  | 4, x, y, z => ∃ (n : ℕ) (φ : Semisentence L n) (v : Fin n → ℕ), encode φ + n ≤ j ∧
      x = encode φ ∧ (∀ i, IsCanonical val (v i)) ∧ y = envCode v ∧ S ⊧/(val ∘ v) φ ∧ z = 0
  | 5, x, y, z => x ≤ j ∧ (∃ n ≤ j + 3, IsEnv val n y) ∧ IsCanonical val z ∧
      ∀ (n : ℕ) (t : ClosedSemiterm L n) (v : Fin n → ℕ), x = encode t → y = envCode v →
        val z = t.val (val ∘ v) Empty.elim
  | 6, x, y, z => x ≤ j ∧ (∃ n ≤ j + 3, IsEnv val n y) ∧ (∃ k ≤ x, IsEnv val k z) ∧
      ∀ (n k : ℕ) (t : Fin k → ClosedSemiterm L n) (v : Fin n → ℕ),
        x = Matrix.vecToNat (fun i ↦ encode (t i)) → y = envCode v →
          ∃ u : Fin k → ℕ, z = envCode u ∧ ∀ i, val (u i) = (t i).val (val ∘ v) Empty.elim
  | 7, x, y, z => ∃ (k : ℕ) (R : L.Rel k) (v : Fin k → ℕ), x = mkPair k (encode R) ∧
      y = envCode v ∧ Tarski.Structure.rel R (val ∘ v) ∧ z = 0
  | 8, x, y, z => IsCanonical val z ∧ val z = val (mkPair (mkPair 1 x) y)
  | 9, x, _, _ => x = B
  | _, _, _, _ => False

/--
`c` consists of the facts that `val` gives on the level `j`, and `B` bounds the numbers that occur
in them.
-/
structure IsModelCode (L : Language) [L.Encodable] [L.Eq] {S : Type*} [Nonempty S]
    [Tarski.Structure L S] (val : ℕ → S) (j B c : ℕ) : Prop where
  lt : B < c
  le : j + 4 ≤ B
  eq_le : mkPair 2 (encode (Language.Eq.eq : L.Rel 2)) ≤ B
  canonical_le {a : ℕ} : IsCanonical val a → a ≤ B
  env_le {n s : ℕ} : n ≤ j + 3 → IsEnv val n s → s ≤ B
  mkPair_le {a b : ℕ} : a ≤ j → b ≤ j → mkPair a b ≤ B
  fact {k x y z : ℕ} : Fact c (ORingStructure.numeral k) x y z ↔
    x ≤ B ∧ y ≤ B ∧ z ≤ B ∧ ModelFact L val j B k x y z

variable [L.Eq] {val : ℕ → S} {j B c : ℕ}

lemma exists_isModelCode [Finite S] (val : ℕ → S) (j : ℕ) : ∃ B c, IsModelCode L val j B c := by
  obtain ⟨D, hD⟩ := exists_isCanonical_le val
  obtain ⟨C, hC⟩ := exists_isEnv_le val (j + 3)
  obtain ⟨B, hB⟩ : ∃ B, B = D + C + (j + 4) + mkPair j j +
    mkPair 2 (encode (Language.Eq.eq : L.Rel 2)) := ⟨_, rfl⟩
  use B
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ e : ℕ, e ∈ c ↔ ∃ k x y z, x ≤ B ∧ y ≤ B ∧ z ≤ B ∧
      ModelFact L val j B k x y z ∧ e = mkPair k (mkPair x (mkPair y z)) := by
    apply exists_forall_mem_iff (s := {e | ∃ k x y z, x ≤ B ∧ y ≤ B ∧ z ≤ B ∧
      ModelFact L val j B k x y z ∧ e = mkPair k (mkPair x (mkPair y z))})
    have : (Set.Iic 9 ×ˢ Set.Iic B ×ˢ Set.Iic B ×ˢ Set.Iic B : Set (ℕ × ℕ × ℕ × ℕ)).Finite :=
      (Set.finite_Iic _).prod <| (Set.finite_Iic _).prod <| (Set.finite_Iic _).prod <|
        Set.finite_Iic _
    apply (this.image fun (k, x, y, z) ↦ mkPair k (mkPair x (mkPair y z))).subset
    rintro e ⟨k, x, y, z, hx, hy, hz, h, rfl⟩
    have hk : k ≤ 9 := by
      by_contra hk
      obtain ⟨k, rfl⟩ : ∃ l, k = l + 10 := ⟨k - 10, by omega⟩
      exact h
    exact ⟨(k, x, y, z), ⟨hk, hx, hy, hz⟩, rfl⟩
  have hBc : B < c := by
    apply (left_lt_mkPair B (mkPair 0 0)).trans
    apply (right_lt_mkPair 9 _).trans
    exact lt_of_mem <| (hc _).mpr ⟨9, B, 0, 0, le_rfl, by simp, by simp, rfl, rfl⟩
  use c
  exact {
    lt := hBc
    le := by omega
    eq_le := by omega
    canonical_le {a} h := by have := hD a h; omega
    env_le {n s} hn h := by have := hC n hn s h; omega
    mkPair_le ha hb := by have := mkPair_le_mkPair ha hb; omega
    fact {k x y z} := by
      rw [show (ORingStructure.numeral k : ℕ) = k by simp, nat_fact_iff, hc]
      constructor
      · rintro ⟨-, -, -, _, _, _, _, hx, hy, hz, h, e⟩
        simp only [mkPair_inj] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact ⟨hx, hy, hz, h⟩
      · rintro ⟨hx, hy, hz, h⟩
        exact ⟨by omega, by omega, by omega, _, _, _, _, hx, hy, hz, h, rfl⟩ }

namespace IsModelCode

variable (H : IsModelCode L val j B c)
include H

lemma dom {a : ℕ} (h : IsCanonical val a) : Fact c (ORingStructure.numeral 2) a 0 0 :=
  H.fact.mpr ⟨H.canonical_le h, Nat.zero_le _, Nat.zero_le _, h, rfl, rfl⟩

lemma env {n s : ℕ} (hn : n ≤ j + 3) (h : IsEnv val n s) :
    Fact c (ORingStructure.numeral 3) n s 0 :=
  H.fact.mpr ⟨by have := H.le; omega, H.env_le hn h, Nat.zero_le _, hn, h, rfl⟩

lemma sat {n : ℕ} {φ : Semisentence L n} {v : Fin n → ℕ} (h : encode φ + n ≤ j)
    (hv : ∀ i, IsCanonical val (v i)) (hφ : S ⊧/(val ∘ v) φ) :
    Fact c (ORingStructure.numeral 4) (encode φ) (envCode v) 0 :=
  H.fact.mpr ⟨by have := H.le; omega, H.env_le (n := n) (by omega) ⟨v, hv, rfl⟩, Nat.zero_le _, n,
    φ, v, h, rfl, hv, rfl, hφ, rfl⟩

lemma value {t n s a : ℕ} (ht : t ≤ j) (hn : n ≤ j + 3) (hs : IsEnv val n s)
    (ha : IsCanonical val a) (h : ∀ (n : ℕ) (t' : ClosedSemiterm L n) (v : Fin n → ℕ),
      t = encode t' → s = envCode v → val a = t'.val (val ∘ v) Empty.elim) :
    Fact c (ORingStructure.numeral 5) t s a :=
  H.fact.mpr ⟨by have := H.le; omega, H.env_le hn hs, H.canonical_le ha, ht, ⟨n, hn, hs⟩, ha, h⟩

lemma values {v n s d k : ℕ} (hv : v ≤ j) (hn : n ≤ j + 3) (hs : IsEnv val n s) (hk : k ≤ v)
    (hd : IsEnv val k d) (h : ∀ (n k : ℕ) (t : Fin k → ClosedSemiterm L n) (w : Fin n → ℕ),
      v = Matrix.vecToNat (fun i ↦ encode (t i)) → s = envCode w →
        ∃ u : Fin k → ℕ, d = envCode u ∧ ∀ i, val (u i) = (t i).val (val ∘ w) Empty.elim) :
    Fact c (ORingStructure.numeral 6) v s d :=
  H.fact.mpr ⟨by have := H.le; omega, H.env_le hn hs, H.env_le (by omega) hd, hv, ⟨n, hn, hs⟩,
    ⟨k, hk, hd⟩, h⟩

lemma isCertificate₁ [Tarski.Structure.Eq L S] {A : ArithmeticSemisentence 2}
    (hA : ∀ p ≤ j, ∀ w ≤ j, ℕ ⊧/![p, w] A → ∃ σ : Sentence L, encode σ = p ∧ S↓[L] ⊧ σ) :
    IsCertificate₁ A (encode (Language.Eq.eq : L.Rel 2)) c j := by
  have hjB := H.le
  have hBc := H.lt
  have hnum (n : ℕ) : (ORingStructure.numeral n : ℕ) = n := by simp
  constructor
  · omega
  · exact H.dom .zero
  · exact H.env (n := 0) (by simp) ⟨![], by simp, rfl⟩
  · intro n _ s _ a _ hn hs ha
    have hn := nat_cobhamLE_iff.mp hn
    obtain ⟨-, -, -, -, hs, -⟩ := H.fact.mp hs
    obtain ⟨-, -, -, ha, -⟩ := H.fact.mp ha
    exact H.env (by omega) <| hs.cons ha
  · intro k _ f _ d _ hk hf hd
    obtain ⟨a, ha, hac, hae⟩ := exists_isCanonical val (funcName k f d)
    have hkf := H.mkPair_le (nat_cobhamLE_iff.mp hk) (nat_cobhamLE_iff.mp hf)
    exact ⟨a, (H.canonical_le hac).trans_lt H.lt, nat_cobhamLE_iff.mpr ha, H.dom hac,
      H.fact.mpr ⟨hkf, (H.fact.mp hd).2.1, H.canonical_le hac, hac, hae⟩⟩
  · intro x _ d _ a _ b _ ha hb
    obtain ⟨-, -, -, ha, ha'⟩ := H.fact.mp ha
    obtain ⟨-, -, -, hb, hb'⟩ := H.fact.mp hb
    exact ha.eq hb <| ha'.trans hb'.symm
  · intro a _ b _ ha hb
    obtain ⟨-, -, -, ha, -⟩ := H.fact.mp ha
    obtain ⟨-, -, -, hb, -⟩ := H.fact.mp hb
    have hv : mkPair a (mkPair b 0) = envCode ![a, b] := by simp
    constructor
    · intro h
      obtain ⟨-, -, -, k, R, v, hR, hd, h, -⟩ := H.fact.mp h
      obtain ⟨hk, hR⟩ := mkPair_inj.mp hR
      obtain rfl : 2 = k := (hnum 2).symm.trans hk
      obtain rfl : Language.Eq.eq = R := encode_injective <| (hnum _).symm.trans hR
      obtain rfl : ![a, b] = v := envCode_injective <| hv.symm.trans hd
      exact ha.eq hb <| by simpa using h
    · rintro rfl
      rw [hnum 2, hnum (encode (Language.Eq.eq : L.Rel 2))]
      exact H.fact.mpr ⟨H.eq_le,
        H.env_le (n := 2) (by omega) ⟨![a, a], by simp [Fin.forall_fin_two, ha], hv⟩,
        Nat.zero_le _, 2, Language.Eq.eq, ![a, a], rfl, hv, by simp, rfl⟩
  · intro p _ w _ hp hw h
    obtain ⟨σ, rfl, hσ⟩ := hA p (nat_cobhamLE_iff.mp hp) w (nat_cobhamLE_iff.mp hw) h
    exact H.sat (n := 0) (v := ![]) (nat_cobhamLE_iff.mp hp) (by simp)
      (by simpa [models_iff, Matrix.empty_eq] using hσ)

lemma isCertificate₂ (hval : IsNaming L val) : IsCertificate₂ c j := by
  constructor
  · intro t _ n _ s _ a _ ht htj hs ha has
    obtain ⟨-, -, -, ha, -⟩ := H.fact.mp ha
    obtain ⟨-, -, -, hn, has, -⟩ := H.fact.mp has
    apply H.value (nat_cobhamLE_iff.mp htj) hn has ha
    rintro n' t' v' rfl hv
    obtain ⟨x, rfl, hx⟩ := exists_eq_bvar <| nat_isNode_iff.mp ht
    match n' with
    | 0 => exact x.elim0
    | n' + 1 =>
      obtain rfl : x = 0 := Fin.ext hx
      simp [(mkPair_inj.mp hv).1]
  · intro t _ u _ i _ n _ s _ a _ b _ ht hu huj hbs hb ha
    obtain ⟨-, -, -, hn, hbs, -⟩ := H.fact.mp hbs
    obtain ⟨-, -, -, -, -, hac, ha⟩ := H.fact.mp ha
    apply H.value (nat_cobhamLE_iff.mp huj) hn hbs hac
    rintro n' t' v' rfl hv
    obtain ⟨x, rfl, hx⟩ := exists_eq_bvar <| nat_isNode_iff.mp hu
    match n' with
    | 0 => exact x.elim0
    | n' + 1 =>
      obtain ⟨y, rfl⟩ : ∃ y : Fin n', x = y.succ :=
        ⟨⟨i, by have := x.isLt; omega⟩, Fin.ext hx⟩
      rw [ha n' #y (fun i ↦ v' i.succ) _ (mkPair_inj.mp hv).2]
      · simp
      · rw [nat_isNode_iff.mp ht, Semiterm.encode_eq_toNat, Semiterm.toNat, ← Nat.succ.inj hx]
  · intro t _ x _ k _ y _ f _ v _ s _ d _ a _ ht hx hy htj hd ha
    obtain rfl := nat_eval_pairDef.mp hx
    obtain rfl := nat_eval_pairDef.mp hy
    obtain ⟨-, -, -, -, ⟨n, hn, hs⟩, -, hd⟩ := H.fact.mp hd
    obtain ⟨-, -, -, hac, ha⟩ := H.fact.mp ha
    apply H.value (nat_cobhamLE_iff.mp htj) hn hs hac
    rintro n' t' v' rfl hv
    obtain ⟨F, u, rfl, rfl, hu⟩ := exists_eq_func <| nat_isNode_iff.mp ht
    obtain ⟨w, rfl, hw⟩ := hd n' k u v' hu.symm hv
    rw [ha]
    exact (hval.func F w).trans <| congrArg _ <| funext hw
  · intro n _ s _ hs
    obtain ⟨-, -, -, hn, hs, -⟩ := H.fact.mp hs
    apply H.values (Nat.zero_le _) hn hs le_rfl ⟨![], by simp, rfl⟩
    intro n' k t v h _
    match k with
    | 0 => exact ⟨![], rfl, by simp⟩
    | k + 1 => simp [Matrix.vecToNat, Matrix.foldr] at h
  · intro w _ t _ v _ s _ a _ d _ hw hwj ha hd
    obtain rfl := nat_isNode_iff.mp hw
    have hwj := nat_cobhamLE_iff.mp hwj
    obtain ⟨-, -, -, -, ⟨n, hn, hs⟩, hac, ha⟩ := H.fact.mp ha
    obtain ⟨-, -, -, -, -, ⟨k, hk, hdk⟩, hd⟩ := H.fact.mp hd
    have hk' := hk.trans <| Nat.right_le_pair t v
    apply H.values hwj hn hs (by omega) (hdk.cons hac)
    intro n' k' t' v' h hv
    match k' with
    | 0 => simp at h
    | k' + 1 =>
      have e : (fun i ↦ encode (t' i)) = encode (t' 0) :> fun i ↦ encode (t' i.succ) := by
        funext i
        cases i using Fin.cases <;> simp
      rw [e, Matrix.encode_succ, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      obtain ⟨u, rfl, hu⟩ := hd n' k' (fun i ↦ t' i.succ) v' h.2 hv
      use a :> u
      simp [Fin.forall_fin_succ, hu, ha n' (t' 0) v' h.1 hv]

lemma isCertificate₃ (hval : IsNaming L val) : IsCertificate₃ c := by
  have hjB := H.le
  have le_pair {k q r : ℕ} : q ≤ Nat.pair k (Nat.pair q r) ∧ r ≤ Nat.pair k (Nat.pair q r) :=
    ⟨(Nat.left_le_pair _ _).trans <| Nat.right_le_pair _ _,
      (Nat.right_le_pair _ _).trans <| Nat.right_le_pair _ _⟩
  have comp {n a : ℕ} {v : Fin n → ℕ} : val ∘ (a :> v) = val a :> val ∘ v :=
    funext fun i ↦ by cases i using Fin.cases <;> rfl
  constructor
  · intro p _ x _ q _ r _ s _ hp hx h
    obtain rfl := nat_eval_pairDef.mp hx
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := exists_eq_and hp
    have := le_pair (k := ORingStructure.numeral 4) (q := encode φ₁) (r := encode φ₂)
    have hφ : S ⊧/(val ∘ v) φ₁ ∧ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
    exact ⟨H.sat (by omega) hv hφ.1, H.sat (by omega) hv hφ.2⟩
  · intro p _ x _ q _ r _ s _ hp hx h
    obtain rfl := nat_eval_pairDef.mp hx
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := exists_eq_or hp
    have := le_pair (k := ORingStructure.numeral 5) (q := encode φ₁) (r := encode φ₂)
    have hφ : S ⊧/(val ∘ v) φ₁ ∨ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
    exact hφ.imp (H.sat (by omega) hv) (H.sat (by omega) hv)
  · intro p _ q _ s _ a _ hp h ha
    obtain ⟨-, -, -, ha, -⟩ := H.fact.mp ha
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ, rfl, rfl⟩ := exists_eq_all hp
    have := Nat.right_le_pair (ORingStructure.numeral 6) (encode φ)
    have hφ : ∀ x, S ⊧/(x :> val ∘ v) φ := by simpa using hφ
    rw [← envCode_cons]
    apply H.sat (by omega)
    · simpa [Fin.forall_fin_succ] using ⟨ha, hv⟩
    · simpa [comp] using hφ (val a)
  · intro p _ q _ s _ hp h
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ, rfl, rfl⟩ := exists_eq_exs hp
    have := Nat.right_le_pair (ORingStructure.numeral 7) (encode φ)
    have hφ := hval.witness φ v <| by simpa using hφ
    obtain ⟨a, ha, hac, hae⟩ := exists_isCanonical val (witnessName (encode φ) (envCode v))
    have := H.sat (φ := φ) (v := a :> v) (by omega) (by simpa [Fin.forall_fin_succ] using ⟨hac, hv⟩)
      (by simpa [comp, hae] using hφ)
    exact ⟨a, (H.canonical_le hac).trans_lt H.lt, nat_cobhamLE_iff.mpr ha, H.dom hac,
      by simpa using this⟩
  · intro p _ s _ hp h
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    obtain rfl := eq_falsum <| nat_isNode_iff.mp hp
    simp at hφ
  · intro p _ x _ k _ y _ R _ v _ s _ d _ hp hx hy h hd
    obtain rfl := nat_eval_pairDef.mp hx
    obtain rfl := nat_eval_pairDef.mp hy
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨R, t, rfl, rfl, rfl⟩ := exists_eq_rel hp
    obtain ⟨-, -, hdB, -, -, -, hd⟩ := H.fact.mp hd
    obtain ⟨u, rfl, hu⟩ := hd n k t v rfl rfl
    have le {r w : ℕ} : k ≤ Nat.pair 0 (Nat.pair k (Nat.pair r w)) ∧
        r ≤ Nat.pair 0 (Nat.pair k (Nat.pair r w)) :=
      ⟨le_pair.1, (le_pair.1.trans <| Nat.right_le_pair 0 _)⟩
    have := le (r := encode R) (w := Matrix.vecToNat fun i ↦ encode (t i))
    have hφ : Tarski.Structure.rel R (val ∘ u) := by
      simpa [Semiformula.eval_rel, Function.comp_def, hu] using hφ
    exact H.fact.mpr
      ⟨H.mkPair_le (by omega) (by omega), hdB, Nat.zero_le _, k, R, u, rfl, rfl, hφ, rfl⟩
  · intro p _ x _ k _ y _ R _ v _ s _ d _ hp hx hy h hd h'
    obtain rfl := nat_eval_pairDef.mp hx
    obtain rfl := nat_eval_pairDef.mp hy
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    obtain ⟨R, t, rfl, rfl, rfl⟩ := exists_eq_nrel <| nat_isNode_iff.mp hp
    obtain ⟨-, -, -, -, -, -, hd⟩ := H.fact.mp hd
    obtain ⟨u, rfl, hu⟩ := hd n k t v rfl rfl
    obtain ⟨-, -, -, k', R', u', hR, hu', h', -⟩ := H.fact.mp h'
    obtain ⟨rfl, hR⟩ := mkPair_inj.mp hR
    obtain rfl := encode_injective hR
    obtain rfl := envCode_injective hu'
    have hφ : ¬Tarski.Structure.rel R (val ∘ u) := by
      simpa [Semiformula.eval_nrel, Function.comp_def, hu] using hφ
    exact hφ h'

end IsModelCode

lemma exists_isCertificate [Tarski.Structure.Eq L S] [Finite S] (A : ArithmeticSemisentence 2)
    (j : ℕ) (hA : ∀ p ≤ j, ∀ w ≤ j, ℕ ⊧/![p, w] A → ∃ σ : Sentence L, encode σ = p ∧ S↓[L] ⊧ σ) :
    ∃ c : ℕ, IsCertificate A (encode (Language.Eq.eq : L.Rel 2)) c j := by
  obtain ⟨val, hval⟩ := exists_isNaming L S
  obtain ⟨B, c, H⟩ := exists_isModelCode (L := L) val j
  exact ⟨c, H.isCertificate₁ hA, H.isCertificate₂ hval, H.isCertificate₃ hval⟩

end model

end naming

end FFL.FirstOrder.Arithmetic.R0

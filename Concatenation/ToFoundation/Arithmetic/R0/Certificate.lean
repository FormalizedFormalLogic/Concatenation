module

public import Concatenation.ToFoundation.Arithmetic.R0.Cut
public import Concatenation.ToFoundation.Arithmetic.R0.Representation
public import Concatenation.ToFoundation.Coding
public import Concatenation.ToFoundation.Naming

/-!
# Certificates of finite models

A certificate codes a finite model, whose elements are named by the numbers, together with its
satisfaction relation for finitely many formulas.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0.Visser

open ORingStructure Encodable Tarski.Structure

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

@[simp, grind =]
lemma nat_isNode_iff {p k x : ℕ} : IsNode p k x ↔ p = Nat.pair k x + 1 := by
  constructor
  · rintro ⟨q, -, hq, rfl⟩
    rw [nat_eval_pairDef.mp hq]
  · rintro rfl
    exact ⟨Nat.pair k x, Nat.lt_succ_self _, nat_eval_pairDef.mpr rfl, rfl⟩

lemma nat_fact_iff {c k x y z : ℕ} :
    Fact c k x y z ↔ x < c ∧ y < c ∧ z < c ∧ mkPair k (mkPair x (mkPair y z)) ∈ c := by
  simp [fact_iff]

end nat

end certificate

section model

variable {L : Language} [L.Encodable] {S : Type*} [Nonempty S] [Tarski.Structure L S]

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
    obtain ⟨x, rfl, hx⟩ := Semiterm.exists_eq_bvar_of_encode_eq <| nat_isNode_iff.mp ht
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
    obtain ⟨x, rfl, hx⟩ := Semiterm.exists_eq_bvar_of_encode_eq <| nat_isNode_iff.mp hu
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
    obtain ⟨F, u, rfl, rfl, hu⟩ := Semiterm.exists_eq_func_of_encode_eq <| nat_isNode_iff.mp ht
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
    obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := Semiformula.exists_eq_and_of_encode_eq hp
    have := le_pair (k := ORingStructure.numeral 4) (q := encode φ₁) (r := encode φ₂)
    have hφ : S ⊧/(val ∘ v) φ₁ ∧ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
    exact ⟨H.sat (by omega) hv hφ.1, H.sat (by omega) hv hφ.2⟩
  · intro p _ x _ q _ r _ s _ hp hx h
    obtain rfl := nat_eval_pairDef.mp hx
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := Semiformula.exists_eq_or_of_encode_eq hp
    have := le_pair (k := ORingStructure.numeral 5) (q := encode φ₁) (r := encode φ₂)
    have hφ : S ⊧/(val ∘ v) φ₁ ∨ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
    exact hφ.imp (H.sat (by omega) hv) (H.sat (by omega) hv)
  · intro p _ q _ s _ a _ hp h ha
    obtain ⟨-, -, -, ha, -⟩ := H.fact.mp ha
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ, rfl, rfl⟩ := Semiformula.exists_eq_all_of_encode_eq hp
    have := Nat.right_le_pair (ORingStructure.numeral 6) (encode φ)
    have hφ : ∀ x, S ⊧/(x :> val ∘ v) φ := by simpa using hφ
    rw [← envCode_cons]
    apply H.sat (by omega)
    · simpa [Fin.forall_fin_succ] using ⟨ha, hv⟩
    · simpa [comp] using hφ (val a)
  · intro p _ q _ s _ hp h
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨φ, rfl, rfl⟩ := Semiformula.exists_eq_ex_of_encode_eq hp
    have := Nat.right_le_pair (ORingStructure.numeral 7) (encode φ)
    have hφ := hval.witness φ v <| by simpa using hφ
    obtain ⟨a, ha, hac, hae⟩ := exists_isCanonical val (witnessName (encode φ) (envCode v))
    have := H.sat (φ := φ) (v := a :> v) (by omega) (by simpa [Fin.forall_fin_succ] using ⟨hac, hv⟩)
      (by simpa [comp, hae] using hφ)
    exact ⟨a, (H.canonical_le hac).trans_lt H.lt, nat_cobhamLE_iff.mpr ha, H.dom hac,
      by simpa using this⟩
  · intro p _ s _ hp h
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    obtain rfl := Semiformula.eq_falsum_of_encode_eq <| nat_isNode_iff.mp hp
    simp at hφ
  · intro p _ x _ k _ y _ R _ v _ s _ d _ hp hx hy h hd
    obtain rfl := nat_eval_pairDef.mp hx
    obtain rfl := nat_eval_pairDef.mp hy
    obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := H.fact.mp h
    have hp := nat_isNode_iff.mp hp
    obtain ⟨R, t, rfl, rfl, rfl⟩ := Semiformula.exists_eq_rel_of_encode_eq hp
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
    obtain ⟨R, t, rfl, rfl, rfl⟩ :=
      Semiformula.exists_eq_nrel_of_encode_eq <| nat_isNode_iff.mp hp
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

end FFL.FirstOrder.Arithmetic.R0.Visser

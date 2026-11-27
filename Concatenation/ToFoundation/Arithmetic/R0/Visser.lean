module

public import Concatenation.ToFoundation.Arithmetic.R0.LocallyFinitelySatisfiable
public import Concatenation.ToFoundation.Arithmetic.R0.Certificate
public import Foundation.FirstOrder.Incompleteness.Church

/-!
# Interpretability in $\mathsf{R}_0$

A recursively enumerable theory of a finite language is interpretable in $\mathsf{R}_0$ if and only
if it is locally finitely satisfiable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure Encodable DirectTranslation

variable {V : Type*} [ORingStructure V] {A : ArithmeticSemisentence 2} {E : ℕ}
  {c j k x y z : V}

namespace Visser

section stage

/-- `c` is the least certificate of level `j`. -/
@[mk_iff]
structure IsStage (A : ArithmeticSemisentence 2) (E : ℕ) (j c : V) : Prop where
  isCertificate : IsCertificate A E c j
  eq_of_le : ∀ d, d ⊴ c → IsCertificate A E d j → d = c

/-- `c` is the least certificate of level `j`. -/
def isStageDef (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 := “j c.
  !(isCertificateDef A E) c j ∧ ∀ d, !cobhamLEDef d c → !(isCertificateDef A E) d j → d = c”

instance isStage_defined : ℒₒᵣ-relation[V] (IsStage A E) via isStageDef A E :=
  ⟨fun v ↦ by simp [isStageDef, isStage_iff]⟩

instance isStage_definable : ℒₒᵣ-relation[V] (IsStage A E) := isStage_defined.to_definable

/-- `j` has a unique least certificate, which bounds the elements up to `j`. -/
@[mk_iff]
structure HasStage (A : ArithmeticSemisentence 2) (E : ℕ) (j : V) : Prop where
  exists_isStage : ∃ c, IsStage A E j c
  unique : ∀ c, IsStage A E j c → ∀ d, IsStage A E j d → c = d
  lt : ∀ c, IsStage A E j c → ∀ x, x ⊴ j → x < c

/-- `j` has a unique least certificate, which bounds the elements up to `j`. -/
def hasStageDef (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 1 := “j.
  (∃ c, !(isStageDef A E) j c) ∧ (∀ c, !(isStageDef A E) j c → ∀ d, !(isStageDef A E) j d → c = d) ∧
  ∀ c, !(isStageDef A E) j c → ∀ x, !cobhamLEDef x j → x < c”

instance hasStage_defined : ℒₒᵣ-predicate[V] (HasStage A E) via hasStageDef A E :=
  ⟨fun v ↦ by simp [hasStageDef, hasStage_iff]⟩

instance hasStage_definable : ℒₒᵣ-predicate[V] (HasStage A E) := hasStage_defined.to_definable

/-- `x` belongs to the least certificate of level `j`. -/
def MemStage (A : ArithmeticSemisentence 2) (E : ℕ) (x j : V) : Prop :=
  ∃ c, IsStage A E j c ∧ V ⊧/![x, c] bitDef.val

/-- `x` belongs to the least certificate of level `j`. -/
def memStageDef (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 :=
  “x j. ∃ c, !(isStageDef A E) j c ∧ !bitDef x c”

instance memStage_defined : ℒₒᵣ-relation[V] (MemStage A E) via memStageDef A E :=
  ⟨fun v ↦ by simp [memStageDef, MemStage]⟩

instance memStage_definable : ℒₒᵣ-relation[V] (MemStage A E) := memStage_defined.to_definable

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀] (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)

include hA in
lemma isCertificate_numeral_iff (i j : ℕ) :
    IsCertificate A E (numeral i : V) (numeral j) ↔ IsCertificate A E i j := by
  simpa using eval_numeral_iff_of_deltaZero₂ (V := V) (hierarchy_isCertificate (E := E) hA) i j

include hA in
lemma hasStage_numeral {j : ℕ} (h : ∃ c : ℕ, IsCertificate A E c j) :
    HasStage A E (numeral j : V) := by
  classical
  have cert : IsCertificate A E (numeral (Nat.find h) : V) (numeral j) :=
    (isCertificate_numeral_iff hA _ _).mpr <| Nat.find_spec h
  have stage : IsStage A E (numeral j : V) (numeral (Nat.find h)) := ⟨cert, fun d hd hdj ↦ by
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral hd
    have := Nat.find_min' h <| (isCertificate_numeral_iff hA _ _).mp hdj
    rw [le_antisymm hi this]⟩
  have eq (c : V) (hc : IsStage A E (numeral j : V) c) : c = numeral (Nat.find h) := by
    rcases cobhamLE_numeral_or (x := c) (Nat.find h) with h' | h'
    · exact stage.eq_of_le c h' hc.isCertificate
    · exact (hc.eq_of_le _ h' cert).symm
  constructor
  · exact ⟨_, stage⟩
  · grind
  · intro c hc x hx
    rw [eq c hc]
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral hx
    simpa using hi.trans_lt (Nat.find_spec h).lt

end stage

section holds

variable {φ : ArithmeticSemisentence 1} {ψ σ : ArithmeticSemisentence 2}

/--
The fact of tag `k` about `x`, `y` and `z` belongs to the set that `σ` assigns to the greatest good
element or, if there is none, to the limit of the sets defined by `ψ`.
-/
def Holds (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) (k x y z : V) : Prop :=
  (∃ m, IsGreatestGood φ ψ m ∧ ∃ c, V ⊧/![m, c] σ ∧ Fact c k x y z) ∨
  (¬∃ m : V, IsGreatestGood φ ψ m) ∧ MemLimit φ ψ (mkPair k (mkPair x (mkPair y z)))

/--
The fact of tag `k` about `x`, `y` and `z` belongs to the set that `σ` assigns to the greatest good
element or, if there is none, to the limit of the sets defined by `ψ`.
-/
def holdsDef (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 4 := “k x y z.
  (∃ m, !(isGreatestGoodDef φ ψ) m ∧ ∃ c, !σ m c ∧ !factDef c k x y z) ∨
  (¬∃ m, !(isGreatestGoodDef φ ψ) m) ∧
    !(memLimitDef φ ψ) (!mkPairTerm k (!mkPairTerm x (!mkPairTerm y z)))”

instance holds_defined : ℒₒᵣ-relation₄[V] (Holds φ ψ σ) via holdsDef φ ψ σ :=
  ⟨fun v ↦ by simp [holdsDef, Holds]⟩

instance holds_definable : ℒₒᵣ-relation₄[V] (Holds φ ψ σ) := holds_defined.to_definable

/-- There is a greatest good element, or `x` belongs to the shortened cut. -/
def IsSmall (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (x : V) : Prop :=
  (∃ m : V, IsGreatestGood φ ψ m) ∨ IsMulCut φ ψ x

/-- There is a greatest good element, or `x` belongs to the shortened cut. -/
def isSmallDef (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. (∃ m, !(isGreatestGoodDef φ ψ) m) ∨ !(isMulCutDef φ ψ) x”

instance isSmall_defined : ℒₒᵣ-predicate[V] (IsSmall φ ψ) via isSmallDef φ ψ :=
  ⟨fun v ↦ by simp [isSmallDef, IsSmall]⟩

instance isSmall_definable : ℒₒᵣ-predicate[V] (IsSmall φ ψ) := isSmall_defined.to_definable

end holds

section approximation

/--
The facts `F` about the elements of `P` agree, on finitely many elements and all elements below
them, with those of a certificate whose level exceeds the numerals among them.
-/
structure IsApproximable (A : ArithmeticSemisentence 2) (E : ℕ) (P : V → Prop)
    (F : ℕ → V → V → V → Prop) : Prop where
  num (n : ℕ) : P (numeral n)
  pair (x y : V) : P x → P y → P (mkPair x y)
  approx (s : List V) : (∀ x ∈ s, P x) → ∃ (c j : V) (Q : V → Prop), IsCertificate A E c j ∧
    (∀ x ∈ s, Q x) ∧ (∀ x a, Q x → a ⊴ x → Q a) ∧ (∀ a, Q a → P a) ∧
    (∀ x a y, P x → P y → Q (mkPair x y) → a ⊴ x → Q (mkPair a y)) ∧
    (∀ n : ℕ, Q (numeral n) →
      numeral n < c ∧ numeral n ⊴ j) ∧
    ∀ k ≤ 9, ∀ x y z, Q x → Q y → Q z → (F k x y z ↔ Fact c (numeral k) x y z)

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma mkPair_le_mkPair_of_isMulCut {φ : ArithmeticSemisentence 1} {ψ : ArithmeticSemisentence 2}
    (hno : ¬∃ m : V, IsGreatestGood φ ψ m) (hφ : ∀ n : ℕ, V ⊧/![numeral n] φ) {a b : V}
    (ha : IsMulCut φ ψ a) (hb : IsMulCut φ ψ b) (hx : x ⊴ a) (hy : y ⊴ b) :
    mkPair x y ⊴ mkPair a b := by
  have hx' := ha.of_le hx
  have hy' := hb.of_le hy
  exact (ha.mkPair hno hφ hb).isGood.tame.trans _ _
    ((hy'.isGood.tame₃ hx'.isGood ha.isGood).mkPair_le_left hx)
    ((ha.isGood.tame₃ hy'.isGood hb.isGood).mkPair_le_right hy)

lemma isApproximable_holds (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)
    (h : ∀ j : ℕ, ∃ c : ℕ, IsCertificate A E c j) :
    IsApproximable A E (IsSmall (V := V) (hasStageDef A E) (memStageDef A E))
      (fun k ↦ Holds (hasStageDef A E) (memStageDef A E) (isStageDef A E) (numeral k)) := by
  have hφ (n : ℕ) : V ⊧/![numeral n] (hasStageDef A E) :=
    (Defined.eval_iff _).mpr <| hasStage_numeral hA (h n)
  by_cases hm : ∃ m : V, IsGreatestGood (hasStageDef A E) (memStageDef A E) m
  · constructor
    · exact fun _ ↦ .inl hm
    · exact fun _ _ _ _ ↦ .inl hm
    intro s _
    obtain ⟨m, hm⟩ := hm
    have stage : HasStage A E m := (Defined.eval_iff _).mp <| hm.1.eval m <| cobhamLE_refl m
    obtain ⟨c, hc⟩ := stage.exists_isStage
    have hle (n : ℕ) : numeral n ⊴ m := hm.2 _ <| isGood_numeral hφ n
    use c, m, fun _ ↦ True
    have holds (k x y z : V) :
        Holds (hasStageDef A E) (memStageDef A E) (isStageDef A E) k x y z ↔ Fact c k x y z := by
      constructor
      · rintro (⟨m', hm', c', hc', h⟩ | ⟨h, -⟩)
        · obtain rfl := hm.1.tame.antisymm m' (hm'.2 m hm.1) (hm.2 m' hm'.1)
          rwa [stage.unique c hc c' ((Defined.eval_iff _).mp hc')]
        · exact absurd ⟨m, hm⟩ h
      · exact fun h ↦ .inl ⟨m, hm, c, (Defined.eval_iff _).mpr hc, h⟩
    exact ⟨hc.isCertificate, fun _ _ ↦ trivial, fun _ _ _ _ ↦ trivial, fun _ _ ↦ .inl ⟨m, hm⟩,
      fun _ _ _ _ _ _ _ ↦ trivial, fun n _ ↦ ⟨stage.lt c hc _ <| hle n, hle n⟩,
      fun k _ x y z _ _ _ ↦ holds _ x y z⟩
  · have small {x : V} : IsSmall (hasStageDef A E) (memStageDef A E) x ↔
      IsMulCut (hasStageDef A E) (memStageDef A E) x := or_iff_right hm
    have holds {k x y z : V} : Holds (hasStageDef A E) (memStageDef A E) (isStageDef A E) k x y z ↔
        MemLimit (hasStageDef A E) (memStageDef A E) (mkPair k (mkPair x (mkPair y z))) :=
      (or_iff_right fun ⟨m, h, _⟩ ↦ hm ⟨m, h⟩).trans <| and_iff_right hm
    have num (n : ℕ) := isMulCut_numeral (ψ := memStageDef A E) hm hφ n
    constructor
    · exact fun n ↦ small.mpr <| num n
    · exact fun x y hx hy ↦ small.mpr <| (small.mp hx).mkPair hm hφ (small.mp hy)
    intro s hs
    obtain ⟨b, hb, hsb⟩ :
        ∃ b : V, IsMulCut (hasStageDef A E) (memStageDef A E) b ∧ ∀ x ∈ s, x ⊴ b := by
      clear holds
      induction s with
      | nil => exact ⟨_, num 0, by simp⟩
      | cons x s ih =>
        obtain ⟨b, hb, hsb⟩ := ih fun x hx ↦ hs x <| List.mem_cons_of_mem _ hx
        have hx := small.mp <| hs x List.mem_cons_self
        simp only [List.forall_mem_cons]
        rcases hx.isGood.tame.total b with h | h
        · exact ⟨b, hb, h, hsb⟩
        · exact ⟨x, hx, cobhamLE_refl x, fun y hy ↦ hx.isGood.tame.trans b y (hsb y hy) h⟩
    have le {x y a b : V} := mkPair_le_mkPair_of_isMulCut (x := x) (y := y) (a := a) (b := b) hm hφ
    have hB₁ := hb.mkPair hm hφ hb
    have hB₂ := hb.mkPair hm hφ hB₁
    have hB := (num 9).mkPair hm hφ hB₂
    obtain ⟨j, hj, hbj, hjB⟩ := HasPath.exists_memLimit_iff (hB.1.1.add_one hm) hb.isGood
    have stage : HasStage A E j := (Defined.eval_iff _).mp <| hj.eval j <| cobhamLE_refl j
    obtain ⟨c, hc⟩ := stage.exists_isStage
    have lt {x : V} (hx : x ⊴ b) : x < c := stage.lt c hc x <| hj.tame.trans b x hx hbj
    use c, j, (· ⊴ b)
    and_intros
    · exact hc.isCertificate
    · exact hsb
    · exact fun x a hx ha ↦ hb.isGood.tame.trans x a ha hx
    · exact fun a ha ↦ small.mpr <| hb.of_le ha
    · exact fun x a y hx hy hxy ha ↦ hb.isGood.tame.trans _ _
        (le (small.mp hx) (small.mp hy) ha <| cobhamLE_refl y) hxy
    · exact fun n hn ↦ ⟨lt hn, hj.tame.trans b _ hn hbj⟩
    · intro k hk x y z hx hy hz
      have hk : (numeral k : V) ⊴ numeral 9 := numeral_cobhamLE_numeral_iff.mpr hk
      have hle := le (num 9) hB₂ hk <| le hb hB₁ hx <| le hb hb hy hz
      rw [holds, hjB _ <| hB.isGood.lt_add_one_iff.mpr <| by
        by_cases e : mkPair (numeral k) (mkPair x (mkPair y z)) =
            mkPair (numeral 9) (mkPair b (mkPair b b))
        · exact .inr e
        · exact .inl ⟨hle, e⟩]
      constructor
      · intro h
        obtain ⟨d, hd, h⟩ := (Defined.eval_iff _).mp h
        obtain rfl := stage.unique c hc d hd
        exact ⟨lt hx, lt hy, lt hz, h⟩
      · exact fun h ↦ (Defined.eval_iff _).mpr ⟨c, hc, h.mem⟩

end approximation

section clauses

namespace IsApproximable

variable {P : V → Prop} {F : ℕ → V → V → V → Prop} (h : IsApproximable A E P F) {s a b d : V}
  {n p q r R f v : ℕ}
include h

lemma zero : P 0 := by simpa using h.num 0

lemma one : P 1 := by simpa using h.num 1

lemma dom_zero : F 2 0 0 0 := by
  obtain ⟨c, j, Q, hc, hs, -, -, -, -, hF⟩ := h.approx [0] (by simp [h.zero])
  have v₀ := hs 0 (by simp)
  exact (hF 2 (by simp) _ _ _ v₀ v₀ v₀).mpr hc.dom_zero

lemma env_zero : F 3 (numeral 0) 0 0 := by
  obtain ⟨c, j, Q, hc, hs, -, -, -, -, hF⟩ := h.approx [0] (by simp [h.zero])
  have v₀ := hs 0 (by simp)
  simpa using (hF 3 (by simp) _ _ _ v₀ v₀ v₀).mpr hc.env_zero

lemma fn_total (hd : P d) (hnd : F 3 (numeral n) d 0) :
    ∃ a, P a ∧ F 2 a 0 0 ∧ F 8 (mkPair (numeral n) (numeral f)) d a := by
  obtain ⟨c, j, Q, hc, hl, hle, hQP, -, hn, hF⟩ := h.approx
    [0, numeral n, d, numeral f, mkPair (numeral n) (numeral f),
      mkPair (mkPair 1 (mkPair (numeral n) (numeral f))) d]
    (by simp [h.zero, h.one, h.num, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hnd := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hnd
  obtain ⟨a, -, ha, hda, hfa⟩ :=
    hc.fn_total _ hnd.lt₁ _ (hn _ v₃).1 _ hnd.lt₂ (hn _ v₁).2 (hn _ v₃).2 hnd
  have va : Q a := hle _ _ v₅ ha
  exact ⟨a, hQP a va, (hF 2 (by simp) _ _ _ va v₀ v₀).mpr hda,
    (hF 8 (by simp) _ _ _ v₄ v₂ va).mpr hfa⟩

lemma fn_unique (hx : P x) (hd : P d) (ha : P a) (hb : P b) (hxa : F 8 x d a) (hxb : F 8 x d b) :
    a = b := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, -, hF⟩ := h.approx [x, d, a, b] (by simp [hx, hd, ha, hb])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, -⟩ := hl
  have hxa := (hF 8 (by simp) _ _ _ v₁ v₂ v₃).mp hxa
  have hxb := (hF 8 (by simp) _ _ _ v₁ v₂ v₄).mp hxb
  exact hc.fn_unique _ hxa.lt₁ _ hxa.lt₂ _ hxa.lt₃ _ hxb.lt₃ hxa hxb

lemma eq_iff (ha : P a) (hb : P b) (hda : F 2 a 0 0) (hdb : F 2 b 0 0) :
    F 7 (mkPair (numeral 2) (numeral E)) (mkPair a (mkPair b 0)) 0 ↔ a = b := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, -, hF⟩ := h.approx
    [0, a, b, mkPair (numeral 2) (numeral E), mkPair a (mkPair b 0)]
    (by simp [h.zero, h.num, ha, hb, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, -⟩ := hl
  have hda := (hF 2 (by simp) _ _ _ v₁ v₀ v₀).mp hda
  have hdb := (hF 2 (by simp) _ _ _ v₂ v₀ v₀).mp hdb
  exact (hF 7 (by simp) _ _ _ v₃ v₄ v₀).trans <| hc.eq_iff _ hda.lt₁ _ hdb.lt₁ hda hdb

lemma vec_nil (hs : P s) (hns : F 3 (numeral n) s 0) : F 6 (numeral 0) s 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, -, hF⟩ := h.approx [0, numeral n, s]
    (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  simpa using (hF 6 (by simp) _ _ _ v₀ v₂ v₀).mpr <| hc.vec_nil _ hns.lt₁ _ hns.lt₂ hns

end IsApproximable

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma isNode_numeral (k x : ℕ) : IsNode (numeral (Nat.pair k x + 1) : V) (numeral k) (numeral x) :=
  ⟨numeral (Nat.pair k x), by simp, (eval_pairDef_numeral_iff k x).mpr rfl,
    (numeral_add_one_of_R0 _).symm⟩

namespace IsApproximable

variable {P : V → Prop} {F : ℕ → V → V → V → Prop} (h : IsApproximable A E P F) {s a b d : V}
  {n p q r R f v : ℕ}
include h

lemma env_succ (hs : P s) (ha : P a) (hns : F 3 (numeral n) s 0) (hda : F 2 a 0 0) :
    F 3 (numeral (n + 1)) (mkPair a s) 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, numeral n, s, a, numeral (n + 1), mkPair a s]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  have hda := (hF 2 (by simp) _ _ _ v₃ v₀ v₀).mp hda
  apply (hF 3 (by simp) _ _ _ v₄ v₅ v₀).mpr
  simpa using hc.env_succ _ hns.lt₁ _ hns.lt₂ _ hda.lt₁ (hn _ v₁).2 hns hda

lemma ax (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) {w : ℕ} (hp : ℕ ⊧/![p, w] A) :
    F 4 (numeral p) 0 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx [0, numeral p, numeral w]
    (by simp [h.zero, h.num])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  exact (hF 4 (by simp) _ _ _ v₁ v₀ v₀).mpr <| hc.ax _ (hn _ v₁).1 _ (hn _ v₂).1 (hn _ v₁).2
    (hn _ v₂).2 <| (eval_numeral_iff_of_deltaZero₂ hA p w).mpr hp

lemma bvar_zero (hs : P s) (ha : P a) (hns : F 3 (numeral n) s 0) (hda : F 2 a 0 0) :
    F 5 (numeral (Nat.pair 0 0 + 1)) (mkPair a s) a := by
  have has := h.env_succ hs ha hns hda
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, numeral n, s, a, numeral (n + 1), mkPair a s, numeral (Nat.pair 0 0 + 1)]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  have hda := (hF 2 (by simp) _ _ _ v₃ v₀ v₀).mp hda
  have has := (hF 3 (by simp) _ _ _ v₄ v₅ v₀).mp has
  apply (hF 5 (by simp) _ _ _ v₆ v₅ v₃).mpr
  rw [← numeral_add_one_of_R0 n] at has
  exact hc.bvar_zero _ (hn _ v₆).1 _ hns.lt₁ _ hns.lt₂ _ hda.lt₁
    (by simpa using isNode_numeral (V := V) 0 0) (hn _ v₆).2 hns hda has

lemma bvar_succ {i : ℕ} (hs : P s) (ha : P a) (hb : P b) (hns : F 3 (numeral n) s 0)
    (hdb : F 2 b 0 0) (ht : F 5 (numeral (Nat.pair 0 i + 1)) s a) :
    F 5 (numeral (Nat.pair 0 (i + 1) + 1)) (mkPair b s) a := by
  have hbs := h.env_succ hs hb hns hdb
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, numeral n, s, a, b, numeral (n + 1), mkPair b s, numeral (Nat.pair 0 i + 1),
      numeral (Nat.pair 0 (i + 1) + 1), numeral i]
    (by simp [h.zero, h.num, hs, ha, hb, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  have hdb := (hF 2 (by simp) _ _ _ v₄ v₀ v₀).mp hdb
  have hbs := (hF 3 (by simp) _ _ _ v₅ v₆ v₀).mp hbs
  have ht := (hF 5 (by simp) _ _ _ v₇ v₂ v₃).mp ht
  apply (hF 5 (by simp) _ _ _ v₈ v₆ v₃).mpr
  rw [← numeral_add_one_of_R0 n] at hbs
  exact hc.bvar_succ _ ht.lt₁ _ (hn _ v₈).1 _ (hn _ v₉).1 _ hns.lt₁ _ hns.lt₂ _ ht.lt₃ _ hdb.lt₁
    (by simpa using isNode_numeral (V := V) 0 i)
    (by simpa using isNode_numeral (V := V) 0 (i + 1)) (hn _ v₈).2 hbs hdb ht

lemma func (hs : P s) (hd : P d) (ha : P a) (hv : F 6 (numeral v) s d)
    (hf : F 8 (mkPair (numeral n) (numeral f)) d a) :
    F 5 (numeral (Nat.pair 2 (Nat.pair n (Nat.pair f v)) + 1)) s a := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [s, d, a, numeral v, numeral n, numeral f, mkPair (numeral n) (numeral f),
      numeral (Nat.pair f v), numeral (Nat.pair n (Nat.pair f v)),
      numeral (Nat.pair 2 (Nat.pair n (Nat.pair f v)) + 1)]
    (by simp [h.num, hs, hd, ha])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, v₀, -⟩ := hl
  have hv := (hF 6 (by simp) _ _ _ v₄ v₁ v₂).mp hv
  have hf := (hF 8 (by simp) _ _ _ v₇ v₂ v₃).mp hf
  apply (hF 5 (by simp) _ _ _ v₀ v₁ v₃).mpr
  exact hc.func _ (hn _ v₀).1 _ (hn _ v₉).1 _ (hn _ v₅).1 _ (hn _ v₈).1 _ (hn _ v₆).1 _ hv.lt₁ _
    hv.lt₂ _ hv.lt₃ _ hf.lt₃ (isNode_numeral _ _) ((eval_pairDef_numeral_iff _ _).mpr rfl)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) (hn _ v₀).2 hv hf

lemma vec_cons {t : ℕ} (hs : P s) (ha : P a) (hd : P d) (ht : F 5 (numeral t) s a)
    (hv : F 6 (numeral v) s d) : F 6 (numeral (Nat.pair t v + 1)) s (mkPair a d) := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [s, a, d, numeral t, numeral v, numeral (Nat.pair t v + 1), mkPair a d]
    (by simp [h.num, hs, ha, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, -⟩ := hl
  have ht := (hF 5 (by simp) _ _ _ v₄ v₁ v₂).mp ht
  have hv := (hF 6 (by simp) _ _ _ v₅ v₁ v₃).mp hv
  exact (hF 6 (by simp) _ _ _ v₆ v₁ v₇).mpr <| hc.vec_cons _ (hn _ v₆).1 _ ht.lt₁ _ hv.lt₁ _
    ht.lt₂ _ ht.lt₃ _ hv.lt₃ (isNode_numeral _ _) (hn _ v₆).2 ht hv

lemma and (hs : P s) (hp : F 4 (numeral (Nat.pair 4 (Nat.pair q r) + 1)) s 0) :
    F 4 (numeral q) s 0 ∧ F 4 (numeral r) s 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral r, numeral (Nat.pair q r),
      numeral (Nat.pair 4 (Nat.pair q r) + 1)] (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₅ v₁ v₀).mp hp
  exact (hc.and _ hp.lt₁ _ (hn _ v₄).1 _ (hn _ v₂).1 _ (hn _ v₃).1 _ hp.lt₂ (isNode_numeral _ _)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) hp).imp (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mpr
    (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mpr

lemma or (hs : P s) (hp : F 4 (numeral (Nat.pair 5 (Nat.pair q r) + 1)) s 0) :
    F 4 (numeral q) s 0 ∨ F 4 (numeral r) s 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral r, numeral (Nat.pair q r),
      numeral (Nat.pair 5 (Nat.pair q r) + 1)] (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₅ v₁ v₀).mp hp
  exact (hc.or _ hp.lt₁ _ (hn _ v₄).1 _ (hn _ v₂).1 _ (hn _ v₃).1 _ hp.lt₂ (isNode_numeral _ _)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) hp).imp (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mpr
    (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mpr

lemma all (hs : P s) (ha : P a) (hp : F 4 (numeral (Nat.pair 6 q + 1)) s 0) (hda : F 2 a 0 0) :
    F 4 (numeral q) (mkPair a s) 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, a, numeral q, numeral (Nat.pair 6 q + 1), mkPair a s]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₄ v₁ v₀).mp hp
  have hda := (hF 2 (by simp) _ _ _ v₂ v₀ v₀).mp hda
  exact (hF 4 (by simp) _ _ _ v₃ v₅ v₀).mpr <| hc.all _ hp.lt₁ _ (hn _ v₃).1 _ hp.lt₂ _ hda.lt₁
    (isNode_numeral _ _) hp hda

lemma exs (hs : P s) (hp : F 4 (numeral (Nat.pair 7 q + 1)) s 0) :
    ∃ a, P a ∧ F 2 a 0 0 ∧ F 4 (numeral q) (mkPair a s) 0 := by
  obtain ⟨c, j, Q, hc, hl, hle, hQP, hQp, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral (Nat.pair 7 q + 1), mkPair (mkPair 0 (numeral q)) s,
      mkPair (mkPair (mkPair 0 (numeral q)) s) s] (by simp [h.zero, h.num, hs, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mp hp
  obtain ⟨a, -, ha, hda, hqa⟩ :=
    hc.exs _ hp.lt₁ _ (hn _ v₂).1 _ hp.lt₂ (isNode_numeral _ _) hp
  have va : Q a := hle _ _ v₄ ha
  exact ⟨a, hQP a va, (hF 2 (by simp) _ _ _ va v₀ v₀).mpr hda,
    (hF 4 (by simp) _ _ _ v₂ (hQp _ _ _ (hQP _ v₄) hs v₅ ha) v₀).mpr hqa⟩

lemma falsum (hs : P s) (hp : F 4 (numeral (Nat.pair 3 0 + 1)) s 0) : False := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx [0, s, numeral (Nat.pair 3 0 + 1)]
    (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mp hp
  exact hc.falsum _ hp.lt₁ _ hp.lt₂ (by simpa using isNode_numeral (V := V) 3 0) hp

lemma rel (hs : P s) (hd : P d)
    (hp : F 4 (numeral (Nat.pair 0 (Nat.pair n (Nat.pair R v)) + 1)) s 0)
    (hv : F 6 (numeral v) s d) : F 7 (mkPair (numeral n) (numeral R)) d 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, d, numeral v, numeral n, numeral R, mkPair (numeral n) (numeral R),
      numeral (Nat.pair R v), numeral (Nat.pair n (Nat.pair R v)),
      numeral (Nat.pair 0 (Nat.pair n (Nat.pair R v)) + 1)]
    (by simp [h.zero, h.num, hs, hd])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₉ v₁ v₀).mp hp
  have hv := (hF 6 (by simp) _ _ _ v₃ v₁ v₂).mp hv
  exact (hF 7 (by simp) _ _ _ v₆ v₂ v₀).mpr <| hc.rel _ hp.lt₁ _ (hn _ v₈).1 _ (hn _ v₄).1 _
    (hn _ v₇).1 _ (hn _ v₅).1 _ hv.lt₁ _ hp.lt₂ _ hv.lt₃
    (by simpa using isNode_numeral (V := V) 0 (Nat.pair n (Nat.pair R v)))
    ((eval_pairDef_numeral_iff _ _).mpr rfl) ((eval_pairDef_numeral_iff _ _).mpr rfl) hp hv

lemma nrel (hs : P s) (hd : P d)
    (hp : F 4 (numeral (Nat.pair 1 (Nat.pair n (Nat.pair R v)) + 1)) s 0)
    (hv : F 6 (numeral v) s d) : ¬F 7 (mkPair (numeral n) (numeral R)) d 0 := by
  obtain ⟨c, j, Q, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, d, numeral v, numeral n, numeral R, mkPair (numeral n) (numeral R),
      numeral (Nat.pair R v), numeral (Nat.pair n (Nat.pair R v)),
      numeral (Nat.pair 1 (Nat.pair n (Nat.pair R v)) + 1)]
    (by simp [h.zero, h.num, hs, hd])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₉ v₁ v₀).mp hp
  have hv := (hF 6 (by simp) _ _ _ v₃ v₁ v₂).mp hv
  exact (hF 7 (by simp) _ _ _ v₆ v₂ v₀).not.mpr <| hc.nrel _ hp.lt₁ _ (hn _ v₈).1 _ (hn _ v₄).1 _
    (hn _ v₇).1 _ (hn _ v₅).1 _ hv.lt₁ _ hp.lt₂ _ hv.lt₃
    (by simpa using isNode_numeral (V := V) 1 (Nat.pair n (Nat.pair R v)))
    ((eval_pairDef_numeral_iff _ _).mpr rfl) ((eval_pairDef_numeral_iff _ _).mpr rfl) hp hv

end IsApproximable

end clauses

section structures

variable {L : Language} [L.Encodable] {P : V → Prop} {F : ℕ → V → V → V → Prop}
  {W : Type*} [Tarski.Structure L W]

variable (L P F) in
/-- The structure `W` is the one that the facts `F` about the elements of `P` describe. -/
structure IsDescribedBy (val : W → V) : Prop where
  mem (a : W) : P (val a) ∧ F 2 (val a) 0 0
  exists_eq (x : V) : P x → F 2 x 0 0 → ∃ a, val a = x
  rel {n : ℕ} (R : L.Rel n) (v : Fin n → W) : Tarski.Structure.rel R v ↔
    F 7 (mkPair (numeral n) (numeral (encode R))) (envCode (val ∘ v)) 0
  func {n : ℕ} (f : L.Func n) (v : Fin n → W) : F 8 (mkPair (numeral n) (numeral (encode f)))
    (envCode (val ∘ v)) (val (Tarski.Structure.func f v))

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma IsApproximable.env (h : IsApproximable A E P F) {n : ℕ} {v : Fin n → V}
    (hv : ∀ i, P (v i) ∧ F 2 (v i) 0 0) :
    P (envCode v) ∧ F 3 (numeral n) (envCode v) 0 := by
  induction n with
  | zero => exact ⟨h.zero, h.env_zero⟩
  | succ n ih =>
    have ih := ih fun i ↦ hv i.succ
    exact ⟨h.pair _ _ (hv 0).1 ih.1, h.env_succ ih.1 (hv 0).1 ih.2 (hv 0).2⟩

namespace IsDescribedBy

variable {val : W → V} (hW : IsDescribedBy L P F val) (h : IsApproximable A E P F)
include hW h

lemma env {n : ℕ} (v : Fin n → W) :
    P (envCode (val ∘ v)) ∧ F 3 (numeral n) (envCode (val ∘ v)) 0 :=
  h.env fun i ↦ hW.mem (v i)

lemma bvar {n : ℕ} (v : Fin n → W) (i : Fin n) :
    F 5 (numeral (Nat.pair 0 i + 1)) (envCode (val ∘ v)) (val (v i)) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    have env := hW.env h fun i ↦ v i.succ
    cases i using Fin.cases with
    | zero => exact h.bvar_zero env.1 (hW.mem _).1 env.2 (hW.mem _).2
    | succ i =>
      exact h.bvar_succ env.1 (hW.mem _).1 (hW.mem _).1 env.2 (hW.mem _).2 <|
        ih (fun i ↦ v i.succ) i

lemma vec {n k : ℕ} (v : Fin n → W) (t : Fin k → ClosedSemiterm L n)
    (ht : ∀ i, F 5 (numeral (encode (t i))) (envCode (val ∘ v)) (val ((t i).val v Empty.elim))) :
    F 6 (numeral (Matrix.vecToNat fun i ↦ encode (t i))) (envCode (val ∘ v))
      (envCode (val ∘ fun i ↦ (t i).val v Empty.elim)) := by
  have env := hW.env h v
  induction k with
  | zero => exact h.vec_nil env.1 env.2
  | succ k ih =>
    have e : (fun i ↦ encode (t i)) = encode (t 0) :> fun i ↦ encode (t i.succ) := by
      funext i
      cases i using Fin.cases <;> simp
    rw [e, Matrix.encode_succ]
    exact h.vec_cons env.1 (hW.mem _).1 (hW.env h fun i ↦ (t i.succ).val v Empty.elim).1 (ht 0) <|
      ih (fun i ↦ t i.succ) fun i ↦ ht i.succ

lemma term {n : ℕ} (v : Fin n → W) (t : ClosedSemiterm L n) :
    F 5 (numeral (encode t)) (envCode (val ∘ v)) (val (t.val v Empty.elim)) := by
  induction t with
  | bvar i => exact hW.bvar h v i
  | fvar x => exact x.elim
  | func f t ih =>
    have := hW.func f fun i ↦ (t i).val v Empty.elim
    exact h.func (hW.env h v).1 (hW.env h _).1 (hW.mem _).1 (hW.vec h v t ih) this

lemma evalb {n : ℕ} (v : Fin n → W) (φ : Semisentence L n)
    (hφ : F 4 (numeral (encode φ)) (envCode (val ∘ v)) 0) : W ⊧/v φ := by
  have env := (hW.env h v).1
  match φ with
  | .rel R t =>
    have := (hW.rel R fun i ↦ (t i).val v Empty.elim).mpr <|
      h.rel env (hW.env h _).1 hφ <| hW.vec h v t fun i ↦ hW.term h v (t i)
    simpa [Semiformula.eval_rel, Function.comp_def] using this
  | .nrel R t =>
    have := (hW.rel R fun i ↦ (t i).val v Empty.elim).not.mpr <|
      h.nrel env (hW.env h _).1 hφ <| hW.vec h v t fun i ↦ hW.term h v (t i)
    simpa [Semiformula.eval_nrel, Function.comp_def] using this
  | ⊤ => simp
  | ⊥ => exact (h.falsum env hφ).elim
  | φ ⋏ ψ =>
    have := h.and env hφ
    simpa using ⟨evalb v φ this.1, evalb v ψ this.2⟩
  | φ ⋎ ψ =>
    have : W ⊧/v φ ∨ W ⊧/v ψ := (h.or env hφ).imp (evalb v φ) (evalb v ψ)
    simpa using this
  | ∀¹ φ =>
    have (a : W) : W ⊧/(a :> v) φ := evalb (a :> v) φ <|
      h.all env (hW.mem a).1 hφ (hW.mem a).2
    simpa using this
  | ∃¹ φ =>
    obtain ⟨x, hx, hdx, hφ⟩ := h.exs env hφ
    obtain ⟨a, rfl⟩ := hW.exists_eq x hx hdx
    have : W ⊧/(a :> v) φ := evalb (a :> v) φ hφ
    simpa using ⟨a, this⟩

end IsDescribedBy

end structures

section translation

variable {φ : ArithmeticSemisentence 1} {ψ σ : ArithmeticSemisentence 2}

/-- `x` belongs to the domain of the interpreted structure. -/
def InDomain (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) (x : V) : Prop :=
  IsSmall φ ψ x ∧ Holds φ ψ σ (numeral 2) x 0 0

/-- `x` belongs to the domain of the interpreted structure. -/
def inDomainDef (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. !(isSmallDef φ ψ) x ∧ !(holdsDef φ ψ σ) 2 x 0 0”

instance inDomain_defined : ℒₒᵣ-predicate[V] (InDomain φ ψ σ) via inDomainDef φ ψ σ :=
  ⟨fun v ↦ by simp [inDomainDef, InDomain]⟩

instance inDomain_definable : ℒₒᵣ-predicate[V] (InDomain φ ψ σ) := inDomain_defined.to_definable

/-- The relation of arity `n` and code `R` of the interpreted structure. -/
def describedRel (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) (n R : ℕ) :
    ArithmeticSemisentence n :=
  (holdsDef φ ψ σ)/[‘7’, ‘!mkPairTerm ↑n ↑R’, envCodeTerm fun i ↦ #i, ‘0’]

@[simp]
lemma eval_describedRel {n R : ℕ} {v : Fin n → V} : V ⊧/v (describedRel φ ψ σ n R) ↔
    Holds φ ψ σ (numeral 7) (mkPair (numeral n) (numeral R)) (envCode v) 0 := by
  simp [describedRel]

/-- The function of arity `n` and code `f` of the interpreted structure. -/
def describedFunc (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) (n f : ℕ) :
    ArithmeticSemisentence (n + 1) :=
  (holdsDef φ ψ σ)/[‘8’, ‘!mkPairTerm ↑n ↑f’, envCodeTerm fun i : Fin n ↦ #i.succ, #0]

@[simp]
lemma eval_describedFunc {n f : ℕ} {a : V} {v : Fin n → V} :
    V ⊧/(a :> v) (describedFunc φ ψ σ n f) ↔
      Holds φ ψ σ (numeral 8) (mkPair (numeral n) (numeral f)) (envCode v) a := by
  simp [describedFunc]

variable {L : Language} [L.Encodable] [L.Eq]

variable (L) in
/-- The code of the equality symbol of `L`. -/
abbrev eqCode : ℕ := encode (Language.Eq.eq : L.Rel 2)

end translation

end Visser

open Visser

section translation

variable {L : Language} [L.Encodable] [L.Eq]

/-- The translation that describes the models coded by the certificates. -/
def certificateTranslation (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)
    (h : ∀ j : ℕ, ∃ c : ℕ, IsCertificate A (eqCode L) c j) :
    DirectTranslation 𝗥₀ L :=
  let E := eqCode L
  { domain := ⟨inDomainDef (hasStageDef A E) (memStageDef A E) (isStageDef A E)⟩
    rel := fun {n} R ↦
      ⟨describedRel (hasStageDef A E) (memStageDef A E) (isStageDef A E) n (encode R)⟩
    func := fun {n} f ↦
      ⟨describedFunc (hasStageDef A E) (memStageDef A E) (isStageDef A E) n (encode f)⟩
    domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
      have := isApproximable_holds (V := V) hA h
      use 0
      simpa only [Semiformula.Operator.val, Semiformula.eval_substs] using
        (Defined.eval_iff _).mpr ⟨this.zero, this.dom_zero⟩
    func_defined := fun {n} f ↦ complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
      have := isApproximable_holds (V := V) hA h
      intro e he
      have he (i) := (Defined.eval_iff _).mp (he i)
      have env := this.env he
      obtain ⟨a, ha, hda, hfa⟩ := this.fn_total (f := encode f) env.1 env.2
      exact (existsUnique_congr fun a ↦ and_congr (Defined.eval_iff _) eval_describedFunc).mpr
        ⟨a, ⟨⟨ha, hda⟩, hfa⟩, fun b ⟨hb, hfb⟩ ↦
          this.fn_unique (this.pair _ _ (this.num _) (this.num _)) env.1 hb.1 ha hfb hfa⟩
    preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
      have := isApproximable_holds (V := V) hA h
      intro x y hx hy
      have hx := (Defined.eval_iff _).mp hx
      have hy := (Defined.eval_iff _).mp hy
      exact eval_describedRel.trans <| this.eq_iff hx.1 hy.1 hx.2 hy.2 }

lemma certificateTranslation.isDescribedBy_model [V↓[ℒₒᵣ] ⊧* 𝗥₀] (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)
    (h : ∀ j : ℕ, ∃ c : ℕ, IsCertificate A (eqCode L) c j) :
    IsDescribedBy L (IsSmall (hasStageDef A (eqCode L)) (memStageDef A (eqCode L)))
      (fun k ↦ Holds (hasStageDef A (eqCode L)) (memStageDef A (eqCode L)) (isStageDef A (eqCode L))
        (numeral k))
      (Model.val : (certificateTranslation hA h).Model V → V) where
  mem a := (inDomain_defined.iff _).mp a.dom
  exists_eq x hx hdx := ⟨⟨x, (inDomain_defined.iff _).mpr ⟨hx, hdx⟩⟩, rfl⟩
  rel _ _ := eval_describedRel
  func f v := eval_describedFunc.mp <| Model.eval_func f v

variable {T : Theory L}

lemma nonempty_interpretation (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)
    (h : ∀ j : ℕ, ∃ c : ℕ, IsCertificate A (eqCode L) c j)
    (hT : ∀ σ ∈ T, ∃ w : ℕ, ℕ ⊧/![encode σ, w] A) : Nonempty (𝗥₀ ⊳ T) :=
  ⟨⟨certificateTranslation hA h, fun σ hσ ↦ complete.{0} _ _ fun V _ _ ↦
    let ⟨_, hw⟩ := hT σ hσ
    have := isApproximable_holds (V := V) hA h
    Model.translate_iff.mpr <|
      (certificateTranslation.isDescribedBy_model hA h).evalb this ![] σ <| this.ax hA hw⟩⟩

end translation

section theorems

open Theory

variable {L : Language} [L.Eq] [L.Finite] {T : Theory L}

variable [L.Encodable] [L.Primcodable] [𝗘𝗤 L ⪯ T]

/--
A recursively enumerable locally finitely satisfiable theory is interpretable in $\mathsf{R}_0$.
-/
lemma nonempty_interpretation_of_locallyFinitelySatisfiable (hT : REPred (· ∈ T))
    (h : T.LocallyFinitelySatisfiable) : Nonempty (𝗥₀ ⊳ T) := by
  obtain ⟨A, hA₀, hA⟩ : ∃ A : ArithmeticSemisentence 2, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A ∧
      ∀ p, (∃ σ ∈ T, encode σ = p) ↔ ∃ w, ℕ ⊧/![p, w] A := by
    have hP : REPred fun p ↦ ∃ σ ∈ T, encode σ = p := by
      have heq : PrimrecPred fun x : ℕ × Sentence L ↦ encode x.2 = x.1 :=
        Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst
      exact REPred.projection (p := fun x : ℕ × Sentence L ↦ x.2 ∈ T ∧ encode x.2 = x.1) <|
        (hT.comp Computable.snd).and heq.computablePred.to_re
    have hσ : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (codeOfREPred fun p ↦ ∃ σ ∈ T, encode σ = p) := by
      simp [codeOfREPred, codeOfPartrec']
    obtain ⟨ψ, hψ⟩ := Bounding.Prenex.models_exists_prenex.{_, 0} (Γ' := 𝚺) hσ
    use “p w. !ψ.sigmaInv.val w p”
    and_intros
    · simp
    · intro p
      simpa using (codeOfREPred_spec hP (x := p)).symm.trans
        ((hψ ℕ ![p] Empty.elim).trans (ψ.models_sigmaInv _))
  obtain ⟨F, hF, hfin, hEQ⟩ := exists_finite_subset_weakerThan (Theory.Eq.finite (L := L))
    (inferInstance : 𝗘𝗤 L ⪯ T)
  apply nonempty_interpretation hA₀ _ fun σ hσ ↦ (hA _).mp ⟨σ, hσ, rfl⟩
  intro j
  let G : Theory L := F ∪ {σ | σ ∈ T ∧ encode σ ≤ j}
  have hG : G.Finite := hfin.union <|
    Set.Finite.of_finite_image ((Set.finite_Iic j).subset <| by rintro _ ⟨σ, ⟨-, h⟩, rfl⟩; exact h)
      encode_injective.injOn
  have : 𝗘𝗤 L ⪯ G := hEQ.trans <| Entailment.WeakerThan.ofSubset Set.subset_union_left
  obtain ⟨V, _, _, _, _, hV⟩ :=
    (h G (Set.union_subset hF fun _ h ↦ h.1) hG).exists_eq
  apply exists_isCertificate (V := V)
  intro p hp w _ hw
  obtain ⟨σ, hσ, rfl⟩ := (hA p).mpr ⟨w, hw⟩
  exact ⟨σ, rfl, models_theory_iff.mp hV σ <| .inr ⟨hσ, hp⟩⟩

/--
A recursively enumerable theory of a finite language is interpretable in $\mathsf{R}_0$ if and only
if it is locally finitely satisfiable.
- [Hor11, §3, Theorem 3.3]
- [Hor12, §4]
-/
theorem nonempty_interpretation_iff_locallyFinitelySatisfiable (hT : REPred (· ∈ T)) :
    Nonempty (𝗥₀ ⊳ T) ↔ T.LocallyFinitelySatisfiable :=
  ⟨fun ⟨π⟩ ↦ π.locallyFinitelySatisfiable locallyFinitelySatisfiable,
    nonempty_interpretation_of_locallyFinitelySatisfiable hT⟩

/--
A recursively enumerable theory of a finite language is not interpretable in $\mathsf{R}_0$ if and
only if it is not locally finitely satisfiable.
- [Hor11, §3, Theorem 3.3]
-/
theorem notInterprets_iff_not_locallyFinitelySatisfiable (hT : REPred (· ∈ T)) :
    𝗥₀ ⋫ T ↔ ¬T.LocallyFinitelySatisfiable :=
  notInterprets_iff.trans (nonempty_interpretation_iff_locallyFinitelySatisfiable hT).not

end theorems

end FFL.FirstOrder.Arithmetic.R0

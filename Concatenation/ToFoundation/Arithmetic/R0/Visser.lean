module

public import Concatenation.ToFoundation.Arithmetic.R0.LocallyFinitelySatisfiable
public import Concatenation.ToFoundation.Arithmetic.R0.Naming

/-!
# Interpretability in $\mathsf{R}_0$

A recursively enumerable theory of a finite language is interpretable in $\mathsf{R}_0$ if and only
if it is locally finitely satisfiable.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open ORingStructure Encodable

variable {M : Type*} [ORingStructure M] {A : ArithmeticSemisentence 2} {E : ℕ}
  {c j k x y z : M}

section stage

/-- `c` is the least certificate of level `j`. -/
@[mk_iff]
structure IsStage (A : ArithmeticSemisentence 2) (E : ℕ) (j c : M) : Prop where
  isCertificate : IsCertificate A E c j
  eq_of_le : ∀ d, d ⊴ c → IsCertificate A E d j → d = c

/-- `c` is the least certificate of level `j`. -/
def isStage (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 := “j c.
  !(isCertificate A E) c j ∧ ∀ d, !cobhamLE d c → !(isCertificate A E) d j → d = c”

@[simp]
lemma eval_isStage : M ⊧/![j, c] (isStage A E) ↔ IsStage A E j c := by
  simp [isStage, isStage_iff]

/-- `j` has a unique least certificate, which bounds the elements up to `j`. -/
@[mk_iff]
structure HasStage (A : ArithmeticSemisentence 2) (E : ℕ) (j : M) : Prop where
  exists_isStage : ∃ c, IsStage A E j c
  unique : ∀ c, IsStage A E j c → ∀ d, IsStage A E j d → c = d
  lt : ∀ c, IsStage A E j c → ∀ x, x ⊴ j → x < c

/-- `j` has a unique least certificate, which bounds the elements up to `j`. -/
def hasStage (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 1 := “j.
  (∃ c, !(isStage A E) j c) ∧ (∀ c, !(isStage A E) j c → ∀ d, !(isStage A E) j d → c = d) ∧
  ∀ c, !(isStage A E) j c → ∀ x, !cobhamLE x j → x < c”

@[simp]
lemma eval_hasStage : M ⊧/![j] (hasStage A E) ↔ HasStage A E j := by
  simp [hasStage, hasStage_iff]

/-- `x` belongs to the least certificate of level `j`. -/
def MemStage (A : ArithmeticSemisentence 2) (E : ℕ) (x j : M) : Prop :=
  ∃ c, IsStage A E j c ∧ M ⊧/![x, c] bitDef.val

/-- `x` belongs to the least certificate of level `j`. -/
def memStage (A : ArithmeticSemisentence 2) (E : ℕ) : ArithmeticSemisentence 2 :=
  “x j. ∃ c, !(isStage A E) j c ∧ !bitDef x c”

@[simp]
lemma eval_memStage : M ⊧/![x, j] (memStage A E) ↔ MemStage A E x j := by
  simp [memStage, MemStage]

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀] (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)

lemma eval_numeral_iff_of_deltaZero₂ (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) (i j : ℕ) :
    M ⊧/![numeral i, numeral j] A ↔ ℕ ⊧/![i, j] A := by
  have e : (numeral ∘ ![i, j] : Fin 2 → M) = ![numeral i, numeral j] := by
    funext x
    match x with | 0 | 1 => rfl
  constructor
  · intro h
    by_contra h'
    have := bold_sigma_one_completeness' (M := M) (σ := ∼A) (by simpa using hA.of_zero)
      (bv := ![i, j]) (by simpa using h')
    exact absurd h (by simpa [e] using this)
  · intro h
    simpa [e] using bold_sigma_one_completeness' (M := M) hA.of_zero h

include hA in
lemma isCertificate_numeral_iff (i j : ℕ) :
    IsCertificate A E (numeral i : M) (numeral j) ↔ IsCertificate A E i j := by
  simpa using eval_numeral_iff_of_deltaZero₂ (M := M) (hierarchy_isCertificate (E := E) hA) i j

include hA in
lemma hasStage_numeral {j : ℕ} (h : ∃ c : ℕ, IsCertificate A E c j) :
    HasStage A E (numeral j : M) := by
  classical
  have cert : IsCertificate A E (numeral (Nat.find h) : M) (numeral j) :=
    (isCertificate_numeral_iff hA _ _).mpr <| Nat.find_spec h
  have stage : IsStage A E (numeral j : M) (numeral (Nat.find h)) := ⟨cert, fun d hd hdj ↦ by
    obtain ⟨i, hi, rfl⟩ := eq_numeral_of_cobhamLE_numeral hd
    have := Nat.find_min' h <| (isCertificate_numeral_iff hA _ _).mp hdj
    rw [le_antisymm hi this]⟩
  have eq (c : M) (hc : IsStage A E (numeral j : M) c) : c = numeral (Nat.find h) := by
    rcases cobhamLE_numeral_or (x := c) (Nat.find h) with h' | h'
    · exact stage.eq_of_le c h' hc.isCertificate
    · exact (hc.eq_of_le _ h' cert).symm
  constructor
  · exact ⟨_, stage⟩
  · intro c hc d hd
    rw [eq c hc, eq d hd]
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
def Holds (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) (k x y z : M) : Prop :=
  (∃ m, IsGreatestGood φ ψ m ∧ ∃ c, M ⊧/![m, c] σ ∧ Fact c k x y z) ∨
  (¬∃ m : M, IsGreatestGood φ ψ m) ∧ MemLimit φ ψ (mkPair k (mkPair x (mkPair y z)))

/--
The fact of tag `k` about `x`, `y` and `z` belongs to the set that `σ` assigns to the greatest good
element or, if there is none, to the limit of the sets defined by `ψ`.
-/
def holds (φ : ArithmeticSemisentence 1) (ψ σ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 4 := “k x y z.
  (∃ m, !(isGreatestGood φ ψ) m ∧ ∃ c, !σ m c ∧ !fact c k x y z) ∨
  (¬∃ m, !(isGreatestGood φ ψ) m) ∧
    !(memLimit φ ψ) (!mkPairTerm k (!mkPairTerm x (!mkPairTerm y z)))”

@[simp]
lemma eval_holds : M ⊧/![k, x, y, z] (holds φ ψ σ) ↔ Holds φ ψ σ k x y z := by
  simp [holds, Holds]

/-- There is a greatest good element, or `x` belongs to the shortened cut. -/
def IsSmall (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) (x : M) : Prop :=
  (∃ m : M, IsGreatestGood φ ψ m) ∨ IsMulCut φ ψ x

/-- There is a greatest good element, or `x` belongs to the shortened cut. -/
def isSmall (φ : ArithmeticSemisentence 1) (ψ : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 1 :=
  “x. (∃ m, !(isGreatestGood φ ψ) m) ∨ !(isMulCut φ ψ) x”

@[simp]
lemma eval_isSmall : M ⊧/![x] (isSmall φ ψ) ↔ IsSmall φ ψ x := by
  simp [isSmall, IsSmall]

end holds

section approximation

/--
The facts `F` about the elements of `W` agree, on finitely many elements and all elements below
them, with those of a certificate whose level exceeds the numerals among them.
-/
structure IsApproximable (A : ArithmeticSemisentence 2) (E : ℕ) (W : M → Prop)
    (F : ℕ → M → M → M → Prop) : Prop where
  num (n : ℕ) : W (numeral n)
  pair (x y : M) : W x → W y → W (mkPair x y)
  approx (s : List M) : (∀ x ∈ s, W x) → ∃ (c j : M) (V : M → Prop), IsCertificate A E c j ∧
    (∀ x ∈ s, V x) ∧ (∀ x a, V x → a ⊴ x → V a) ∧ (∀ a, V a → W a) ∧
    (∀ x a y, W x → W y → V (mkPair x y) → a ⊴ x → V (mkPair a y)) ∧
    (∀ n : ℕ, V (numeral n) →
      numeral n < c ∧ numeral n ⊴ j) ∧
    ∀ k ≤ 9, ∀ x y z, V x → V y → V z → (F k x y z ↔ Fact c (numeral k) x y z)

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma mkPair_le_mkPair_of_isMulCut {φ : ArithmeticSemisentence 1} {ψ : ArithmeticSemisentence 2}
    (hno : ¬∃ m : M, IsGreatestGood φ ψ m) (hφ : ∀ n : ℕ, M ⊧/![numeral n] φ) {a b : M}
    (ha : IsMulCut φ ψ a) (hb : IsMulCut φ ψ b) (hx : x ⊴ a) (hy : y ⊴ b) :
    mkPair x y ⊴ mkPair a b := by
  have hx' := ha.of_le hx
  have hy' := hb.of_le hy
  exact (ha.mkPair hno hφ hb).isGood.tame.trans _ _
    ((hy'.isGood.tame₃ hx'.isGood ha.isGood).mkPair_le_left hx)
    ((ha.isGood.tame₃ hy'.isGood hb.isGood).mkPair_le_right hy)

lemma isApproximable_holds (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A)
    (h : ∀ j : ℕ, ∃ c : ℕ, IsCertificate A E c j) :
    IsApproximable A E (IsSmall (M := M) (hasStage A E) (memStage A E))
      (fun k ↦ Holds (hasStage A E) (memStage A E) (isStage A E) (numeral k)) := by
  have hφ (n : ℕ) : M ⊧/![numeral n] (hasStage A E) :=
    eval_hasStage.mpr <| hasStage_numeral hA (h n)
  by_cases hm : ∃ m : M, IsGreatestGood (hasStage A E) (memStage A E) m
  · refine ⟨fun _ ↦ .inl hm, fun _ _ _ _ ↦ .inl hm, fun s _ ↦ ?_⟩
    obtain ⟨m, hm⟩ := hm
    have stage : HasStage A E m := eval_hasStage.mp <| hm.1.eval m <| cobhamLE_refl m
    obtain ⟨c, hc⟩ := stage.exists_isStage
    have hle (n : ℕ) : numeral n ⊴ m := hm.2 _ <| isGood_numeral hφ n
    refine ⟨c, m, fun _ ↦ True, hc.isCertificate, fun _ _ ↦ trivial, fun _ _ _ _ ↦ trivial,
      fun _ _ ↦ .inl ⟨m, hm⟩, fun _ _ _ _ _ _ _ ↦ trivial, fun n _ ↦ ⟨stage.lt c hc _ <| hle n, hle n⟩,
      fun k _ x y z _ _ _ ↦ ⟨?_, ?_⟩⟩
    · rintro (⟨m', hm', c', hc', h⟩ | ⟨h, -⟩)
      · obtain rfl := hm.1.tame.antisymm m' (hm'.2 m hm.1) (hm.2 m' hm'.1)
        rwa [stage.unique c hc c' (eval_isStage.mp hc')]
      · exact absurd ⟨m, hm⟩ h
    · exact fun h ↦ .inl ⟨m, hm, c, eval_isStage.mpr hc, h⟩
  · have small {x : M} : IsSmall (hasStage A E) (memStage A E) x ↔
      IsMulCut (hasStage A E) (memStage A E) x := or_iff_right hm
    have holds {k x y z : M} : Holds (hasStage A E) (memStage A E) (isStage A E) k x y z ↔
        MemLimit (hasStage A E) (memStage A E) (mkPair k (mkPair x (mkPair y z))) :=
      (or_iff_right fun ⟨m, h, _⟩ ↦ hm ⟨m, h⟩).trans <| and_iff_right hm
    have num (n : ℕ) := isMulCut_numeral (ψ := memStage A E) hm hφ n
    refine ⟨fun n ↦ small.mpr <| num n,
      fun x y hx hy ↦ small.mpr <| (small.mp hx).mkPair hm hφ (small.mp hy), fun s hs ↦ ?_⟩
    obtain ⟨b, hb, hsb⟩ : ∃ b : M, IsMulCut (hasStage A E) (memStage A E) b ∧ ∀ x ∈ s, x ⊴ b := by
      clear holds
      induction s with
      | nil => exact ⟨_, num 0, by simp⟩
      | cons x s ih =>
        obtain ⟨b, hb, hsb⟩ := ih fun x hx ↦ hs x <| List.mem_cons_of_mem _ hx
        have hx := small.mp <| hs x List.mem_cons_self
        rcases hx.isGood.tame.total b with h | h
        · refine ⟨b, hb, fun y hy ↦ ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact h
          · exact hsb y hy
        · refine ⟨x, hx, fun y hy ↦ ?_⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact cobhamLE_refl y
          · exact hx.isGood.tame.trans b y (hsb y hy) h
    have hB₁ := hb.mkPair hm hφ hb
    have hB₂ := hb.mkPair hm hφ hB₁
    have hB := (num 9).mkPair hm hφ hB₂
    obtain ⟨j, hj, hbj, hjB⟩ := HasPath.exists_memLimit_iff (hB.1.1.add_one hm) hb.isGood
    have stage : HasStage A E j := eval_hasStage.mp <| hj.eval j <| cobhamLE_refl j
    obtain ⟨c, hc⟩ := stage.exists_isStage
    have lt {x : M} (hx : x ⊴ b) : x < c := stage.lt c hc x <| hj.tame.trans b x hx hbj
    refine ⟨c, j, (· ⊴ b), hc.isCertificate, hsb, fun x a hx ha ↦ hb.isGood.tame.trans x a ha hx,
      fun a ha ↦ small.mpr <| hb.of_le ha, fun x a y hx hy hxy ha ↦
        hb.isGood.tame.trans _ _ (mkPair_le_mkPair_of_isMulCut hm hφ (small.mp hx) (small.mp hy) ha
          <| cobhamLE_refl y) hxy,
      fun n hn ↦ ⟨lt hn, hj.tame.trans b _ hn hbj⟩,
      fun k hk x y z hx hy hz ↦ ?_⟩
    have hk : (numeral k : M) ⊴ numeral 9 := numeral_cobhamLE_numeral_iff.mpr hk
    have hle := mkPair_le_mkPair_of_isMulCut hm hφ (num 9) hB₂ hk <|
      mkPair_le_mkPair_of_isMulCut hm hφ hb hB₁ hx <|
        mkPair_le_mkPair_of_isMulCut hm hφ hb hb hy hz
    rw [holds, hjB _ <| hB.isGood.lt_add_one_iff.mpr <| by
      by_cases e : mkPair (numeral k) (mkPair x (mkPair y z)) =
          mkPair (numeral 9) (mkPair b (mkPair b b))
      · exact .inr e
      · exact .inl ⟨hle, e⟩]
    constructor
    · intro h
      obtain ⟨d, hd, h⟩ := eval_memStage.mp h
      obtain rfl := stage.unique c hc d hd
      exact ⟨lt hx, lt hy, lt hz, h⟩
    · exact fun h ↦ eval_memStage.mpr ⟨c, hc, h.mem⟩

end approximation

section clauses

namespace IsApproximable

variable {W : M → Prop} {F : ℕ → M → M → M → Prop} (h : IsApproximable A E W F) {s a b d : M}
  {n p q r R f v : ℕ}
include h

lemma zero : W 0 := by simpa using h.num 0

lemma one : W 1 := by simpa using h.num 1

lemma dom_zero : F 2 0 0 0 := by
  obtain ⟨c, j, V, hc, hs, -, -, -, -, hF⟩ := h.approx [0] (by simp [h.zero])
  have v₀ := hs 0 (by simp)
  exact (hF 2 (by simp) _ _ _ v₀ v₀ v₀).mpr hc.dom_zero

lemma env_zero : F 3 (numeral 0) 0 0 := by
  obtain ⟨c, j, V, hc, hs, -, -, -, -, hF⟩ := h.approx [0] (by simp [h.zero])
  have v₀ := hs 0 (by simp)
  simpa using (hF 3 (by simp) _ _ _ v₀ v₀ v₀).mpr hc.env_zero

lemma fn_total (hd : W d) (hnd : F 3 (numeral n) d 0) :
    ∃ a, W a ∧ F 2 a 0 0 ∧ F 8 (mkPair (numeral n) (numeral f)) d a := by
  obtain ⟨c, j, V, hc, hl, hle, hVW, -, hn, hF⟩ := h.approx
    [0, numeral n, d, numeral f, mkPair (numeral n) (numeral f),
      mkPair (mkPair 1 (mkPair (numeral n) (numeral f))) d]
    (by simp [h.zero, h.one, h.num, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hnd := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hnd
  obtain ⟨a, -, ha, hda, hfa⟩ :=
    hc.fn_total _ hnd.lt₁ _ (hn _ v₃).1 _ hnd.lt₂ (hn _ v₁).2 (hn _ v₃).2 hnd
  have va : V a := hle _ _ v₅ ha
  exact ⟨a, hVW a va, (hF 2 (by simp) _ _ _ va v₀ v₀).mpr hda,
    (hF 8 (by simp) _ _ _ v₄ v₂ va).mpr hfa⟩

lemma fn_unique (hx : W x) (hd : W d) (ha : W a) (hb : W b) (hxa : F 8 x d a) (hxb : F 8 x d b) :
    a = b := by
  obtain ⟨c, j, V, hc, hl, -, -, -, -, hF⟩ := h.approx [x, d, a, b] (by simp [hx, hd, ha, hb])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, -⟩ := hl
  have hxa := (hF 8 (by simp) _ _ _ v₁ v₂ v₃).mp hxa
  have hxb := (hF 8 (by simp) _ _ _ v₁ v₂ v₄).mp hxb
  exact hc.fn_unique _ hxa.lt₁ _ hxa.lt₂ _ hxa.lt₃ _ hxb.lt₃ hxa hxb

lemma eq_iff (ha : W a) (hb : W b) (hda : F 2 a 0 0) (hdb : F 2 b 0 0) :
    F 7 (mkPair (numeral 2) (numeral E)) (mkPair a (mkPair b 0)) 0 ↔ a = b := by
  obtain ⟨c, j, V, hc, hl, -, -, -, -, hF⟩ := h.approx
    [0, a, b, mkPair (numeral 2) (numeral E), mkPair a (mkPair b 0)]
    (by simp [h.zero, h.num, ha, hb, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, -⟩ := hl
  have hda := (hF 2 (by simp) _ _ _ v₁ v₀ v₀).mp hda
  have hdb := (hF 2 (by simp) _ _ _ v₂ v₀ v₀).mp hdb
  exact (hF 7 (by simp) _ _ _ v₃ v₄ v₀).trans <| hc.eq_iff _ hda.lt₁ _ hdb.lt₁ hda hdb

lemma vec_nil (hs : W s) (hns : F 3 (numeral n) s 0) : F 6 (numeral 0) s 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, -, hF⟩ := h.approx [0, numeral n, s]
    (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  simpa using (hF 6 (by simp) _ _ _ v₀ v₂ v₀).mpr <| hc.vec_nil _ hns.lt₁ _ hns.lt₂ hns

end IsApproximable

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma isNode_numeral (k x : ℕ) : IsNode (numeral (Nat.pair k x + 1) : M) (numeral k) (numeral x) :=
  ⟨numeral (Nat.pair k x), by simp, (eval_pairDef_numeral_iff k x).mpr rfl,
    (numeral_add_one _).symm⟩

namespace IsApproximable

variable {W : M → Prop} {F : ℕ → M → M → M → Prop} (h : IsApproximable A E W F) {s a b d : M}
  {n p q r R f v : ℕ}
include h

lemma env_succ (hs : W s) (ha : W a) (hns : F 3 (numeral n) s 0) (hda : F 2 a 0 0) :
    F 3 (numeral (n + 1)) (mkPair a s) 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, numeral n, s, a, numeral (n + 1), mkPair a s]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  have hda := (hF 2 (by simp) _ _ _ v₃ v₀ v₀).mp hda
  apply (hF 3 (by simp) _ _ _ v₄ v₅ v₀).mpr
  rw [← numeral_add_one n]
  exact hc.env_succ _ hns.lt₁ _ hns.lt₂ _ hda.lt₁ (hn _ v₁).2 hns hda

lemma ax (hA : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 0 A) {w : ℕ} (hp : ℕ ⊧/![p, w] A) :
    F 4 (numeral p) 0 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx [0, numeral p, numeral w]
    (by simp [h.zero, h.num])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  exact (hF 4 (by simp) _ _ _ v₁ v₀ v₀).mpr <| hc.ax _ (hn _ v₁).1 _ (hn _ v₂).1 (hn _ v₁).2
    (hn _ v₂).2 <| (eval_numeral_iff_of_deltaZero₂ hA p w).mpr hp

lemma bvar_zero (hs : W s) (ha : W a) (hns : F 3 (numeral n) s 0) (hda : F 2 a 0 0) :
    F 5 (numeral (Nat.pair 0 0 + 1)) (mkPair a s) a := by
  have has := h.env_succ hs ha hns hda
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, numeral n, s, a, numeral (n + 1), mkPair a s, numeral (Nat.pair 0 0 + 1)]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, -⟩ := hl
  have hns := (hF 3 (by simp) _ _ _ v₁ v₂ v₀).mp hns
  have hda := (hF 2 (by simp) _ _ _ v₃ v₀ v₀).mp hda
  have has := (hF 3 (by simp) _ _ _ v₄ v₅ v₀).mp has
  apply (hF 5 (by simp) _ _ _ v₆ v₅ v₃).mpr
  rw [← numeral_add_one n] at has
  exact hc.bvar_zero _ (hn _ v₆).1 _ hns.lt₁ _ hns.lt₂ _ hda.lt₁
    (by simpa using isNode_numeral (M := M) 0 0) (hn _ v₆).2 hns hda has

lemma bvar_succ {i : ℕ} (hs : W s) (ha : W a) (hb : W b) (hns : F 3 (numeral n) s 0)
    (hdb : F 2 b 0 0) (ht : F 5 (numeral (Nat.pair 0 i + 1)) s a) :
    F 5 (numeral (Nat.pair 0 (i + 1) + 1)) (mkPair b s) a := by
  have hbs := h.env_succ hs hb hns hdb
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
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
  rw [← numeral_add_one n] at hbs
  exact hc.bvar_succ _ ht.lt₁ _ (hn _ v₈).1 _ (hn _ v₉).1 _ hns.lt₁ _ hns.lt₂ _ ht.lt₃ _ hdb.lt₁
    (by simpa using isNode_numeral (M := M) 0 i)
    (by simpa [numeral_add_one] using isNode_numeral (M := M) 0 (i + 1)) (hn _ v₈).2 hbs hdb ht

lemma func (hs : W s) (hd : W d) (ha : W a) (hv : F 6 (numeral v) s d)
    (hf : F 8 (mkPair (numeral n) (numeral f)) d a) :
    F 5 (numeral (Nat.pair 2 (Nat.pair n (Nat.pair f v)) + 1)) s a := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [s, d, a, numeral v, numeral n, numeral f, mkPair (numeral n) (numeral f),
      numeral (Nat.pair f v), numeral (Nat.pair n (Nat.pair f v)),
      numeral (Nat.pair 2 (Nat.pair n (Nat.pair f v)) + 1)]
    (by simp [h.num, hs, hd, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, v₀, -⟩ := hl
  have hv := (hF 6 (by simp) _ _ _ v₄ v₁ v₂).mp hv
  have hf := (hF 8 (by simp) _ _ _ v₇ v₂ v₃).mp hf
  apply (hF 5 (by simp) _ _ _ v₀ v₁ v₃).mpr
  exact hc.func _ (hn _ v₀).1 _ (hn _ v₉).1 _ (hn _ v₅).1 _ (hn _ v₈).1 _ (hn _ v₆).1 _ hv.lt₁ _
    hv.lt₂ _ hv.lt₃ _ hf.lt₃ (isNode_numeral _ _) ((eval_pairDef_numeral_iff _ _).mpr rfl)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) (hn _ v₀).2 hv hf

lemma vec_cons {t : ℕ} (hs : W s) (ha : W a) (hd : W d) (ht : F 5 (numeral t) s a)
    (hv : F 6 (numeral v) s d) : F 6 (numeral (Nat.pair t v + 1)) s (mkPair a d) := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [s, a, d, numeral t, numeral v, numeral (Nat.pair t v + 1), mkPair a d]
    (by simp [h.num, hs, ha, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, -⟩ := hl
  have ht := (hF 5 (by simp) _ _ _ v₄ v₁ v₂).mp ht
  have hv := (hF 6 (by simp) _ _ _ v₅ v₁ v₃).mp hv
  exact (hF 6 (by simp) _ _ _ v₆ v₁ v₇).mpr <| hc.vec_cons _ (hn _ v₆).1 _ ht.lt₁ _ hv.lt₁ _
    ht.lt₂ _ ht.lt₃ _ hv.lt₃ (isNode_numeral _ _) (hn _ v₆).2 ht hv

lemma and (hs : W s) (hp : F 4 (numeral (Nat.pair 4 (Nat.pair q r) + 1)) s 0) :
    F 4 (numeral q) s 0 ∧ F 4 (numeral r) s 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral r, numeral (Nat.pair q r),
      numeral (Nat.pair 4 (Nat.pair q r) + 1)] (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₅ v₁ v₀).mp hp
  exact (hc.and _ hp.lt₁ _ (hn _ v₄).1 _ (hn _ v₂).1 _ (hn _ v₃).1 _ hp.lt₂ (isNode_numeral _ _)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) hp).imp (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mpr
    (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mpr

lemma or (hs : W s) (hp : F 4 (numeral (Nat.pair 5 (Nat.pair q r) + 1)) s 0) :
    F 4 (numeral q) s 0 ∨ F 4 (numeral r) s 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral r, numeral (Nat.pair q r),
      numeral (Nat.pair 5 (Nat.pair q r) + 1)] (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₅ v₁ v₀).mp hp
  exact (hc.or _ hp.lt₁ _ (hn _ v₄).1 _ (hn _ v₂).1 _ (hn _ v₃).1 _ hp.lt₂ (isNode_numeral _ _)
    ((eval_pairDef_numeral_iff _ _).mpr rfl) hp).imp (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mpr
    (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mpr

lemma all (hs : W s) (ha : W a) (hp : F 4 (numeral (Nat.pair 6 q + 1)) s 0) (hda : F 2 a 0 0) :
    F 4 (numeral q) (mkPair a s) 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, a, numeral q, numeral (Nat.pair 6 q + 1), mkPair a s]
    (by simp [h.zero, h.num, hs, ha, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₄ v₁ v₀).mp hp
  have hda := (hF 2 (by simp) _ _ _ v₂ v₀ v₀).mp hda
  exact (hF 4 (by simp) _ _ _ v₃ v₅ v₀).mpr <| hc.all _ hp.lt₁ _ (hn _ v₃).1 _ hp.lt₂ _ hda.lt₁
    (isNode_numeral _ _) hp hda

lemma exs (hs : W s) (hp : F 4 (numeral (Nat.pair 7 q + 1)) s 0) :
    ∃ a, W a ∧ F 2 a 0 0 ∧ F 4 (numeral q) (mkPair a s) 0 := by
  obtain ⟨c, j, V, hc, hl, hle, hVW, hVp, hn, hF⟩ := h.approx
    [0, s, numeral q, numeral (Nat.pair 7 q + 1), mkPair (mkPair 0 (numeral q)) s,
      mkPair (mkPair (mkPair 0 (numeral q)) s) s] (by simp [h.zero, h.num, hs, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₃ v₁ v₀).mp hp
  obtain ⟨a, -, ha, hda, hqa⟩ :=
    hc.exs _ hp.lt₁ _ (hn _ v₂).1 _ hp.lt₂ (isNode_numeral _ _) hp
  have va : V a := hle _ _ v₄ ha
  exact ⟨a, hVW a va, (hF 2 (by simp) _ _ _ va v₀ v₀).mpr hda,
    (hF 4 (by simp) _ _ _ v₂ (hVp _ _ _ (hVW _ v₄) hs v₅ ha) v₀).mpr hqa⟩

lemma falsum (hs : W s) (hp : F 4 (numeral (Nat.pair 3 0 + 1)) s 0) : False := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx [0, s, numeral (Nat.pair 3 0 + 1)]
    (by simp [h.zero, h.num, hs])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₂ v₁ v₀).mp hp
  exact hc.falsum _ hp.lt₁ _ hp.lt₂ (by simpa using isNode_numeral (M := M) 3 0) hp

lemma rel (hs : W s) (hd : W d)
    (hp : F 4 (numeral (Nat.pair 0 (Nat.pair n (Nat.pair R v)) + 1)) s 0)
    (hv : F 6 (numeral v) s d) : F 7 (mkPair (numeral n) (numeral R)) d 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, d, numeral v, numeral n, numeral R, mkPair (numeral n) (numeral R),
      numeral (Nat.pair R v), numeral (Nat.pair n (Nat.pair R v)),
      numeral (Nat.pair 0 (Nat.pair n (Nat.pair R v)) + 1)]
    (by simp [h.zero, h.num, hs, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₉ v₁ v₀).mp hp
  have hv := (hF 6 (by simp) _ _ _ v₃ v₁ v₂).mp hv
  exact (hF 7 (by simp) _ _ _ v₆ v₂ v₀).mpr <| hc.rel _ hp.lt₁ _ (hn _ v₈).1 _ (hn _ v₄).1 _
    (hn _ v₇).1 _ (hn _ v₅).1 _ hv.lt₁ _ hp.lt₂ _ hv.lt₃
    (by simpa using isNode_numeral (M := M) 0 (Nat.pair n (Nat.pair R v)))
    ((eval_pairDef_numeral_iff _ _).mpr rfl) ((eval_pairDef_numeral_iff _ _).mpr rfl) hp hv

lemma nrel (hs : W s) (hd : W d)
    (hp : F 4 (numeral (Nat.pair 1 (Nat.pair n (Nat.pair R v)) + 1)) s 0)
    (hv : F 6 (numeral v) s d) : ¬F 7 (mkPair (numeral n) (numeral R)) d 0 := by
  obtain ⟨c, j, V, hc, hl, -, -, -, hn, hF⟩ := h.approx
    [0, s, d, numeral v, numeral n, numeral R, mkPair (numeral n) (numeral R),
      numeral (Nat.pair R v), numeral (Nat.pair n (Nat.pair R v)),
      numeral (Nat.pair 1 (Nat.pair n (Nat.pair R v)) + 1)]
    (by simp [h.zero, h.num, hs, hd, h.pair])
  simp only [List.forall_mem_cons] at hl
  obtain ⟨v₀, v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, v₉, -⟩ := hl
  have hp := (hF 4 (by simp) _ _ _ v₉ v₁ v₀).mp hp
  have hv := (hF 6 (by simp) _ _ _ v₃ v₁ v₂).mp hv
  exact (hF 7 (by simp) _ _ _ v₆ v₂ v₀).not.mpr <| hc.nrel _ hp.lt₁ _ (hn _ v₈).1 _ (hn _ v₄).1 _
    (hn _ v₇).1 _ (hn _ v₅).1 _ hv.lt₁ _ hp.lt₂ _ hv.lt₃
    (by simpa using isNode_numeral (M := M) 1 (Nat.pair n (Nat.pair R v)))
    ((eval_pairDef_numeral_iff _ _).mpr rfl) ((eval_pairDef_numeral_iff _ _).mpr rfl) hp hv

end IsApproximable

end clauses

end FFL.FirstOrder.Arithmetic.R0

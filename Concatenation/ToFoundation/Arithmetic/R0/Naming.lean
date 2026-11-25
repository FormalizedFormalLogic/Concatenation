module

public import Concatenation.ToFoundation.Arithmetic.R0.Certificate

/-!
# Certificates of finite models exist

The elements of a finite model are named by the numbers, and its certificates code it through these
names.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.R0

open Encodable

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
lemma IsEnv.cons (ha : IsCanonical val a) (hs : IsEnv val n s) : IsEnv val (n + 1) (mkPair a s) := by
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

variable [L.Eq] [Tarski.Structure.Eq L S] [Finite S]

lemma exists_isCertificate (A : ArithmeticSemisentence 2) (j : ℕ)
    (hA : ∀ p ≤ j, ∀ w ≤ j, ℕ ⊧/![p, w] A → ∃ σ : Sentence L, encode σ = p ∧ S↓[L] ⊧ σ) :
    ∃ c : ℕ, IsCertificate A (encode (Language.Eq.eq : L.Rel 2)) c j := by
  obtain ⟨val, hval⟩ := exists_isNaming L S
  obtain ⟨D, hD⟩ := exists_isCanonical_le val
  obtain ⟨C, hC⟩ := exists_isEnv_le val (j + 3)
  let E : ℕ := encode (Language.Eq.eq : L.Rel 2)
  let B : ℕ := D + C + (j + 4) + mkPair j j + mkPair 2 E
  have hjB : j + 4 ≤ B := by omega
  have hDB {a : ℕ} (h : IsCanonical val a) : a ≤ B := by have := hD a h; omega
  have hCB {n s : ℕ} (hn : n ≤ j + 3) (h : IsEnv val n s) : s ≤ B := by
    have := hC n hn s h
    omega
  have hpB {a b : ℕ} (ha : a ≤ j) (hb : b ≤ j) : mkPair a b ≤ B := by
    have := mkPair_le_mkPair ha hb
    omega
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ e : ℕ, e ∈ c ↔ ∃ k x y z, x ≤ B ∧ y ≤ B ∧ z ≤ B ∧
      ModelFact L val j B k x y z ∧ e = mkPair k (mkPair x (mkPair y z)) := by
    apply exists_forall_mem_iff (s := {e | ∃ k x y z, x ≤ B ∧ y ≤ B ∧ z ≤ B ∧
      ModelFact L val j B k x y z ∧ e = mkPair k (mkPair x (mkPair y z))})
    have : (Set.Iic 9 ×ˢ Set.Iic B ×ˢ Set.Iic B ×ˢ Set.Iic B : Set (ℕ × ℕ × ℕ × ℕ)).Finite :=
      (Set.finite_Iic _).prod <| (Set.finite_Iic _).prod <| (Set.finite_Iic _).prod <|
        Set.finite_Iic _
    apply (this.image fun x ↦ mkPair x.1 (mkPair x.2.1 (mkPair x.2.2.1 x.2.2.2))).subset
    rintro e ⟨k, x, y, z, hx, hy, hz, h, rfl⟩
    refine ⟨(k, x, y, z), ⟨?_, hx, hy, hz⟩, rfl⟩
    by_contra hk
    obtain ⟨k, rfl⟩ : ∃ l, k = l + 10 := ⟨k - 10, by simp at hk; omega⟩
    exact h
  have hBc : B < c := by
    apply (left_lt_mkPair B (mkPair 0 0)).trans
    apply (right_lt_mkPair 9 _).trans
    exact lt_of_mem <| (hc _).mpr ⟨9, B, 0, 0, le_rfl, by simp, by simp, rfl, rfl⟩
  have hnum (n : ℕ) : (ORingStructure.numeral n : ℕ) = n := by simp
  have fact {k x y z : ℕ} : Fact c (ORingStructure.numeral k) x y z ↔
      x ≤ B ∧ y ≤ B ∧ z ≤ B ∧ ModelFact L val j B k x y z := by
    rw [hnum, nat_fact_iff, hc]
    constructor
    · rintro ⟨-, -, -, _, _, _, _, hx, hy, hz, h, e⟩
      simp only [mkPair_inj] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact ⟨hx, hy, hz, h⟩
    · rintro ⟨hx, hy, hz, h⟩
      exact ⟨by omega, by omega, by omega, _, _, _, _, hx, hy, hz, h, rfl⟩
  have dom {a : ℕ} (h : IsCanonical val a) : Fact c (ORingStructure.numeral 2) a 0 0 :=
    fact.mpr ⟨hDB h, Nat.zero_le _, Nat.zero_le _, h, rfl, rfl⟩
  have env {n s : ℕ} (hn : n ≤ j + 3) (h : IsEnv val n s) :
      Fact c (ORingStructure.numeral 3) n s 0 :=
    fact.mpr ⟨by omega, hCB hn h, Nat.zero_le _, hn, h, rfl⟩
  have sat {n : ℕ} {φ : Semisentence L n} {v : Fin n → ℕ} (h : encode φ + n ≤ j)
      (hv : ∀ i, IsCanonical val (v i)) (hφ : S ⊧/(val ∘ v) φ) :
      Fact c (ORingStructure.numeral 4) (encode φ) (envCode v) 0 :=
    fact.mpr ⟨by omega, hCB (n := n) (by omega) ⟨v, hv, rfl⟩, Nat.zero_le _, n, φ, v, h, rfl, hv,
      rfl, hφ, rfl⟩
  have le_pair {k q r : ℕ} : q ≤ Nat.pair k (Nat.pair q r) ∧ r ≤ Nat.pair k (Nat.pair q r) :=
    ⟨(Nat.left_le_pair _ _).trans <| Nat.right_le_pair _ _,
      (Nat.right_le_pair _ _).trans <| Nat.right_le_pair _ _⟩
  have comp {n a : ℕ} {v : Fin n → ℕ} : val ∘ (a :> v) = val a :> val ∘ v :=
    funext fun i ↦ by cases i using Fin.cases <;> rfl
  use c
  constructor
  · constructor
    · exact dom .zero
    · exact env (n := 0) (by simp) ⟨![], by simp, rfl⟩
    · intro n _ s _ a _ hn hs ha
      have hn := nat_cobhamLE_iff.mp hn
      exact env (by omega) <| (fact.mp hs).2.2.2.2.1.cons (fact.mp ha).2.2.2.1
    · intro k _ f _ d _ hk hf hd
      obtain ⟨a, ha, hac, hae⟩ := exists_isCanonical val (funcName k f d)
      exact ⟨a, (hDB hac).trans_lt hBc, nat_cobhamLE_iff.mpr ha, dom hac, fact.mpr
        ⟨hpB (nat_cobhamLE_iff.mp hk) (nat_cobhamLE_iff.mp hf), (fact.mp hd).2.1, hDB hac, hac, hae⟩⟩
    · intro x _ d _ a _ b _ ha hb
      obtain ⟨-, -, -, ha, ha'⟩ := fact.mp ha
      obtain ⟨-, -, -, hb, hb'⟩ := fact.mp hb
      exact ha.eq hb <| ha'.trans hb'.symm
    · intro a _ b _ ha hb
      have ha := (fact.mp ha).2.2.2.1
      have hb := (fact.mp hb).2.2.2.1
      have hv : mkPair a (mkPair b 0) = envCode ![a, b] := by simp
      constructor
      · intro h
        obtain ⟨-, -, -, k, R, v, hR, hd, h, -⟩ := fact.mp h
        obtain ⟨hk, hR⟩ := mkPair_inj.mp hR
        obtain rfl : 2 = k := (hnum 2).symm.trans hk
        obtain rfl : Language.Eq.eq = R := encode_injective <| (hnum E).symm.trans hR
        obtain rfl : ![a, b] = v := envCode_injective <| hv.symm.trans hd
        exact ha.eq hb <| by simpa using h
      · rintro rfl
        refine fact.mpr ⟨?_, ?_, Nat.zero_le _, 2, Language.Eq.eq, ![a, a], ?_, hv, ?_, rfl⟩
        · rw [hnum, hnum]
          exact Nat.le_add_left _ _
        · exact hCB (n := 2) (by omega) ⟨![a, a], by simp [Fin.forall_fin_two, ha], hv⟩
        · rw [hnum, hnum]
        · simp
    · intro p _ w _ hp hw h
      obtain ⟨σ, rfl, hσ⟩ := hA p (nat_cobhamLE_iff.mp hp) w (nat_cobhamLE_iff.mp hw) h
      exact sat (n := 0) (v := ![]) (nat_cobhamLE_iff.mp hp) (by simp)
        (by simpa [models_iff, Matrix.empty_eq] using hσ)
  · constructor
    · intro t _ n _ s _ a _ ht htj hs ha has
      obtain ⟨-, -, -, ha, -⟩ := fact.mp ha
      obtain ⟨-, hB, -, hn, has, -⟩ := fact.mp has
      refine fact.mpr ⟨?_, hB, hDB ha, nat_cobhamLE_iff.mp htj, ⟨_, hn, has⟩, ha, ?_⟩
      · have := nat_cobhamLE_iff.mp htj
        omega
      · rintro n' t' v' rfl hv
        obtain ⟨x, rfl, hx⟩ := exists_eq_bvar <| nat_isNode_iff.mp ht
        match n' with
        | 0 => exact x.elim0
        | n' + 1 =>
          obtain rfl : x = 0 := Fin.ext hx
          simp [(mkPair_inj.mp hv).1]
    · intro t _ u _ i _ n _ s _ a _ b _ ht hu huj hbs hb ha
      obtain ⟨-, hB, -, hn, hbs, -⟩ := fact.mp hbs
      obtain ⟨-, -, -, -, -, hac, ha⟩ := fact.mp ha
      refine fact.mpr ⟨?_, hB, hDB hac, nat_cobhamLE_iff.mp huj, ⟨_, hn, hbs⟩, hac, ?_⟩
      · have := nat_cobhamLE_iff.mp huj
        omega
      · rintro n' t' v' rfl hv
        obtain ⟨x, rfl, hx⟩ := exists_eq_bvar <| nat_isNode_iff.mp hu
        match n' with
        | 0 => exact x.elim0
        | n' + 1 =>
          obtain ⟨y, rfl⟩ : ∃ y : Fin n', x = y.succ :=
            ⟨⟨i, by have := x.isLt; omega⟩, Fin.ext hx⟩
          rw [ha n' #y (fun i ↦ v' i.succ) _ (mkPair_inj.mp hv).2]
          · simp
          · rw [nat_isNode_iff.mp ht, Semiterm.encode_eq_toNat, Semiterm.toNat,
              ← Nat.succ.inj hx]
    · intro t _ x _ k _ y _ f _ v _ s _ d _ a _ ht hx hy htj hd ha
      obtain rfl := nat_eval_pairDef.mp hx
      obtain rfl := nat_eval_pairDef.mp hy
      obtain ⟨-, hB, -, -, hs, -, hd⟩ := fact.mp hd
      obtain ⟨-, -, -, hac, ha⟩ := fact.mp ha
      refine fact.mpr ⟨?_, hB, hDB hac, nat_cobhamLE_iff.mp htj, hs, hac, ?_⟩
      · have := nat_cobhamLE_iff.mp htj
        omega
      · rintro n' t' v' rfl hv
        obtain ⟨F, u, rfl, rfl, hu⟩ := exists_eq_func <| nat_isNode_iff.mp ht
        obtain ⟨w, rfl, hw⟩ := hd n' k u v' hu.symm hv
        rw [ha]
        exact (hval.func F w).trans <| congrArg _ <| funext hw
    · intro n _ s _ hs
      obtain ⟨-, hB, -, hn, hs, -⟩ := fact.mp hs
      refine fact.mpr ⟨Nat.zero_le _, hB, Nat.zero_le _, Nat.zero_le _, ⟨n, hn, hs⟩,
        ⟨0, le_rfl, ![], by simp, rfl⟩, ?_⟩
      intro n' k t v h _
      match k with
      | 0 => exact ⟨![], rfl, by simp⟩
      | k + 1 => simp [Matrix.vecToNat, Matrix.foldr] at h
    · intro w _ t _ v _ s _ a _ d _ hw hwj ha hd
      obtain rfl := nat_isNode_iff.mp hw
      have hwj := nat_cobhamLE_iff.mp hwj
      obtain ⟨-, hB, -, -, hs, hac, ha⟩ := fact.mp ha
      obtain ⟨-, -, -, -, -, ⟨k, hk, hdk⟩, hd⟩ := fact.mp hd
      have hk' := hk.trans <| Nat.right_le_pair t v
      refine fact.mpr ⟨by omega, hB, hCB (n := k + 1) (by omega) <| hdk.cons hac, hwj, hs,
        ⟨k + 1, by omega, hdk.cons hac⟩, ?_⟩
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
  · constructor
    · intro p _ x _ q _ r _ s _ hp hx h
      obtain rfl := nat_eval_pairDef.mp hx
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      have hp := nat_isNode_iff.mp hp
      obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := exists_eq_and hp
      have := le_pair (k := ORingStructure.numeral 4) (q := encode φ₁) (r := encode φ₂)
      have hφ : S ⊧/(val ∘ v) φ₁ ∧ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
      exact ⟨sat (by omega) hv hφ.1, sat (by omega) hv hφ.2⟩
    · intro p _ x _ q _ r _ s _ hp hx h
      obtain rfl := nat_eval_pairDef.mp hx
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      have hp := nat_isNode_iff.mp hp
      obtain ⟨φ₁, φ₂, rfl, rfl, rfl⟩ := exists_eq_or hp
      have := le_pair (k := ORingStructure.numeral 5) (q := encode φ₁) (r := encode φ₂)
      have hφ : S ⊧/(val ∘ v) φ₁ ∨ S ⊧/(val ∘ v) φ₂ := by simpa using hφ
      exact hφ.imp (sat (by omega) hv) (sat (by omega) hv)
    · intro p _ q _ s _ a _ hp h ha
      obtain ⟨-, -, -, ha, -⟩ := fact.mp ha
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      have hp := nat_isNode_iff.mp hp
      obtain ⟨φ, rfl, rfl⟩ := exists_eq_all hp
      have := Nat.right_le_pair (ORingStructure.numeral 6) (encode φ)
      have hφ : ∀ x, S ⊧/(x :> val ∘ v) φ := by simpa using hφ
      rw [← envCode_cons]
      apply sat (by omega)
      · simpa [Fin.forall_fin_succ] using ⟨ha, hv⟩
      · simpa [comp] using hφ (val a)
    · intro p _ q _ s _ hp h
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      have hp := nat_isNode_iff.mp hp
      obtain ⟨φ, rfl, rfl⟩ := exists_eq_exs hp
      have := Nat.right_le_pair (ORingStructure.numeral 7) (encode φ)
      have hφ := hval.witness φ v <| by simpa using hφ
      obtain ⟨a, ha, hac, hae⟩ := exists_isCanonical val (witnessName (encode φ) (envCode v))
      refine ⟨a, (hDB hac).trans_lt hBc, nat_cobhamLE_iff.mpr ha, dom hac, ?_⟩
      rw [← envCode_cons]
      apply sat (by omega)
      · simpa [Fin.forall_fin_succ] using ⟨hac, hv⟩
      · simpa [comp, hae] using hφ
    · intro p _ s _ hp h
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      obtain rfl := eq_falsum <| nat_isNode_iff.mp hp
      simp at hφ
    · intro p _ x _ k _ y _ R _ v _ s _ d _ hp hx hy h hd
      obtain rfl := nat_eval_pairDef.mp hx
      obtain rfl := nat_eval_pairDef.mp hy
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      have hp := nat_isNode_iff.mp hp
      obtain ⟨R, t, rfl, rfl, rfl⟩ := exists_eq_rel hp
      obtain ⟨-, -, hdB, -, -, -, hd⟩ := fact.mp hd
      obtain ⟨u, rfl, hu⟩ := hd n k t v rfl rfl
      have := (Nat.left_le_pair k (Nat.pair (encode R) (Matrix.vecToNat fun i ↦ encode (t i)))).trans
        <| Nat.right_le_pair 0 _
      have := (le_pair (k := k) (q := encode R)
        (r := Matrix.vecToNat fun i ↦ encode (t i))).1.trans <| Nat.right_le_pair 0 _
      refine fact.mpr ⟨hpB (by omega) (by omega), hdB, Nat.zero_le _, k, R, u, rfl, rfl, ?_, rfl⟩
      simpa [Semiformula.eval_rel, Function.comp_def, hu] using hφ
    · intro p _ x _ k _ y _ R _ v _ s _ d _ hp hx hy h hd h'
      obtain rfl := nat_eval_pairDef.mp hx
      obtain rfl := nat_eval_pairDef.mp hy
      obtain ⟨-, -, -, n, φ, v, hj, rfl, hv, rfl, hφ, -⟩ := fact.mp h
      obtain ⟨R, t, rfl, rfl, rfl⟩ := exists_eq_nrel <| nat_isNode_iff.mp hp
      obtain ⟨-, -, -, -, -, -, hd⟩ := fact.mp hd
      obtain ⟨u, rfl, hu⟩ := hd n k t v rfl rfl
      obtain ⟨-, -, -, k', R', u', hR, hu', h', -⟩ := fact.mp h'
      obtain ⟨rfl, hR⟩ := mkPair_inj.mp hR
      obtain rfl := encode_injective hR
      obtain rfl := envCode_injective hu'
      have hφ : ¬Tarski.Structure.rel R (val ∘ u) := by
        simpa [Semiformula.eval_nrel, Function.comp_def, hu] using hφ
      exact hφ h'

end model

end FFL.FirstOrder.Arithmetic.R0

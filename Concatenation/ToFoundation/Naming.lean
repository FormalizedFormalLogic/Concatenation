module

public import Concatenation.ToFoundation.Arithmetic.Pairing
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Naming the elements of a structure by numbers

The elements of a structure are named by numbers, so that the names of the witnesses of
existential formulas and of the values of functions are given by codes.
-/

@[expose] public section

namespace FFL.FirstOrder.Tarski.Structure

open Encodable Arithmetic

/-- The name of the witness of the existential formula with the kernel of code `p`. -/
def witnessName (p s : ℕ) : ℕ := mkPair (mkPair 0 p) s

/-- The name of the value of the function symbol of code `f` and arity `k`. -/
def funcName (k f d : ℕ) : ℕ := mkPair (mkPair 1 (mkPair k f)) d

variable {L : Language} [L.Encodable] {V : Type*} [Tarski.Structure L V]

/--
`val` names the elements of `V` by the numbers: it maps the names of witnesses to witnesses and
the names of values to values.
-/
structure IsNaming (L : Language) [L.Encodable] {V : Type*} [Nonempty V] [Tarski.Structure L V]
    (val : ℕ → V) : Prop where
  witness : ∀ {n} (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
    (∃ a, V ⊧/(a :> val ∘ v) φ) → V ⊧/(val (witnessName (encode φ) (envCode v)) :> val ∘ v) φ
  func : ∀ {k} (f : L.Func k) (v : Fin k → ℕ),
    val (funcName k (encode f) (envCode v)) = Tarski.Structure.func f (val ∘ v)

variable (L V) [Nonempty V] in
lemma exists_isNaming : ∃ val : ℕ → V, IsNaming L val := by
  have (e : ℕ) (u : ℕ → V) : ∃ b : V,
      (∀ n (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
        e = witnessName (encode φ) (envCode v) → (∃ a, V ⊧/(a :> u ∘ v) φ) →
          V ⊧/(b :> u ∘ v) φ) ∧
      ∀ k (f : L.Func k) (v : Fin k → ℕ), e = funcName k (encode f) (envCode v) →
        b = Tarski.Structure.func f (u ∘ v) := by
    by_cases h₁ : ∃ n, ∃ (φ : Semisentence L (n + 1)) (v : Fin n → ℕ),
        e = witnessName (encode φ) (envCode v)
    · obtain ⟨n, φ, v, rfl⟩ := h₁
      have h (b : V) (hb : (∃ a, V ⊧/(a :> u ∘ v) φ) → V ⊧/(b :> u ∘ v) φ) : ∃ b : V,
          (∀ n' (φ' : Semisentence L (n' + 1)) (v' : Fin n' → ℕ),
            witnessName (encode φ) (envCode v) = witnessName (encode φ') (envCode v') →
              (∃ a, V ⊧/(a :> u ∘ v') φ') → V ⊧/(b :> u ∘ v') φ') ∧
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
          simp [witnessName, funcName] at h
      by_cases hb : ∃ a, V ⊧/(a :> u ∘ v) φ
      · obtain ⟨b, hb⟩ := hb
        exact h b fun _ ↦ hb
      · exact h (Classical.arbitrary V) fun h ↦ absurd h hb
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
      · use Classical.arbitrary V
        exact ⟨fun n φ v h ↦ absurd ⟨n, φ, v, h⟩ h₁, fun k f v h ↦ absurd ⟨k, f, v, h⟩ h₂⟩
  choose g hg₁ hg₂ using this
  obtain ⟨val, hval⟩ : ∃ val : ℕ → V, ∀ e, ∃ u : ℕ → V, (∀ i < e, u i = val i) ∧ val e = g e u := by
    classical
    let val : ℕ → V := Nat.lt_wfRel.wf.fix fun e ih ↦
      g e fun i ↦ if h : i < e then ih i h else Classical.arbitrary V
    use val
    intro e
    use fun i ↦ if i < e then val i else Classical.arbitrary V
    constructor
    · intro i hi
      simp [hi]
    · exact Nat.lt_wfRel.wf.fix_eq _ e
  have comp {n e : ℕ} {u : ℕ → V} (hu : ∀ i < e, u i = val i) (v : Fin n → ℕ)
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
def IsCanonical (val : ℕ → V) (a : ℕ) : Prop := ∀ b < a, val b ≠ val a

/-- `s` codes an environment of `n` least names. -/
def IsEnv (val : ℕ → V) (n s : ℕ) : Prop :=
  ∃ v : Fin n → ℕ, (∀ i, IsCanonical val (v i)) ∧ s = envCode v

variable {val : ℕ → V} {a b n s : ℕ}

@[grind .]
lemma IsCanonical.zero : IsCanonical val 0 := by
  simp [IsCanonical]

lemma IsCanonical.eq (ha : IsCanonical val a) (hb : IsCanonical val b) (h : val a = val b) :
    a = b := by
  grind [IsCanonical]

variable (val) in
lemma exists_isCanonical (a : ℕ) : ∃ b ≤ a, IsCanonical val b ∧ val b = val a := by
  classical
  have h : ∃ b, val b = val a := ⟨a, rfl⟩
  exact ⟨Nat.find h, Nat.find_min' h rfl,
    fun b hb H ↦ Nat.find_min h hb (H.trans <| Nat.find_spec h), Nat.find_spec h⟩

variable (val) in
lemma exists_isCanonical_le [Finite V] : ∃ D, ∀ a, IsCanonical val a → a ≤ D := by
  have : {a | IsCanonical val a}.Finite :=
    Set.Finite.of_finite_image (Set.toFinite (val '' _)) fun a ha b hb ↦ IsCanonical.eq ha hb
  obtain ⟨D, hD⟩ := this.bddAbove
  exact ⟨D, fun a ha ↦ hD ha⟩

lemma IsEnv.cons (ha : IsCanonical val a) (hs : IsEnv val n s) :
    IsEnv val (n + 1) (mkPair a s) := by
  obtain ⟨v, hv, rfl⟩ := hs
  use a :> v
  simpa [Fin.forall_fin_succ] using ⟨ha, hv⟩

variable (val) in
lemma exists_isEnv_le [Finite V] (N : ℕ) : ∃ B, ∀ n ≤ N, ∀ s, IsEnv val n s → s ≤ B := by
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
end FFL.FirstOrder.Tarski.Structure

module

public import Concatenation.TC.Empty
public import Concatenation.TC.Interpretability
public import Concatenation.ToFoundation.Coding
public import Concatenation.ToMathlib.AtomicPairing
public import Concatenation.WTC.Basic
public import Concatenation.WTC.Empty
public import Concatenation.WTC.Standard

/-!
# $\mathsf{WTC}$ with the editor axiom

Every finite part of $\mathsf{WTC}$ with the unrestricted editor axiom holds in a structure of
strings and formal pairs, whose theory is decidable. Hence neither it nor its extension with the
empty string interprets $\mathsf{TC}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section atomicPairing

open AtomicPairing

variable {S : Type*} {tbl : S → S → S → Prop} {M M' : Type*} [ConcatenationStructure M]
  [ConcatenationStructure M'] (F : AtomicPairing tbl M) (F' : AtomicPairing tbl M')
  (h₀ : ∃ s, (0 : M) = F.atom s ∧ (0 : M') = F'.atom s)
  (h₁ : ∃ s, (1 : M) = F.atom s ∧ (1 : M') = F'.atom s) {n : ℕ}

include h₀ h₁

lemma exists_similar_val (t : ClosedSemiterm ℒ⌢ n) :
    ∃ k, ∀ (d : ℕ) (ρ : Set (M × M')), ρ.Finite → F.Similar F' (d + k) ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) →
        ∃ ρ', ρ ⊆ ρ' ∧ ρ'.Finite ∧ F.Similar F' d ρ' ∧ (t.valb v, t.valb w) ∈ ρ' := by
  have atom {c : M} {c' : M'} (hc : ∃ s, c = F.atom s ∧ c' = F'.atom s) (d : ℕ)
      (ρ : Set (M × M')) (hρ : ρ.Finite) (h : F.Similar F' (d + 0) ρ) :
      ∃ ρ', ρ ⊆ ρ' ∧ ρ'.Finite ∧ F.Similar F' d ρ' ∧ (c, c') ∈ ρ' := by
    obtain ⟨s, rfl, rfl⟩ := hc
    use insert (F.atom s, F'.atom s) ρ
    exact ⟨Set.subset_insert _ _, hρ.insert _, h.insert_atom s, Set.mem_insert _ _⟩
  induction t with
  | bvar x => exact ⟨0, fun d ρ hρ h v w hvw ↦ ⟨ρ, subset_rfl, hρ, h, hvw x⟩⟩
  | fvar x => exact x.elim
  | func f t ih =>
    cases f with
    | zero => exact ⟨0, fun d ρ hρ h _ _ _ ↦ atom h₀ d ρ hρ h⟩
    | one => exact ⟨0, fun d ρ hρ h _ _ _ ↦ atom h₁ d ρ hρ h⟩
    | concat =>
      obtain ⟨k₁, hk₁⟩ := ih 0
      obtain ⟨k₂, hk₂⟩ := ih 1
      use k₁ + k₂ + 1
      intro d ρ hρ h v w hvw
      obtain ⟨ρ₁, hρρ₁, hρ₁, h', hm₁⟩ :=
        hk₁ (d + 1 + k₂) ρ hρ (h.mono (by omega) subset_rfl) v w hvw
      obtain ⟨ρ₂, hρ₁ρ₂, hρ₂, h'', hm₂⟩ := hk₂ (d + 1) ρ₁ hρ₁ h' v w fun i ↦ hρρ₁ (hvw i)
      use insert ((t 0).valb v ++ (t 1).valb v, (t 0).valb w ++ (t 1).valb w) ρ₂
      exact ⟨(hρρ₁.trans hρ₁ρ₂).trans (Set.subset_insert _ _), hρ₂.insert _,
        h''.insert_append (hρ₁ρ₂ hm₁) hm₂, Set.mem_insert _ _⟩

lemma exists_similar_val_eq (t₁ t₂ : ClosedSemiterm ℒ⌢ n) :
    ∃ k, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' k ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) →
        (t₁.valb v = t₂.valb v ↔ t₁.valb w = t₂.valb w) := by
  obtain ⟨k₁, hk₁⟩ := exists_similar_val F F' h₀ h₁ t₁
  obtain ⟨k₂, hk₂⟩ := exists_similar_val F F' h₀ h₁ t₂
  use 0 + k₂ + k₁
  intro ρ hρ h v w hvw
  obtain ⟨ρ₁, hρρ₁, hρ₁, h', hm₁⟩ := hk₁ (0 + k₂) ρ hρ h v w hvw
  obtain ⟨ρ₂, hρ₁ρ₂, -, h'', hm₂⟩ := hk₂ 0 ρ₁ hρ₁ h' v w fun i ↦ hρρ₁ (hvw i)
  exact h''.eq_iff (hρ₁ρ₂ hm₁) hm₂

lemma exists_similar_eval (φ : Semisentence ℒ⌢ n) :
    ∃ k, ∀ ρ : Set (M × M'), ρ.Finite → F.Similar F' k ρ →
      ∀ (v : Fin n → M) (w : Fin n → M'), (∀ i, (v i, w i) ∈ ρ) → (M ⊧/v φ ↔ M' ⊧/w φ) := by
  have hc {n : ℕ} {v : Fin n → M} {w : Fin n → M'} {ρ : Set (M × M')} (hvw : ∀ i, (v i, w i) ∈ ρ)
      (a : M) (b : M') (i) : ((a :> v) i, (b :> w) i) ∈ insert (a, b) ρ := by
    cases i using Fin.cases with
    | zero => exact Set.mem_insert _ _
    | succ i => exact Set.mem_insert_of_mem _ (hvw i)
  induction φ using Semiformula.rec' with
  | hverum => exact ⟨0, fun _ _ _ _ _ _ ↦ by simp⟩
  | hfalsum => exact ⟨0, fun _ _ _ _ _ _ ↦ by simp⟩
  | hrel r t =>
    cases r
    obtain ⟨k, hk⟩ := exists_similar_val_eq F F' h₀ h₁ (t 0) (t 1)
    exact ⟨k, fun ρ hρ h v w hvw ↦ hk ρ hρ h v w hvw⟩
  | hnrel r t =>
    cases r
    obtain ⟨k, hk⟩ := exists_similar_val_eq F F' h₀ h₁ (t 0) (t 1)
    exact ⟨k, fun ρ hρ h v w hvw ↦ not_congr (hk ρ hρ h v w hvw)⟩
  | hand φ ψ ihφ ihψ =>
    obtain ⟨k₁, hk₁⟩ := ihφ
    obtain ⟨k₂, hk₂⟩ := ihψ
    use max k₁ k₂
    intro ρ hρ h v w hvw
    simpa using and_congr (hk₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) v w hvw)
      (hk₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) v w hvw)
  | hor φ ψ ihφ ihψ =>
    obtain ⟨k₁, hk₁⟩ := ihφ
    obtain ⟨k₂, hk₂⟩ := ihψ
    use max k₁ k₂
    intro ρ hρ h v w hvw
    simpa using or_congr (hk₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) v w hvw)
      (hk₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) v w hvw)
  | hall φ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨g₁, hg₁⟩ := F.exists_similar_insert F' k
    obtain ⟨g₂, hg₂⟩ := F.exists_similar_insert' F' k
    use max g₁ g₂
    intro ρ hρ h v w hvw
    simp only [Semiformula.eval_all]
    constructor
    · intro ha b
      obtain ⟨a, hab⟩ := hg₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) b
      exact (hk _ (hρ.insert _) hab _ _ (hc hvw a b)).mp (ha a)
    · intro hb a
      obtain ⟨b, hab⟩ := hg₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) a
      exact (hk _ (hρ.insert _) hab _ _ (hc hvw a b)).mpr (hb b)
  | hexs φ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨g₁, hg₁⟩ := F.exists_similar_insert F' k
    obtain ⟨g₂, hg₂⟩ := F.exists_similar_insert' F' k
    use max g₁ g₂
    intro ρ hρ h v w hvw
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hab⟩ := hg₁ ρ hρ (h.mono (le_max_left _ _) subset_rfl) a
      exact ⟨b, (hk _ (hρ.insert _) hab _ _ (hc hvw a b)).mp ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, hab⟩ := hg₂ ρ hρ (h.mono (le_max_right _ _) subset_rfl) b
      exact ⟨a, (hk _ (hρ.insert _) hab _ _ (hc hvw a b)).mpr hb⟩

/--
Two atomic pairings with the same table of atoms, in which each of the two letters is the same
atom, satisfy the same sentences.
-/
lemma models_iff_of_atomicPairing (σ : Sentence ℒ⌢) : M↓[ℒ⌢] ⊧ σ ↔ M'↓[ℒ⌢] ⊧ σ := by
  obtain ⟨k, hk⟩ := exists_similar_eval F F' h₀ h₁ σ
  exact hk ∅ Set.finite_empty (similar_empty k) ![] ![] fun i ↦ i.elim0

end atomicPairing

/-- The nonempty binary strings of length at most `N + 1`, and all formal pairs built from them. -/
inductive PrePairing (N : ℕ) : Type
  | string (x : FreeSemigroup Bool) (hx : x.length ≤ N + 1) : PrePairing N
  | pair (a b : PrePairing N) : PrePairing N

namespace PrePairing

variable {N : ℕ} {a b c d : PrePairing N} {x y u : FreeSemigroup Bool}

instance : Nonempty (PrePairing N) := ⟨string 0 <| by simp [zero_eq_of_false]⟩

/--
Two strings are concatenated when the result is of length at most `N + 1`; every other product is
the formal pair.
-/
instance : ConcatenationStructure (PrePairing N) where
  zero := string 0 <| by simp [zero_eq_of_false]
  one := string 1 <| by simp [one_eq_of_true]
  append
    | string x hx, string y hy =>
      if h : (x * y).length ≤ N + 1 then string (x * y) h else pair (string x hx) (string y hy)
    | a, b => pair a b

lemma zero_eq : (0 : PrePairing N) = string 0 (by simp [zero_eq_of_false]) := rfl

lemma one_eq : (1 : PrePairing N) = string 1 (by simp [one_eq_of_true]) := rfl

lemma string_append_string (hx : x.length ≤ N + 1) (hy : y.length ≤ N + 1)
    (h : (x * y).length ≤ N + 1) : string x hx ++ string y hy = string (x * y) h :=
  dite_eq_left_of_eq_true <| eq_true h

/-- A product is a concatenation of strings or a formal pair. -/
lemma append_eq (a b : PrePairing N) :
    (∃ x y hx hy h, a = string x hx ∧ b = string y hy ∧ a ++ b = string (x * y) h) ∨
      a ++ b = pair a b := by
  rcases a with ⟨x, hx⟩ | ⟨a₁, a₂⟩
  · rcases b with ⟨y, hy⟩ | ⟨b₁, b₂⟩
    · by_cases h : (x * y).length ≤ N + 1
      · exact .inl ⟨x, y, hx, hy, h, rfl, rfl, dite_eq_left_of_eq_true <| eq_true h⟩
      · exact .inr <| dite_eq_right_of_eq_false <| eq_false h
    · exact .inr rfl
  · exact .inr rfl

lemma exists_of_append_eq (hu : u.length ≤ N + 1) (h : a ++ b = string u hu) :
    ∃ x y hx hy, a = string x hx ∧ b = string y hy ∧ x * y = u := by
  rcases append_eq a b with ⟨x, y, hx, hy, _, rfl, rfl, h'⟩ | h'
  · exact ⟨x, y, hx, hy, rfl, rfl, by simpa [h'] using h⟩
  · simp [h'] at h

lemma exists_of_isSubstring (hu : u.length ≤ N + 1) (h : IsSubstring a (string u hu)) :
    ∃ x hx, a = string x hx := by
  apply h.of_forall_append (P := fun a ↦ ∃ x hx, a = string x hx) _ ⟨u, hu, rfl⟩
  rintro a b ⟨u, hu, h⟩
  obtain ⟨x, y, hx, hy, rfl, rfl, -⟩ := exists_of_append_eq hu h
  exact ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

lemma append_assoc_of_eq_string (hu : u.length ≤ N + 1)
    (h : a ++ b ++ c = string u hu ∨ a ++ (b ++ c) = string u hu) :
    a ++ b ++ c = a ++ (b ++ c) := by
  rcases h with h | h
  · obtain ⟨w, z, hw, hz, h', rfl, rfl⟩ := exists_of_append_eq hu h
    obtain ⟨x, y, hx, hy, rfl, rfl, rfl⟩ := exists_of_append_eq hw h'
    have hl : (x * y * z).length = x.length + y.length + z.length := by
      simp [FreeSemigroup.length_mul]
    have hyz : (y * z).length ≤ N + 1 := by rw [FreeSemigroup.length_mul]; omega
    rw [h, string_append_string hy hz hyz,
      string_append_string hx hyz (by rw [← mul_assoc]; exact hu)]
    simp [mul_assoc]
  · obtain ⟨x, w, hx, hw, rfl, h', rfl⟩ := exists_of_append_eq hu h
    obtain ⟨y, z, hy, hz, rfl, rfl, rfl⟩ := exists_of_append_eq hw h'
    have hl : (x * (y * z)).length = x.length + y.length + z.length := by
      simp [FreeSemigroup.length_mul, add_assoc]
    have hxy : (x * y).length ≤ N + 1 := by rw [FreeSemigroup.length_mul]; omega
    rw [h, string_append_string hx hy hxy,
      string_append_string hxy hz (by rw [mul_assoc]; exact hu)]
    simp [mul_assoc]

lemma append_assoc_of_isSubstring (hu : u.length ≤ N + 1)
    (h : IsSubstring (a ++ b ++ c) (string u hu) ∨ IsSubstring (a ++ (b ++ c)) (string u hu)) :
    a ++ b ++ c = a ++ (b ++ c) := by
  rcases h with h | h <;> obtain ⟨v, hv, h⟩ := exists_of_isSubstring hu h
  exacts [append_assoc_of_eq_string hv <| .inl h, append_assoc_of_eq_string hv <| .inr h]

lemma editor (h : a ++ b = c ++ d) :
    (a = c ∧ b = d) ∨ ∃ w, (a ++ w = c ∧ b = w ++ d) ∨ (a = c ++ w ∧ w ++ b = d) := by
  rcases append_eq a b with ⟨x, y, hx, hy, hxy, rfl, rfl, hab⟩ | hab <;>
  rcases append_eq c d with ⟨z, w, hz, hw, hzw, rfl, rfl, hcd⟩ | hcd <;>
  rw [hab, hcd] at h
  · have hl : (x * y).length = x.length + y.length := FreeSemigroup.length_mul x y
    have hl' : (z * w).length = z.length + w.length := FreeSemigroup.length_mul z w
    rcases FreeSemigroup.mul_eq_mul_iff.mp (string.inj h) with ⟨rfl, rfl⟩ | ⟨t, h⟩
    · simp
    · right
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have ht : t.length ≤ N + 1 := by rw [FreeSemigroup.length_mul] at hy; omega
        use string t ht
        left
        rw [string_append_string hx ht hz, string_append_string ht hw hy]
        simp
      · have ht : t.length ≤ N + 1 := by rw [FreeSemigroup.length_mul] at hx; omega
        use string t ht
        right
        rw [string_append_string hz ht hx, string_append_string ht hy hw]
        simp
  · simp at h
  · simp at h
  · exact .inl <| by simpa using h

lemma append_ne_string (hu : u.length = 1) (hu' : u.length ≤ N + 1) : a ++ b ≠ string u hu' := by
  intro h
  obtain ⟨x, y, -, -, -, -, rfl⟩ := exists_of_append_eq hu' h
  rw [FreeSemigroup.length_mul] at hu
  have hx : 0 < x.length := Nat.succ_pos _
  have hy : 0 < y.length := Nat.succ_pos _
  omega

lemma zero_ne_one : (0 : PrePairing N) ≠ 1 := by
  simp [zero_eq, one_eq, zero_eq_of_false, one_eq_of_true, FreeSemigroup.of]

lemma ofFreeSemigroup_eq (hu : u.length ≤ N + 1) :
    (ConcatenationStructure.ofFreeSemigroup u : PrePairing N) = string u hu := by
  have hb (b : Bool) : (FreeSemigroup.of b).length ≤ N + 1 := by simp
  have h₀ (b : Bool) :
      (if b then 1 else 0 : PrePairing N) = string (FreeSemigroup.of b) (hb b) := by
    cases b <;> rfl
  have h (l : List Bool) (x : FreeSemigroup Bool) (hx : x.length ≤ N + 1)
      (hxl : (⟨x.head, x.tail ++ l⟩ : FreeSemigroup Bool).length ≤ N + 1) :
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (string x hx) =
        string ⟨x.head, x.tail ++ l⟩ hxl := by
    induction l generalizing x with
    | nil => simp
    | cons b l ih =>
      have hxb : (x * FreeSemigroup.of b).length ≤ N + 1 := by
        simp [FreeSemigroup.length] at hxl ⊢
        omega
      rw [List.foldl_cons, h₀, string_append_string hx _ hxb,
        ih _ hxb (by simpa [FreeSemigroup.of] using hxl)]
      congr 2
      simp [FreeSemigroup.of]
  rw [ConcatenationStructure.ofFreeSemigroup, stringValue, h₀,
    h _ _ (by simp) (by simpa [FreeSemigroup.of])]
  simp [FreeSemigroup.of]

/-- No formal pair inside is the pair of two strings whose concatenation is a string. -/
def Good : PrePairing N → Prop
  | string _ _ => True
  | pair a b => Good a ∧ Good b ∧ a ++ b = pair a b

lemma good_append (ha : a.Good) (hb : b.Good) : (a ++ b).Good := by
  rcases append_eq a b with ⟨x, y, hx, hy, h, rfl, rfl, h'⟩ | h' <;> rw [h']
  exacts [trivial, ⟨ha, hb, h'⟩]

lemma good_of_append (h : (a ++ b).Good) : a.Good ∧ b.Good := by
  rcases append_eq a b with ⟨x, y, hx, hy, _, rfl, rfl, _⟩ | h'
  · exact ⟨trivial, trivial⟩
  · rw [h'] at h
    exact ⟨h.1, h.2.1⟩

/-- The number of letters. -/
def size : PrePairing N → ℕ
  | string x _ => x.length
  | pair a b => a.size + b.size

lemma size_append (a b : PrePairing N) : (a ++ b).size = a.size + b.size := by
  rcases append_eq a b with ⟨x, y, hx, hy, h, rfl, rfl, h'⟩ | h' <;> rw [h']
  exacts [FreeSemigroup.length_mul x y, rfl]

lemma size_pos (a : PrePairing N) : 0 < a.size := by
  induction a with
  | string x hx => exact Nat.succ_pos _
  | pair a b iha ihb => exact Nat.add_pos_left iha _

end PrePairing

/--
The nonempty binary strings of length at most `N + 1`, and the formal pairs built from them other
than the pairs of two strings whose concatenation is of length at most `N + 1`.
-/
@[ext]
structure Pairing (N : ℕ) : Type where
  /-- The underlying string or formal pair. -/
  val : PrePairing N
  good : val.Good

namespace Pairing

variable {N : ℕ} {a b c d : Pairing N} {x y u : FreeSemigroup Bool}

/-- A string of length at most `N + 1`. -/
def string (x : FreeSemigroup Bool) (hx : x.length ≤ N + 1) : Pairing N := ⟨.string x hx, trivial⟩

instance : ConcatenationStructure (Pairing N) where
  zero := string 0 <| by simp [zero_eq_of_false]
  one := string 1 <| by simp [one_eq_of_true]
  append a b := ⟨a.1 ++ b.1, PrePairing.good_append a.2 b.2⟩

instance : Nonempty (Pairing N) := ⟨0⟩

lemma val_string (hx : x.length ≤ N + 1) : (string x hx : Pairing N).val = .string x hx := rfl

lemma zero_eq : (0 : Pairing N) = string 0 (by simp [zero_eq_of_false]) := rfl

lemma one_eq : (1 : Pairing N) = string 1 (by simp [one_eq_of_true]) := rfl

lemma string_injective {hx : x.length ≤ N + 1} {hy : y.length ≤ N + 1}
    (h : (string x hx : Pairing N) = string y hy) : x = y :=
  PrePairing.string.inj (congrArg Pairing.val h)

lemma string_append_string (hx : x.length ≤ N + 1) (hy : y.length ≤ N + 1)
    (h : (x * y).length ≤ N + 1) : string x hx ++ string y hy = string (x * y) h :=
  Pairing.ext <| PrePairing.string_append_string hx hy h

/-- A product is a concatenation of strings or a formal pair. -/
lemma append_eq (a b : Pairing N) :
    (∃ x y hx hy h, a = string x hx ∧ b = string y hy ∧ a ++ b = string (x * y) h) ∨
      (a ++ b).1 = .pair a.1 b.1 := by
  rcases PrePairing.append_eq a.1 b.1 with ⟨x, y, hx, hy, h, ha, hb, hab⟩ | h
  · exact .inl ⟨x, y, hx, hy, h, Pairing.ext ha, Pairing.ext hb, Pairing.ext hab⟩
  · exact .inr h

lemma exists_of_append_eq (hu : u.length ≤ N + 1) (h : a ++ b = string u hu) :
    ∃ x y hx hy, a = string x hx ∧ b = string y hy ∧ x * y = u := by
  obtain ⟨x, y, hx, hy, ha, hb, rfl⟩ := PrePairing.exists_of_append_eq hu (congrArg Pairing.val h)
  exact ⟨x, y, hx, hy, Pairing.ext ha, Pairing.ext hb, rfl⟩

lemma isSubstring_val (h : IsSubstring a b) : IsSubstring a.1 b.1 := h.map Pairing.val fun _ _ ↦ rfl

lemma append_assoc_of_isSubstring (hu : u.length ≤ N + 1)
    (h : IsSubstring (a ++ b ++ c) (string u hu) ∨ IsSubstring (a ++ (b ++ c)) (string u hu)) :
    a ++ b ++ c = a ++ (b ++ c) :=
  Pairing.ext <| PrePairing.append_assoc_of_isSubstring hu <| h.imp isSubstring_val isSubstring_val

lemma editor (h : a ++ b = c ++ d) :
    (a = c ∧ b = d) ∨ ∃ w, (a ++ w = c ∧ b = w ++ d) ∨ (a = c ++ w ∧ w ++ b = d) := by
  rcases PrePairing.editor (congrArg Pairing.val h) with ⟨h₁, h₂⟩ | ⟨w, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
  · exact .inl ⟨Pairing.ext h₁, Pairing.ext h₂⟩
  · have hw : w.Good := (PrePairing.good_of_append (h₁ ▸ c.2)).2
    exact .inr ⟨⟨w, hw⟩, .inl ⟨Pairing.ext h₁, Pairing.ext h₂⟩⟩
  · have hw : w.Good := (PrePairing.good_of_append (h₂ ▸ d.2)).1
    exact .inr ⟨⟨w, hw⟩, .inr ⟨Pairing.ext h₁, Pairing.ext h₂⟩⟩

lemma append_ne_string (hu : u.length = 1) (hu' : u.length ≤ N + 1) : a ++ b ≠ string u hu' :=
  fun h ↦ PrePairing.append_ne_string hu hu' (congrArg Pairing.val h)

lemma zero_ne_one : (0 : Pairing N) ≠ 1 := fun h ↦
  PrePairing.zero_ne_one (congrArg Pairing.val h)

lemma ofFreeSemigroup_eq (hu : u.length ≤ N + 1) :
    (ConcatenationStructure.ofFreeSemigroup u : Pairing N) = string u hu := by
  apply Pairing.ext
  rw [ConcatenationStructure.ofFreeSemigroup, map_stringValue Pairing.val fun _ _ ↦ rfl, val_string,
    ← PrePairing.ofFreeSemigroup_eq hu]
  congr
  funext b
  cases b <;> rfl

/-- The number of letters. -/
def size (a : Pairing N) : ℕ := a.1.size

lemma size_append (a b : Pairing N) : (a ++ b).size = a.size + b.size :=
  PrePairing.size_append a.1 b.1

lemma size_pos (a : Pairing N) : 0 < a.size := PrePairing.size_pos a.1

lemma exists_string_or_append (a : Pairing N) : (∃ x hx, a = string x hx) ∨ ∃ b c, a = b ++ c := by
  rcases a with ⟨⟨x, hx⟩ | ⟨b, c⟩, ha⟩
  · exact .inl ⟨x, hx, rfl⟩
  · exact .inr ⟨⟨b, ha.1⟩, ⟨c, ha.2.1⟩, Pairing.ext ha.2.2.symm⟩

lemma append_injective (h : ∀ x hx, a ++ b ≠ string x hx) (h' : a ++ b = c ++ d) :
    a = c ∧ b = d := by
  rcases append_eq a b with ⟨x, y, _, _, hxy, -, -, hab⟩ | hab
  · exact (h _ hxy hab).elim
  · rcases append_eq c d with ⟨x, y, _, _, hxy, -, -, hcd⟩ | hcd
    · exact (h _ hxy (h'.trans hcd)).elim
    · rw [h', hcd] at hab
      obtain ⟨h₁, h₂⟩ := PrePairing.pair.inj hab
      exact ⟨Pairing.ext h₁.symm, Pairing.ext h₂.symm⟩

lemma exists_ne_string : ∃ a : Pairing N, ∀ x hx, a ≠ string x hx := by
  have hm : (⟨false, List.replicate N false⟩ : FreeSemigroup Bool).length ≤ N + 1 := by
    simp [FreeSemigroup.length]
  use string _ hm ++ string _ hm
  intro x hx h
  obtain ⟨y, z, _, _, hy, hz, rfl⟩ := exists_of_append_eq hx h
  rw [← string_injective hy, ← string_injective hz, FreeSemigroup.length_mul] at hx
  simp [FreeSemigroup.length] at hx

end Pairing

section theory

open AtomicPairing ConcatenationStructure

variable {N : ℕ} {M : Type*} [ConcatenationStructure M] {x y : M}

/-- The strings of length at most `N + 1`. -/
noncomputable def short (N : ℕ) : List (FreeSemigroup Bool) :=
  (FreeSemigroup.finite_length_le (N + 1)).toFinset.toList

@[simp]
lemma mem_short {u : FreeSemigroup Bool} : u ∈ short N ↔ u.length ≤ N + 1 := by simp [short]

/-- `x` is the value of a string of length at most `N + 1`. -/
def IsShort (N : ℕ) (x : M) : Prop :=
  ∃ u : {u : FreeSemigroup Bool // u.length ≤ N + 1}, x = ofFreeSemigroup u.1

/-- `x` is the value of a string of length at most `N + 1`. -/
noncomputable def isShort (N : ℕ) : Semisentence ℒ⌢ 1 := isOneOf (short N)

@[simp]
lemma eval_isShort : M ⊧/![x] (isShort N) ↔ IsShort N x := by
  simp [isShort, IsShort]

/-- `y` is a left or a right factor of `x`. -/
def isFactor : Semisentence ℒ⌢ 2 := “y x. ∃ z, x = y ⌢ z ∨ x = z ⌢ y”

@[simp]
lemma eval_isFactor : M ⊧/![y, x] isFactor ↔ IsFactor y x := by
  simp [isFactor, IsFactor]

/-- `y` is reached from `x` by passing `k` times to a factor. -/
def IsFactorAt : ℕ → M → M → Prop
  | 0, x, y => x = y
  | k + 1, x, y => ∃ z, IsFactor z x ∧ IsFactorAt k z y

lemma exists_isFactorAt_of_transGen (h : Relation.TransGen IsFactor y x) :
    ∃ k, IsFactorAt (k + 1) x y := by
  induction h with
  | single h => exact ⟨0, _, h, rfl⟩
  | tail _ h ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, _, h, hk⟩

/-- One more step in `notFactorAt`. -/
def notFactorStep (φ : Semisentence ℒ⌢ 2) : Semisentence ℒ⌢ 2 :=
  ∀¹ ∀¹ ((“z w x y. ¬!isFactor z x ∨ w ≠ y” : Semisentence ℒ⌢ 4) ⋎
    (Rew.castLE (by decide : 2 ≤ 4) ▹ φ))

/-- `y` is not reached from `x` by passing `k` times to a factor. -/
def notFactorAt (k : ℕ) : Semisentence ℒ⌢ 2 := notFactorStep^[k] “x y. x ≠ y”

lemma eval_notFactorAt (k : ℕ) (x y : M) : M ⊧/![x, y] (notFactorAt k) ↔ ¬IsFactorAt k x y := by
  induction k generalizing x y with
  | zero => simp [notFactorAt, IsFactorAt]
  | succ k ih =>
    have hv (a b : M) :
        (fun i : Fin 2 ↦ (![b, a, x, y] : Fin 4 → M) (i.castLE (by decide))) = ![b, a] := by
      funext i
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    rw [notFactorAt, Function.iterate_succ_apply', ← notFactorAt, notFactorStep]
    suffices (∀ a b : M, (¬IsFactor b x ∨ ¬a = y) ∨ ¬IsFactorAt k b a) ↔
        ∀ z, IsFactor z x → ¬IsFactorAt k z y by
      simpa [hv, ih, IsFactorAt] using this
    grind

/-- Nothing is reached from itself by passing `k + 1` times to a factor. -/
def acyclic (k : ℕ) : Sentence ℒ⌢ := ∀¹ ∀¹ (“x y. x ≠ y” ⋎ notFactorAt (k + 1))

lemma models_acyclic_iff (k : ℕ) : M↓[ℒ⌢] ⊧ acyclic k ↔ ∀ x : M, ¬IsFactorAt (k + 1) x x := by
  simp [models_iff, acyclic, eval_notFactorAt]
  grind
lemma primrec_acyclic : Primrec acyclic :=
  have hstep : Primrec notFactorStep :=
    Semiformula.primrec_all.comp <| Semiformula.primrec_all.comp <|
      Semiformula.primrec₂_or.comp (Primrec.const _) (Semiformula.primrec_castLE _)
  Semiformula.primrec_all.comp <| Semiformula.primrec_all.comp <|
    Semiformula.primrec₂_or.comp (Primrec.const _) <|
      Primrec.nat_iterate Primrec.succ (Primrec.const _) (hstep.comp Primrec.snd).to₂

/-- Axioms for the structure of strings and formal pairs, other than the scheme `acyclic`. -/
inductive IsPairingAxiom (N : ℕ) : Sentence ℒ⌢ → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⌢, IsPairingAxiom N φ
  | stringNe {u v : FreeSemigroup Bool} : u.length ≤ N + 1 → v.length ≤ N + 1 → u ≠ v →
      IsPairingAxiom N “!!(biteral u) ≠ !!(biteral v)”
  | stringAppend {u v w : FreeSemigroup Bool} : u.length ≤ N + 1 → v.length ≤ N + 1 →
      w.length ≤ N + 1 → u * v = w →
      IsPairingAxiom N “!!(biteral u) ⌢ !!(biteral v) = !!(biteral w)”
  | stringAppendNe {u v w : FreeSemigroup Bool} : u.length ≤ N + 1 → v.length ≤ N + 1 →
      w.length ≤ N + 1 → u * v ≠ w →
      IsPairingAxiom N “!!(biteral u) ⌢ !!(biteral v) ≠ !!(biteral w)”
  | shortOfAppend : IsPairingAxiom N
      “∀ x y, !(isShort N) (x ⌢ y) → !(isShort N) x ∧ !(isShort N) y”
  | appendInjective : IsPairingAxiom N
      “∀ x y z w, ¬!(isShort N) (x ⌢ y) → x ⌢ y = z ⌢ w → x = z ∧ y = w”
  | existsAppend : IsPairingAxiom N “∀ x, !(isShort N) x ∨ ∃ y z, x = y ⌢ z”
  | existsNotShort : IsPairingAxiom N “∃ x, ¬!(isShort N) x”

/--
The theory of the strings of length at most `N + 1` and formal pairs: the products of strings
follow the table of concatenation, every other product is an injective pairing, every element is
a string or a product, and no element is reached from itself by passing to factors.
-/
abbrev PairingTheory (N : ℕ) : Theory ℒ⌢ := Set.ofPred (IsPairingAxiom N) ∪ Set.range acyclic

instance : 𝗘𝗤 ℒ⌢ ⪯ PairingTheory N :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ .inl <| IsPairingAxiom.equal φ hφ

lemma finite_isPairingAxiom (N : ℕ) : (Set.ofPred (IsPairingAxiom N)).Finite := by
  have h₁ := FreeSemigroup.finite_length_le (α := Bool) (N + 1)
  have h₂ := h₁.prod h₁
  have h₃ := h₁.prod h₂
  apply ((Theory.Eq.finite (L := ℒ⌢)).union <|
    (h₂.image fun p ↦ (“!!(biteral p.1) ≠ !!(biteral p.2)” : Sentence ℒ⌢)).union <|
    (h₃.image fun p ↦
      (“!!(biteral p.1) ⌢ !!(biteral p.2.1) = !!(biteral p.2.2)” : Sentence ℒ⌢)).union <|
    (h₃.image fun p ↦
      (“!!(biteral p.1) ⌢ !!(biteral p.2.1) ≠ !!(biteral p.2.2)” : Sentence ℒ⌢)).union <|
    Set.toFinite {_, _, _, _}).subset fun σ hσ ↦ by
    cases hσ with
    | equal _ h => exact .inl h
    | stringNe hu hv _ => exact .inr <| .inl ⟨(_, _), ⟨hu, hv⟩, rfl⟩
    | stringAppend hu hv hw _ => exact .inr <| .inr <| .inl ⟨(_, _, _), ⟨hu, hv, hw⟩, rfl⟩
    | stringAppendNe hu hv hw _ =>
      exact .inr <| .inr <| .inr <| .inl ⟨(_, _, _), ⟨hu, hv, hw⟩, rfl⟩
    | shortOfAppend => exact .inr <| .inr <| .inr <| .inr <| .inl rfl
    | appendInjective => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | existsAppend => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl rfl
    | existsNotShort => exact .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr rfl

instance : (PairingTheory N).RE :=
  Theory.RE.add (Theory.RE.ofFinite (finite_isPairingAxiom N)) (Theory.RE.range primrec_acyclic)

instance : (Pairing N)↓[ℒ⌢] ⊧* PairingTheory N := models_theory_iff.mpr <| by
  have hsh (a : Pairing N) : IsShort N a ↔ ∃ x hx, a = Pairing.string x hx :=
    ⟨fun ⟨u, hu⟩ ↦ ⟨u.1, u.2, hu.trans (Pairing.ofFreeSemigroup_eq u.2)⟩,
      fun ⟨x, hx, h⟩ ↦ ⟨⟨x, hx⟩, h.trans (Pairing.ofFreeSemigroup_eq hx).symm⟩⟩
  rintro σ (hσ | ⟨k, rfl⟩)
  · cases hσ with
    | equal _ h =>
      have : (Pairing N)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
      exact models_theory_iff.mp this _ h
    | stringNe hu hv h =>
      simpa [models_iff, Pairing.ofFreeSemigroup_eq hu, Pairing.ofFreeSemigroup_eq hv] using
        fun e ↦ h (Pairing.string_injective e)
    | stringAppend hu hv hw h =>
      subst h
      simpa [models_iff, Pairing.ofFreeSemigroup_eq hu, Pairing.ofFreeSemigroup_eq hv,
        Pairing.ofFreeSemigroup_eq hw] using Pairing.string_append_string hu hv hw
    | stringAppendNe hu hv hw h =>
      suffices Pairing.string _ hu ++ Pairing.string _ hv ≠ Pairing.string _ hw by
        simpa [models_iff, Pairing.ofFreeSemigroup_eq hu, Pairing.ofFreeSemigroup_eq hv,
          Pairing.ofFreeSemigroup_eq hw] using this
      intro e
      obtain ⟨x, y, _, _, hx, hy, hxy⟩ := Pairing.exists_of_append_eq hw e
      exact h (by rw [Pairing.string_injective hx, Pairing.string_injective hy, hxy])
    | shortOfAppend =>
      suffices ∀ a b : Pairing N, IsShort N (a ++ b) → IsShort N a ∧ IsShort N b by
        simpa [models_iff] using this
      intro a b h
      obtain ⟨u, hu, h⟩ := (hsh _).mp h
      obtain ⟨x, y, hx, hy, rfl, rfl, -⟩ := Pairing.exists_of_append_eq hu h
      exact ⟨(hsh _).mpr ⟨x, hx, rfl⟩, (hsh _).mpr ⟨y, hy, rfl⟩⟩
    | appendInjective =>
      suffices ∀ a b c d : Pairing N, ¬IsShort N (a ++ b) → a ++ b = c ++ d → a = c ∧ b = d by
        simpa [models_iff] using this
      intro a b c d h
      exact Pairing.append_injective fun x hx e ↦ h ((hsh _).mpr ⟨x, hx, e⟩)
    | existsAppend =>
      suffices ∀ a : Pairing N, IsShort N a ∨ ∃ b c, a = b ++ c by simpa [models_iff] using this
      intro a
      exact (Pairing.exists_string_or_append a).imp_left (hsh a).mpr
    | existsNotShort =>
      suffices ∃ a : Pairing N, ¬IsShort N a by simpa [models_iff] using this
      obtain ⟨a, ha⟩ := Pairing.exists_ne_string (N := N)
      exact ⟨a, fun h ↦ let ⟨x, hx, e⟩ := (hsh a).mp h; ha x hx e⟩
  · apply (models_acyclic_iff k).mpr
    have key (k : ℕ) : ∀ a b : Pairing N, IsFactorAt k a b → b.size + k ≤ a.size := by
      induction k with
      | zero =>
        rintro a b rfl
        exact le_rfl
      | succ k ih =>
        rintro a b ⟨c, ⟨d, hd | hd⟩, hk⟩ <;>
        · have := ih c b hk
          have := Pairing.size_pos d
          rw [hd, Pairing.size_append]
          omega
    intro a h
    have := key _ a a h
    omega

/-- A model of `PairingTheory N` is an atomic pairing whose atoms are the short strings. -/
noncomputable def atomicPairing (N : ℕ) (M : Type*) [ConcatenationStructure M]
    [hM : M↓[ℒ⌢] ⊧* PairingTheory N] :
    AtomicPairing (fun u v w : {u : FreeSemigroup Bool // u.length ≤ N + 1} ↦ u.1 * v.1 = w.1) M :=
  have ax {σ : Sentence ℒ⌢} (h : IsPairingAxiom N σ) : M↓[ℒ⌢] ⊧ σ :=
    models_theory_iff.mp hM σ (.inl h)
  { atom u := ofFreeSemigroup u.1
    atom_injective u v h := by
      by_contra hne
      have : (ofFreeSemigroup u.1 : M) ≠ ofFreeSemigroup v.1 := by
        simpa [models_iff] using ax (.stringNe u.2 v.2 fun e ↦ hne (Subtype.ext e))
      exact this h
    atom_append_atom u v w := by
      by_cases h : u.1 * v.1 = w.1
      · simpa [models_iff, h] using ax (.stringAppend u.2 v.2 w.2 h)
      · simpa [models_iff, h] using ax (.stringAppendNe u.2 v.2 w.2 h)
    exists_atom_of_append {x y s} h := by
      have : ∀ x y : M, IsShort N (x ++ y) → IsShort N x ∧ IsShort N y := by
        simpa [models_iff] using ax .shortOfAppend
      exact this x y ⟨s, h⟩
    append_injective {x y x' y'} h h' := by
      have : ∀ x y z w : M, ¬IsShort N (x ++ y) → x ++ y = z ++ w → x = z ∧ y = w := by
        simpa [models_iff] using ax .appendInjective
      exact this x y x' y' (fun ⟨s, hs⟩ ↦ h s hs) h'
    exists_append {x} h := by
      have : ∀ x : M, IsShort N x ∨ ∃ y z, x = y ++ z := by
        simpa [models_iff] using ax .existsAppend
      exact (this x).resolve_left fun ⟨s, hs⟩ ↦ h s hs
    exists_ne_atom := by
      obtain ⟨x, hx⟩ : ∃ x : M, ¬IsShort N x := by simpa [models_iff] using ax .existsNotShort
      exact ⟨x, fun s hs ↦ hx ⟨s, hs⟩⟩
    acyclic x h := by
      obtain ⟨k, hk⟩ := exists_isFactorAt_of_transGen h
      exact (models_acyclic_iff k).mp (models_theory_iff.mp hM _ (.inr ⟨k, rfl⟩)) x hk }

/-- Every model of `PairingTheory N` satisfies the same sentences as `Pairing N`. -/
theorem models_iff_models_pairing (M : Type*) [ConcatenationStructure M]
    [M↓[ℒ⌢] ⊧* PairingTheory N] (σ : Sentence ℒ⌢) : M↓[ℒ⌢] ⊧ σ ↔ (Pairing N)↓[ℒ⌢] ⊧ σ :=
  models_iff_of_atomicPairing (atomicPairing N M) (atomicPairing N (Pairing N))
    ⟨⟨.of false, by simp⟩, rfl, rfl⟩ ⟨⟨.of true, by simp⟩, rfl, rfl⟩ σ

lemma provable_pairingTheory_iff {σ : Sentence ℒ⌢} :
    PairingTheory N ⊢ σ ↔ (Pairing N)↓[ℒ⌢] ⊧ σ :=
  ⟨fun h ↦ consequence_iff'.mp (Theory.Proof.sound h) (Pairing N),
    fun h ↦ complete.{0} _ _ fun M _ _ ↦ (models_iff_models_pairing M σ).mpr h⟩

instance : Entailment.Complete (PairingTheory N) where
  con σ := by
    by_cases h : (Pairing N)↓[ℒ⌢] ⊧ σ
    · exact .inl <| provable_pairingTheory_iff.mpr h
    · exact .inr <| provable_pairingTheory_iff.mpr <| by simpa [models_iff] using h

/-- The theory of the structure of strings and formal pairs is decidable. -/
theorem decidable_theory_pairing (N : ℕ) :
    Entailment.Decidable (Tarski.Structure.theory ℒ⌢ (Pairing N)) where
  dec := by
    have : (Pairing N)↓[ℒ⌢] ⊧* Tarski.Structure.theory ℒ⌢ (Pairing N) :=
      models_theory_iff.mpr fun _ h ↦ h
    apply (Theory.decidable_of_complete (PairingTheory N) inferInstance).dec.of_eq
    intro σ
    exact provable_pairingTheory_iff.trans
      ⟨fun h ↦ (Entailment.by_axm h : Tarski.Structure.theory ℒ⌢ (Pairing N) ⊢ σ),
        fun h ↦ consequence_iff'.mp (Theory.Proof.sound h) (Pairing N)⟩

end theory

/--
Axioms of $\mathsf{WTC}$ without the empty string and with the unrestricted editor axiom.
- [HH14, Definition 5, Question 1]
-/
inductive IsWTCEditorAxiom : Sentence ℒ⌢ → Prop
  | wtc : ∀ φ ∈ 𝗪𝗧𝗖, IsWTCEditorAxiom φ
  | editor : IsWTCEditorAxiom “∀ x y z w, x ⌢ y = z ⌢ w →
      (x = z ∧ y = w) ∨ ∃ u, (x ⌢ u = z ∧ y = u ⌢ w) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”

/--
$\mathsf{WTC}$ without the empty string and with the unrestricted editor axiom.
- [HH14, Definition 5, Question 1]
-/
abbrev WTCEditor : Theory ℒ⌢ := Set.ofPred IsWTCEditorAxiom

instance : 𝗪𝗧𝗖 ⪯ WTCEditor := Entailment.WeakerThan.ofSubset IsWTCEditorAxiom.wtc

instance : 𝗘𝗤 ℒ⌢ ⪯ WTCEditor := Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖) inferInstance inferInstance

namespace WTCEditor

/-- Every axiom holds in all but finitely many of the structures `Pairing N`. -/
lemma eventually_models {σ : Sentence ℒ⌢} (hσ : σ ∈ WTCEditor) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧ σ := by
  rcases hσ with ⟨_, hσ⟩ | _
  swap
  · exact .of_forall fun N ↦ by
      simpa [models_iff] using fun (a b c d : Pairing N) ↦ Pairing.editor
  cases hσ
  case equal h =>
    have (N : ℕ) : (Pairing N)↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact .of_forall fun N ↦ models_theory_iff.mp (this N) _ h
  case concatAssoc u =>
    filter_upwards [Filter.eventually_ge_atTop u.length] with N hN
    have hu : u.length ≤ N + 1 := by omega
    simpa [models_iff, Pairing.ofFreeSemigroup_eq hu] using
      fun (a b c : Pairing N) ↦ Pairing.append_assoc_of_isSubstring hu
  case editor u =>
    exact .of_forall fun N ↦ by
      simpa [models_iff] using fun (a b c d : Pairing N) h _ ↦ Pairing.editor h
  case concatNeZero =>
    exact .of_forall fun N ↦ by
      simpa [models_iff, Pairing.zero_eq] using
        fun (a b : Pairing N) ↦ Pairing.append_ne_string rfl _
  case concatNeOne =>
    exact .of_forall fun N ↦ by
      simpa [models_iff, Pairing.one_eq] using
        fun (a b : Pairing N) ↦ Pairing.append_ne_string rfl _
  case zeroNeOne => exact .of_forall fun N ↦ by simpa [models_iff] using Pairing.zero_ne_one

/--
Every finite part of $\mathsf{WTC}$ with the editor axiom holds in all but finitely many of the
structures `Pairing N`.
-/
lemma eventually_models_of_finite {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor) (hfin : F.Finite) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧* F :=
  ((Filter.eventually_all_finite hfin).mpr fun _ hσ ↦ eventually_models (hF hσ)).mono
    fun _ h ↦ models_theory_iff.mpr h

/-- No finite part of $\mathsf{WTC}$ with the editor axiom is essentially undecidable. -/
theorem not_essentiallyUndecidable_of_finite {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor)
    (hfin : F.Finite) : ¬F.EssentiallyUndecidable :=
  let ⟨N, _⟩ := (eventually_models_of_finite hF hfin).exists
  Theory.not_essentiallyUndecidable_of_models (Pairing N) (decidable_theory_pairing N)

/--
$\mathsf{WTC}$ with the editor axiom does not interpret $\mathsf{TC}$.
- [HH14, Question 1]
-/
theorem notInterprets_TC : WTCEditor ⋫ 𝗧𝗖 :=
  DirectInterpretation.notInterprets_of_forall_finite_not_essentiallyUndecidable
    TC.finiteAxiomatizable fun _ ↦ not_essentiallyUndecidable_of_finite

end WTCEditor


/--
Axioms of $\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
inductive IsWTCEmptyEditorAxiom : Sentence ℒ⌢ₑ → Prop
  | wtcEmpty : ∀ φ ∈ 𝗪𝗧𝗖ₑ, IsWTCEmptyEditorAxiom φ
  | editor : IsWTCEmptyEditorAxiom “∀ x y s t, x ⌢ y = s ⌢ t →
      ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”

/--
$\mathsf{WTC}$ with the empty string and the editor axiom (TC3).
- [HH14, Definition 1, Question 1]
-/
abbrev WTCEmptyEditor : Theory ℒ⌢ₑ := Set.ofPred IsWTCEmptyEditorAxiom

instance : 𝗪𝗧𝗖ₑ ⪯ WTCEmptyEditor := Entailment.WeakerThan.ofSubset IsWTCEmptyEditorAxiom.wtcEmpty

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ WTCEmptyEditor :=
  Entailment.WeakerThan.trans (𝓣 := 𝗪𝗧𝗖ₑ) inferInstance inferInstance

open ConcatenationStructure ConcatenationEmptyStructure DirectTranslation

section option

variable {M : Type*} [ConcatenationStructure M] {x y : M}

lemma Option.ofList_cons (b : Bool) (l : List Bool) :
    (ofList (b :: l) : Option M) = some (ofFreeSemigroup ⟨b, l⟩) := by
  suffices ∀ (l : List Bool) (x : M),
      l.foldl (fun m b ↦ m ++ if b then 1 else 0) (some x) =
        some (l.foldl (fun m b ↦ m ++ if b then 1 else 0) x) by
    rw [ofFreeSemigroup, stringValue, ← this]
    cases b <;> rfl
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    intro x
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    cases b <;> rfl

@[simp]
lemma Option.not_isSubstring_none : ¬IsSubstring (some x) (none : Option M) := by
  rintro (h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩)
  · simp at h
  · rcases u with _ | u <;> simp at h
  · rcases v with _ | v <;> simp at h
  · rcases u with _ | u <;> rcases v with _ | v <;> simp at h
  · rcases u with _ | u <;> rcases v with _ | v <;> simp at h

lemma Option.isSubstring_of_some (h : IsSubstring (some x) (some y)) : IsSubstring x y := by
  rcases h with h | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · exact .inl <| Option.some.inj h
  · rcases u with _ | u
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inl ⟨u, Option.some.inj h⟩
  · rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, Option.some.inj h⟩
  · rcases u with _ | u <;> rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, by simpa using h⟩
    · exact .inr <| .inl ⟨u, by simpa using h⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨u, v, Option.some.inj h⟩
  · rcases u with _ | u <;> rcases v with _ | v
    · exact .inl <| by simpa using h.symm
    · exact .inr <| .inr <| .inl ⟨v, by simpa using h⟩
    · exact .inr <| .inl ⟨u, by simpa using h⟩
    · exact .inr <| .inr <| .inr <| .inr ⟨u, v, Option.some.inj h⟩

end option

namespace WTCEditor

section models

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* WTCEditor]

instance : M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := ⟨fun _ h ↦ Theory.models M WTCEditor (.wtc _ h)⟩

lemma editor {x y z w : M} (h : x ++ y = z ++ w) :
    (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) := by
  have := by simpa [models_iff] using Theory.models M _ IsWTCEditorAxiom.editor
  exact this x y z w h

/--
The strings of a model of $\mathsf{WTC}$ with the editor axiom together with an empty string form a
model of $\mathsf{WTC}$ with the empty string and the editor axiom.
-/
instance : (Option M)↓[ℒ⌢ₑ] ⊧* WTCEmptyEditor := by
  constructor
  rintro _ (⟨_, hσ⟩ | _)
  swap
  · suffices ∀ x y z w : Option M, x ++ y = z ++ w →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ ↦ Option.editor fun _ _ _ _ ↦ editor
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case emptyUnit => simp [models_iff, Option.empty_eq_none]
  case concatAssoc u =>
    suffices ∀ x y z : Option M, IsSubstring (x ++ y ++ z) (ofList u) ∨
        IsSubstring (x ++ (y ++ z)) (ofList u) → x ++ y ++ z = x ++ (y ++ z) by
      simpa [models_iff]
    rintro (_ | x) (_ | y) (_ | z) <;>
      simp only [Option.none_append, Option.append_none, implies_true, Option.some_append_some,
        Option.some.injEq]
    rcases u with _ | ⟨b, l⟩
    · simp [ofList, Option.empty_eq_none]
    · rw [Option.ofList_cons]
      have assoc : ∀ x y z : M, IsSubstring (x ++ y ++ z) (ofFreeSemigroup ⟨b, l⟩) ∨
          IsSubstring (x ++ (y ++ z)) (ofFreeSemigroup ⟨b, l⟩) → x ++ y ++ z = x ++ (y ++ z) := by
        simpa [models_iff] using Theory.models M 𝗪𝗧𝗖 (.concatAssoc ⟨b, l⟩)
      exact fun h ↦ assoc x y z <|
        h.imp Option.isSubstring_of_some Option.isSubstring_of_some
  case editor u =>
    suffices ∀ x y z w : Option M, x ++ y = z ++ w → IsSubstring (x ++ y) (ofList u) →
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    exact fun _ _ _ _ h _ ↦ Option.editor (fun _ _ _ _ ↦ editor) h
  case zeroNeEmpty => simp [models_iff, Option.empty_eq_none, Option.zero_eq_some]
  case oneNeEmpty => simp [models_iff, Option.empty_eq_none, Option.one_eq_some]
  case zeroAtom =>
    suffices ∀ x y : Option M, x ++ y = 0 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact (WTC.append_ne_zero x y (Option.some.inj h)).elim
  case oneAtom =>
    suffices ∀ x y : Option M, x ++ y = 1 → x = ∅ ∨ y = ∅ by simpa [models_iff]
    rintro (_ | x) (_ | y) h
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr rfl
    · exact (WTC.append_ne_one x y (Option.some.inj h)).elim
  case zeroNeOne =>
    simp [models_iff, Option.zero_eq_some, Option.one_eq_some]

end models

section code

variable {M : Type} [ConcatenationStructure M] {x y z : M}

/-- `z` is the code of the concatenation of the strings coded by `x` and `y`. -/
def IsCodeAppend (z x y : M) : Prop :=
  (x = 1 ∧ z = y) ∨ (y = 1 ∧ z = x) ∨ ∃ u v, x = 1 ++ u ∧ y = 1 ++ v ∧ z = 1 ++ (u ++ v)

/-- `z` is the code of the concatenation of the strings coded by `x` and `y`. -/
def isCodeAppend : Semisentence ℒ⌢ 3 :=
  “z x y. (x = !!(op(1).const) ∧ z = y) ∨ (y = !!(op(1).const) ∧ z = x) ∨
    ∃ u v, x = !!(op(1).const) ⌢ u ∧ y = !!(op(1).const) ⌢ v ∧ z = !!(op(1).const) ⌢ (u ⌢ v)”

@[simp]
lemma eval_isCodeAppend : M ⊧/![z, x, y] isCodeAppend ↔ IsCodeAppend z x y := by
  simp [isCodeAppend, IsCodeAppend]

section

variable [M↓[ℒ⌢] ⊧* WTCEditor]

lemma one_append_cancel (h : 1 ++ x = 1 ++ y) : x = y := by
  rcases editor h with ⟨-, h⟩ | ⟨u, ⟨h, -⟩ | ⟨h, -⟩⟩
  · exact h
  · exact (WTC.append_ne_one 1 u h).elim
  · exact (WTC.append_ne_one 1 u h.symm).elim

lemma emptyCode_injective : Function.Injective (emptyCode (M := M)) := by
  rintro (_ | x) (_ | y) h
  · rfl
  · exact (WTC.append_ne_one 1 y h.symm).elim
  · exact (WTC.append_ne_one 1 x h).elim
  · exact congrArg some <| one_append_cancel h

lemma isCodeAppend_emptyCode_iff {x y : Option M} :
    IsCodeAppend z (emptyCode x) (emptyCode y) ↔ z = emptyCode (x ++ y) := by
  have h (x y : M) : 1 ++ x = 1 ++ y ↔ x = y := ⟨one_append_cancel, congrArg _⟩
  have h' (x : M) : 1 ≠ 1 ++ x := fun h ↦ WTC.append_ne_one 1 x h.symm
  rcases x with _ | x <;> rcases y with _ | y <;>
    simp [IsCodeAppend, emptyCode, h, h', WTC.append_ne_one]

end

/--
The translation of the language with the empty string into $\mathsf{WTC}$ with the editor axiom that
codes a string by the string itself after the letter $1$, and the empty string by the letter $1$.
-/
def emptyTranslation : DirectTranslation WTCEditor ℒ⌢ₑ where
  domain := ⟨isEmptyCode⟩
  rel
    | Sum.inl Language.Concatenation.Rel.eq => ⟨“x y. x = y”⟩
  func
    | Sum.inl Language.Concatenation.Func.zero => ⟨“z. z = !!(op(1).const) ⌢ !!(op(0).const)”⟩
    | Sum.inl Language.Concatenation.Func.one => ⟨“z. z = !!(op(1).const) ⌢ !!(op(1).const)”⟩
    | Sum.inl Language.Concatenation.Func.concat => ⟨isCodeAppend⟩
    | Sum.inr (Language.Constant.Func.const _) => ⟨“z. z = !!(op(1).const)”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use emptyCode none
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsEmptyCode (e i) := by simpa [Semiformula.Operator.val] using he i
    rcases f with (_ | _ | _) | ⟨⟨⟩⟩
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode (some 0) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 0)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode (some 1) by
        simpa [Semiformula.Operator.val]
      use emptyCode (some 1)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ IsCodeAppend y (e 0) (e 1) by
        simpa [Semiformula.Operator.val]
      obtain ⟨x, hx⟩ := isEmptyCode_iff.mp (he 0)
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp (he 1)
      simp only [← hx, ← hy, isCodeAppend_emptyCode_iff]
      use emptyCode (x ++ y)
      simp
    · suffices ∃! y : M, IsEmptyCode y ∧ y = emptyCode none by
        simpa [Semiformula.Operator.val]
      use emptyCode none
      simp
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    exact fun _ _ _ _ ↦ Iff.rfl

namespace emptyTranslation

@[simp]
lemma dom_iff : emptyTranslation.Dom x ↔ IsEmptyCode x := by
  simp [DirectTranslation.dom_iff, emptyTranslation, Semiformula.Operator.val]

variable [M↓[ℒ⌢] ⊧* WTCEditor]

/-- The bijection of the strings of `M` and the empty string with their codes. -/
noncomputable def equiv : Option M ≃ emptyTranslation.Model M :=
  Equiv.ofBijective (fun x ↦ ⟨emptyCode x, by simp⟩) <| by
    constructor
    · exact fun x y h ↦ emptyCode_injective <| congrArg Model.val h
    · intro x
      obtain ⟨y, hy⟩ := isEmptyCode_iff.mp <| dom_iff.mp x.dom
      exact ⟨y, Model.ext hy⟩

@[simp]
lemma val_equiv (x : Option M) : (equiv x : M) = emptyCode x := rfl

lemma struc_eq : Model.struc emptyTranslation M = Tarski.Structure.ofEquiv equiv :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      obtain ⟨v, rfl⟩ : ∃ w, v = equiv ∘ w := ⟨equiv.symm ∘ v, by simp [← Function.comp_assoc]⟩
      rcases f with (_ | _ | _) | ⟨⟨⟩⟩
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl
      · have h : M ⊧/![emptyCode (v 0 ++ v 1), emptyCode (v 0), emptyCode (v 1)] isCodeAppend :=
          eval_isCodeAppend.mpr <| isCodeAppend_emptyCode_iff.mpr rfl
        change Semiformula.Evalb _ isCodeAppend
        convert h using 2
        funext i
        match i with
        | 0 =>
          change emptyCode (equiv.symm (equiv (v 0)) ++ equiv.symm (equiv (v 1))) = _
          simp
        | 1 | 2 => rfl
      · simp [emptyTranslation, Semiformula.Operator.val]
        rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext <| (Model.eq_iff v).trans equiv.symm.apply_eq_iff_eq.symm)

end emptyTranslation

/--
The codes of the strings of a model of $\mathsf{WTC}$ with the editor axiom and of the empty string
form a model of $\mathsf{WTC}$ with the empty string and the editor axiom.
-/
instance [M↓[ℒ⌢] ⊧* WTCEditor] : (emptyTranslation.Model M)↓[ℒ⌢ₑ] ⊧* WTCEmptyEditor := by
  have : Option M ≡ₑ[ℒ⌢ₑ] emptyTranslation.Model M := by
    rw [emptyTranslation.struc_eq]
    exact Tarski.Structure.ElementaryEquiv.ofEquiv emptyTranslation.equiv
  exact (Tarski.Structure.ElementaryEquiv.modelsTheory (M₁ := Option M)).mp inferInstance

/--
$\mathsf{WTC}$ with the editor axiom interprets $\mathsf{WTC}$ with the empty string and the editor
axiom.
-/
instance : WTCEditor ⊳ WTCEmptyEditor where
  trln := emptyTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end code

end WTCEditor

/--
$\mathsf{WTC}$ with the empty string and the editor axiom does not interpret $\mathsf{TC}$.
- [HH14, Question 1]
-/
theorem WTCEmptyEditor.notInterprets_TCEmpty : WTCEmptyEditor ⋫ 𝗧𝗖ₑ :=
  ⟨fun π ↦ WTCEditor.notInterprets_TC.false <| DirectInterpretation.comp
    (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖) <| π.comp (inferInstance : WTCEditor ⊳ WTCEmptyEditor)⟩

end FFL.FirstOrder.Concatenation

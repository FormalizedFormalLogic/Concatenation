module

public import Concatenation.Coding
public import Concatenation.Semantics.AtomicPairing
public import Concatenation.Semantics.Standard
public import Concatenation.ToFoundation.Decidability
public import Concatenation.ToFoundation.PrimrecCoding
public import Concatenation.WTC.Basic

/-!
# Strings and formal pairs

The structure of the binary strings of length at most `N + 1` and the formal pairs built from them
has a decidable theory.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

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
  rcases h with rfl | ⟨b, h⟩ | ⟨b, h⟩ | ⟨b, c, h⟩ | ⟨b, c, h⟩
  · exact ⟨u, hu, rfl⟩
  · obtain ⟨_, y, _, hy, -, rfl, -⟩ := exists_of_append_eq hu h.symm
    exact ⟨y, hy, rfl⟩
  · obtain ⟨x, _, hx, _, rfl, -, -⟩ := exists_of_append_eq hu h.symm
    exact ⟨x, hx, rfl⟩
  · obtain ⟨_, _, hz, _, h', -, -⟩ := exists_of_append_eq hu h.symm
    obtain ⟨_, y, _, hy, -, rfl, -⟩ := exists_of_append_eq hz h'
    exact ⟨y, hy, rfl⟩
  · obtain ⟨_, _, _, hz, -, h', -⟩ := exists_of_append_eq hu h.symm
    obtain ⟨x, _, hx, _, rfl, -, -⟩ := exists_of_append_eq hz h'
    exact ⟨x, hx, rfl⟩

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
  rcases h with h | h
  · obtain ⟨v, hv, h⟩ := exists_of_isSubstring hu h
    exact append_assoc_of_eq_string hv <| .inl h
  · obtain ⟨v, hv, h⟩ := exists_of_isSubstring hu h
    exact append_assoc_of_eq_string hv <| .inr h

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
  rw [ConcatenationStructure.ofFreeSemigroup, h₀, h _ _ (by simp) (by simpa [FreeSemigroup.of])]
  simp [FreeSemigroup.of]


/-- No formal pair inside is the pair of two strings whose concatenation is a string. -/
def Good : PrePairing N → Prop
  | string _ _ => True
  | pair a b => Good a ∧ Good b ∧ a ++ b = pair a b

lemma good_append (ha : a.Good) (hb : b.Good) : (a ++ b).Good := by
  rcases append_eq a b with ⟨x, y, hx, hy, h, rfl, rfl, h'⟩ | h'
  · rw [h']
    trivial
  · rw [h']
    exact ⟨ha, hb, h'⟩

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
  rcases append_eq a b with ⟨x, y, hx, hy, h, rfl, rfl, h'⟩ | h'
  · rw [h']
    exact FreeSemigroup.length_mul x y
  · rw [h']
    rfl

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

lemma isSubstring_val (h : IsSubstring a b) : IsSubstring a.1 b.1 := by
  rcases h with rfl | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩ | ⟨u, v, h⟩
  · exact .inl rfl
  · exact .inr <| .inl ⟨u.1, congrArg Pairing.val h⟩
  · exact .inr <| .inr <| .inl ⟨v.1, congrArg Pairing.val h⟩
  · exact .inr <| .inr <| .inr <| .inl ⟨u.1, v.1, congrArg Pairing.val h⟩
  · exact .inr <| .inr <| .inr <| .inr ⟨u.1, v.1, congrArg Pairing.val h⟩

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
  have h (l : List Bool) (m : Pairing N) :
      (l.foldl (fun m b ↦ m ++ if b then 1 else 0) m).1 =
        l.foldl (fun m b ↦ m ++ if b then 1 else 0) m.1 := by
    induction l generalizing m with
    | nil => rfl
    | cons b l ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      cases b <;> rfl
  apply Pairing.ext
  rw [ConcatenationStructure.ofFreeSemigroup, h, val_string, ← PrePairing.ofFreeSemigroup_eq hu]
  rcases u with ⟨b, l⟩
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

lemma finite_length_le (N : ℕ) : {u : FreeSemigroup Bool | u.length ≤ N + 1}.Finite :=
  ((List.finite_length_le Bool (N + 1)).preimage FreeSemigroup.toList_injective.injOn).subset
    fun u hu ↦ by simpa [FreeSemigroup.toList, FreeSemigroup.length] using hu

/-- The strings of length at most `N + 1`. -/
noncomputable def short (N : ℕ) : List (FreeSemigroup Bool) := (finite_length_le N).toFinset.toList

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
    constructor
    · intro h z hz hk
      rcases h y z with (h | h) | h
      · exact h hz
      · exact h rfl
      · exact h hk
    · intro h a b
      by_cases hb : IsFactor b x
      · by_cases ha : a = y
        · exact .inr (ha ▸ h b hb)
        · exact .inl (.inr ha)
      · exact .inl (.inl hb)

/-- Nothing is reached from itself by passing `k + 1` times to a factor. -/
def acyclic (k : ℕ) : Sentence ℒ⌢ := ∀¹ ∀¹ (“x y. x ≠ y” ⋎ notFactorAt (k + 1))

lemma models_acyclic_iff (k : ℕ) : M↓[ℒ⌢] ⊧ acyclic k ↔ ∀ x : M, ¬IsFactorAt (k + 1) x x := by
  suffices (∀ a b : M, ¬b = a ∨ ¬IsFactorAt (k + 1) b a) ↔ ∀ x : M, ¬IsFactorAt (k + 1) x x by
    simpa [models_iff, acyclic, eval_notFactorAt] using this
  constructor
  · intro h x
    exact (h x x).resolve_left (not_not.mpr rfl)
  · intro h a b
    by_cases e : b = a
    · exact .inr (e ▸ h b)
    · exact .inl e
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
  have h₂ := (finite_length_le N).prod (finite_length_le N)
  have h₃ := (finite_length_le N).prod h₂
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
      have : ∃ x : M, ¬IsShort N x := by simpa [models_iff] using ax .existsNotShort
      obtain ⟨x, hx⟩ := this
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

end FFL.FirstOrder.Concatenation

module

public import Concatenation.OpenProblem
public import Concatenation.Semantics.Standard
public import Concatenation.TC.Empty
public import Concatenation.TC.FiniteModel
public import Concatenation.TC.Undecidability
public import Concatenation.WTC.Basic

/-!
# $\mathsf{WTC}$ with the editor axiom

Every finite part of $\mathsf{WTC}$ with the unrestricted editor axiom holds in a structure of
strings and formal pairs.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
The editor axiom for nonempty strings.
- [GZ08, §1]
-/
def editorAxiom : Sentence ℒ⌢ := “∀ x y z w, x ⌢ y = z ⌢ w →
  (x = z ∧ y = w) ∨ ∃ u, (x ⌢ u = z ∧ y = u ⌢ w) ∨ (x = z ⌢ u ∧ u ⌢ y = w)”

/-- $\mathsf{WTC}$ with the unrestricted editor axiom, without the empty string. -/
abbrev WTCEditor : Theory ℒ⌢ := insert editorAxiom 𝗪𝗧𝗖

instance : 𝗘𝗤 ℒ⌢ ⪯ WTCEditor :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ .inr <| IsWTCAxiom.equal φ hφ

/--
The editor axiom.
- [HH14, Definition 1]
-/
def editorAxiomEmpty : Sentence ℒ⌢ₑ := “∀ x y s t, x ⌢ y = s ⌢ t →
  ∃ w, (x ⌢ w = s ∧ y = w ⌢ t) ∨ (x = s ⌢ w ∧ w ⌢ y = t)”

/--
$\mathsf{WTC}$ with the unrestricted editor axiom.
- [HH14, Question 1]
-/
abbrev WTCEmptyEditor : Theory ℒ⌢ₑ := insert editorAxiomEmpty 𝗪𝗧𝗖ₑ

instance : 𝗘𝗤 ℒ⌢ₑ ⪯ WTCEmptyEditor :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ .inr <| IsWTCEmptyAxiom.equal φ hφ

/--
Does $\mathsf{WTC}$ with the unrestricted editor axiom interpret $\mathsf{TC}$?
- [HH14, Question 1]
-/
open_problem WTCEmptyEditor_interprets_TCEmpty := Nonempty (WTCEmptyEditor ⊳ 𝗧𝗖ₑ)

namespace WTCEditor

/--
The nonempty binary strings of length at most `N + 1`, and the formal pairs built from them.
-/
inductive Pairing (N : ℕ) : Type
  | string (x : FreeSemigroup Bool) (hx : x.length ≤ N + 1) : Pairing N
  | pair (a b : Pairing N) : Pairing N

namespace Pairing

variable {N : ℕ} {a b c d : Pairing N} {x y u : FreeSemigroup Bool}

instance : Nonempty (Pairing N) := ⟨string 0 <| by simp [zero_eq_of_false]⟩

/--
Two strings are concatenated when the result is of length at most `N + 1`; every other product is
the formal pair.
-/
instance : ConcatenationStructure (Pairing N) where
  zero := string 0 <| by simp [zero_eq_of_false]
  one := string 1 <| by simp [one_eq_of_true]
  append
    | string x hx, string y hy =>
      if h : (x * y).length ≤ N + 1 then string (x * y) h else pair (string x hx) (string y hy)
    | a, b => pair a b

lemma zero_eq : (0 : Pairing N) = string 0 (by simp [zero_eq_of_false]) := rfl

lemma one_eq : (1 : Pairing N) = string 1 (by simp [one_eq_of_true]) := rfl

lemma string_append_string (hx : x.length ≤ N + 1) (hy : y.length ≤ N + 1)
    (h : (x * y).length ≤ N + 1) : string x hx ++ string y hy = string (x * y) h :=
  dite_eq_left_of_eq_true <| eq_true h

/-- A product is a concatenation of strings or a formal pair. -/
lemma append_eq (a b : Pairing N) :
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

lemma zero_ne_one : (0 : Pairing N) ≠ 1 := by
  simp [zero_eq, one_eq, zero_eq_of_false, one_eq_of_true, FreeSemigroup.of]

lemma ofFreeSemigroup_eq (hu : u.length ≤ N + 1) :
    (ConcatenationStructure.ofFreeSemigroup u : Pairing N) = string u hu := by
  have hb (b : Bool) : (FreeSemigroup.of b).length ≤ N + 1 := by simp
  have h₀ (b : Bool) : (if b then 1 else 0 : Pairing N) = string (FreeSemigroup.of b) (hb b) := by
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

end Pairing

/-- Every axiom holds in all but finitely many of the structures `Pairing N`. -/
lemma eventually_models {σ : Sentence ℒ⌢} (hσ : σ ∈ WTCEditor) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧ σ := by
  rcases hσ with rfl | hσ
  · exact .of_forall fun N ↦ by
      simpa [models_iff, editorAxiom] using fun (a b c d : Pairing N) ↦ Pairing.editor
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
theorem eventually_models_of_finite {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor) (hfin : F.Finite) :
    ∀ᶠ N in Filter.atTop, (Pairing N)↓[ℒ⌢] ⊧* F :=
  ((Filter.eventually_all_finite hfin).mpr fun _ hσ ↦ eventually_models (hF hσ)).mono
    fun _ h ↦ models_theory_iff.mpr h

/--
If the theories of infinitely many of the structures `Pairing N` are decidable, then no finite
part of $\mathsf{WTC}$ with the editor axiom is essentially undecidable.
-/
theorem not_essentiallyUndecidable_of_finite
    (h : ∃ᶠ N in Filter.atTop, Entailment.Decidable (Tarski.Structure.theory ℒ⌢ (Pairing N)))
    {F : Theory ℒ⌢} (hF : F ⊆ WTCEditor) (hfin : F.Finite) : ¬F.EssentiallyUndecidable :=
  let ⟨N, _, hN⟩ := ((eventually_models_of_finite hF hfin).and_frequently h).exists
  Theory.not_essentiallyUndecidable_of_models (Pairing N) hN

/--
If the theories of infinitely many of the structures `Pairing N` are decidable, then
$\mathsf{WTC}$ with the editor axiom does not interpret $\mathsf{TC}$.
- [HH14, Question 1]
-/
theorem notInterprets_TC
    (h : ∃ᶠ N in Filter.atTop, Entailment.Decidable (Tarski.Structure.theory ℒ⌢ (Pairing N))) :
    WTCEditor ⋫ 𝗧𝗖 :=
  DirectInterpretation.notInterprets_of_forall_finite_not_essentiallyUndecidable
    finiteAxiomatizable_TC fun _ ↦ not_essentiallyUndecidable_of_finite h

end WTCEditor

end FFL.FirstOrder.Concatenation

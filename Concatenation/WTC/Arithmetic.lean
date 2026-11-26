module

public import Concatenation.TC.Interpretability
public import Concatenation.ToFoundation.Arithmetic.R
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Arithmetic.R0.Visser
public import Concatenation.ToFoundation.Interpretability.DefinitionalEquivalence
public import Concatenation.ToFoundation.Interpretability.Undecidability
public import Concatenation.ToMathlib.FreeSemigroup
public import Concatenation.WTC.Standard
import Concatenation.OpenProblem

/-!
# Mutual interpretability of $\mathsf{WTC}$ and $\mathsf{R}_0$

$\mathsf{WTC}$, with two or more letters, is mutually interpretable with $\mathsf{R}_0$, and
essentially undecidable; it interprets the recursively enumerable theories of a finite language that
are locally finitely satisfiable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

section arithmetic

open ConcatenationStructure DirectTranslation

namespace WTC

variable {M : Type*} [ConcatenationStructure M] {u v w x y z : M} {m n : ℕ}

/-- The pair of `u` and `v` is listed between separators in `w`. -/
def IsEntry (u v w : M) : Prop := IsSubstring (0 ++ 0 ++ pairOf u v ++ 0 ++ 0) w

/-- The pair of `u` and `v` is listed between separators in `w`. -/
def isEntry : Semisentence ℒ⌢ 3 :=
  “u v w. !isSubstring (!!(op(0).const) ⌢ !!(op(0).const) ⌢ (u ⌢ !!(op(0).const) ⌢ v) ⌢
    !!(op(0).const) ⌢ !!(op(0).const)) w”

@[simp]
lemma eval_isEntry : M ⊧/![u, v, w] isEntry ↔ IsEntry u v w := by simp [isEntry, IsEntry, pairOf]

/--
`w` is a multiplication table for `x`: each pair of `1`-tallies listed in it is `(x, 1)` or is
`(u x, v 1)` for a pair `(u, v)` of `1`-tallies listed in it.
- [Hor12, §4, Definition 4.7]
-/
def IsMulTable (x w : M) : Prop := ∀ u' v', IsTally 1 u' → IsTally 1 v' → IsEntry u' v' w →
  (u' = x ∧ v' = 1) ∨
    ∃ u v, IsTally 1 u ∧ IsTally 1 v ∧ u' = u ++ x ∧ v' = v ++ 1 ∧ IsEntry u v w

/-- `w` is a multiplication table for `x`. -/
def isMulTable : Semisentence ℒ⌢ 2 :=
  “x w. ∀ u' v', !isTally !!(op(1).const) u' → !isTally !!(op(1).const) v' → !isEntry u' v' w →
    (u' = x ∧ v' = !!(op(1).const)) ∨
      ∃ u v, !isTally !!(op(1).const) u ∧ !isTally !!(op(1).const) v ∧
        u' = u ⌢ x ∧ v' = v ⌢ !!(op(1).const) ∧ !isEntry u v w”

@[simp]
lemma eval_isMulTable : M ⊧/![x, w] isMulTable ↔ IsMulTable x w := by simp [isMulTable, IsMulTable]

/-- `z` is a product of the `1`-tallies `x` and `y`, read off a multiplication table. -/
def IsProduct (z x y : M) : Prop :=
  IsTally 1 z ∧ IsTally 1 x ∧ IsTally 1 y ∧ ∃ w, IsMulTable x w ∧ IsEntry z y w

/-- `z` is a product of the `1`-tallies `x` and `y`, read off a multiplication table. -/
def isProduct : Semisentence ℒ⌢ 3 :=
  “z x y. !isTally !!(op(1).const) z ∧ !isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧
    ∃ w, !isMulTable x w ∧ !isEntry z y w”

@[simp]
lemma eval_isProduct : M ⊧/![z, x, y] isProduct ↔ IsProduct z x y := by simp [isProduct, IsProduct]

/-- `z` is the sum of `x` and `y`: their concatenation, with `0` neutral. -/
def AddGraph (z x y : M) : Prop :=
  (y = 0 ∧ z = x) ∨ (y ≠ 0 ∧ x = 0 ∧ z = y) ∨ (y ≠ 0 ∧ x ≠ 0 ∧ z = x ++ y)

/-- `z` is the sum of `x` and `y`. -/
def addGraph : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(0).const) ∧ z = x) ∨ (y ≠ !!(op(0).const) ∧ x = !!(op(0).const) ∧ z = y) ∨
    (y ≠ !!(op(0).const) ∧ x ≠ !!(op(0).const) ∧ z = x ⌢ y)”

@[simp]
lemma eval_addGraph : M ⊧/![z, x, y] addGraph ↔ AddGraph z x y := by simp [addGraph, AddGraph]

/-- `z` is the product of `x` and `y` if there is exactly one, and `0` otherwise. -/
def MulGraph (z x y : M) : Prop :=
  ((∃! r, IsProduct r x y) ∧ IsProduct z x y) ∨ (¬(∃! r, IsProduct r x y) ∧ z = 0)

/-- `z` is the product of `x` and `y` if there is exactly one, and `0` otherwise. -/
def mulGraph : Semisentence ℒ⌢ 3 :=
  “z x y. ((∃! r, !isProduct r x y) ∧ !isProduct z x y) ∨
    (¬(∃! r, !isProduct r x y) ∧ z = !!(op(0).const))”

@[simp]
lemma eval_mulGraph : M ⊧/![z, x, y] mulGraph ↔ MulGraph z x y := by simp [mulGraph, MulGraph]

/-- `x` is less than `y`: `0` below everything else, or a proper prefix of `y`. -/
def LtGraph (x y : M) : Prop := (x = 0 ∧ y ≠ 0) ∨ ∃ v, y = x ++ v

/-- `x` is less than `y`. -/
def ltGraph : Semisentence ℒ⌢ 2 :=
  “x y. (x = !!(op(0).const) ∧ y ≠ !!(op(0).const)) ∨ ∃ v, y = x ⌢ v”

@[simp]
lemma eval_ltGraph : M ⊧/![x, y] ltGraph ↔ LtGraph x y := by simp [ltGraph, LtGraph]

lemma existsUnique_addGraph (x y : M) : ∃! z, AddGraph z x y := by
  by_cases hy : y = 0
  · use x
    simp [AddGraph, hy]
  by_cases hx : x = 0
  · use y
    simp [AddGraph, hx, hy]
  · use x ++ y
    simp [AddGraph, hx, hy]

lemma existsUnique_mulGraph (x y : M) : ∃! z, MulGraph z x y := by
  by_cases h : ∃! r, IsProduct r x y
  · simp [MulGraph, h]
  · use 0
    simp [MulGraph, h]

/--
The translation of the language of arithmetic into $\mathsf{WTC}$ on all strings: `0` is `0`, `1`
is `1`, `+`, `*` and `<` are `AddGraph`, `MulGraph` and `LtGraph`.
- [Hor12, §4, Corollary 4.9]
-/
def arithmeticTranslation : DirectTranslation 𝗪𝗧𝗖 ℒₒᵣ where
  domain := ⟨“x. ⊤”⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨ltGraph⟩
  func
    | .zero => ⟨“z. z = !!(op(0).const)”⟩
    | .one => ⟨“z. z = !!(op(1).const)”⟩
    | .add => ⟨addGraph⟩
    | .mul => ⟨mulGraph⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_addGraph (e 0) (e 1)
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_mulGraph (e 0) (e 1)
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma arithmeticTranslation_dom (x : M) [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖] : arithmeticTranslation.Dom x := by
  simp [dom_iff, arithmeticTranslation, Semiformula.Operator.val]

section TCPlus

variable {M : Type*} [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺] {x y z : M}

/-- A multiplication sequence in a model of $\mathsf{TC}^+$ is a multiplication table. -/
lemma isMulTable_of_isMulSeq (h : IsMulSeq x y z) : IsMulTable x z := by
  intro u' v' hu' hv' he
  have hfirst (hp : 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0 ◨ z) : u' = x ∧ v' = 1 := by
    have h1 := isTally_one_one (M := M)
    rcases hp.total h.isFirst with hp | hp
    · exact IsFirst.pairOf_inj hv' h.isTally_left h1 hp
    · simpa [eq_comm] using IsFirst.pairOf_inj h1 hu' hv' hp
  have hstep (s) (hs : s ++ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) ◨ z) :
      ∃ u v, IsTally 1 u ∧ IsTally 1 v ∧ u' = u ++ x ∧ v' = v ++ 1 ∧ IsEntry u v z := by
    have hs : s ++ 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0 ◨ z := by
      simpa only [Concatenation.append_assoc] using hs
    obtain ⟨u, v, hu, hv, hu'', hv'', hsuf⟩ := h.exists_pred s u' v' hu' hv' hs
    use u, v, hu, hv, hu'', hv''
    have h₁ : 0 ++ 0 ++ pairOf u v ++ (0 ++ 0) = 0 ++ 0 ++ pairOf u v ++ 0 ++ 0 := by
      simp only [Concatenation.append_assoc]
    have h₂ : s ++ (0 ++ 0) ◨ s ++ 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0 := by
      simp only [Concatenation.append_assoc]
      exact .inr ⟨pairOf u' v' ++ (0 ++ 0), by simp only [Concatenation.append_assoc]⟩
    rw [IsEntry, ← h₁]
    apply (hsuf.append_congr (z := 0 ++ 0)).isSubstring.trans
    exact (h₂.trans hs).isSubstring
  rcases isSubstring_iff.mp he with he | ⟨s, he⟩ | ⟨t, he⟩ | ⟨s, t, he⟩
  · exact .inl <| hfirst <| .inl he
  · exact .inr <| hstep s <| .inl he.symm
  · exact .inl <| hfirst <| .inr ⟨t, he⟩
  · exact .inr <| hstep s <| .inr ⟨t, he⟩

end TCPlus

variable [M↓[ℒ⌢] ⊧* 𝗪𝗧𝗖]

section tallyOf

@[simp]
lemma ofFreeSemigroup_tallyOf : ∀ n, (ofFreeSemigroup (tallyOf n) : M) = tallyOf n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [ofFreeSemigroup_tallyOf (n + 1)]

lemma isTally_tallyOf_add_one (n : ℕ) : IsTally 1 (tallyOf (n + 1) : M) := by
  simpa using isTally_ofFreeSemigroup_iff (M := M) (c := 1) |>.mpr <| isTally_tallyOf_succ n

lemma tallyOf_add_one_ne_zero (n : ℕ) : (tallyOf (n + 1) : M) ≠ 0 := by
  rcases n with _ | n <;> simp [tallyOf]

lemma tallyOf_add_one_append (m : ℕ) :
    ∀ n, (tallyOf (m + 1) ++ tallyOf (n + 1) : M) = tallyOf (m + 1 + (n + 1)) := by
  have h (n) : (tallyOf (m + 1) ++ tallyOf (n + 1) : FreeSemigroup Bool) =
      tallyOf (m + 1 + (n + 1)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [tallyOf_add_two, ← Concatenation.append_assoc, ih]
      rfl
  intro n
  simpa using congrArg (ofFreeSemigroup (α := M)) (h n)

lemma eq_tallyOf_of_tallyOf_eq_append_one (h : tallyOf (n + 2) = v ++ 1) :
    v = tallyOf (n + 1) := by
  rw [← ofFreeSemigroup_tallyOf] at h
  obtain ⟨a, b, rfl, hb, h⟩ := exists_of_append_eq_ofFreeSemigroup h.symm
  obtain rfl : 1 = b := ofFreeSemigroup_injective (M := M) hb
  rw [← isAtom_one.append_right_cancel (x := tallyOf (n + 1)) h, ofFreeSemigroup_tallyOf]

lemma exists_eq_tallyOf_of_tallyOf_eq_append (h : tallyOf n = x ++ y) :
    ∃ i < n, x = tallyOf i := by
  fun_induction tallyOf n (M := M) generalizing y with
  | case1 => exact absurd h.symm <| append_ne_zero x y
  | case2 => exact absurd h.symm <| append_ne_one x y
  | case3 n ih =>
    have hu : IsSubstring (tallyOf (n + 2) : M) (ofFreeSemigroup (tallyOf (n + 2))) := by simp
    rcases editor _ h hu with ⟨rfl, -⟩ | ⟨w, ⟨-, hw⟩ | ⟨hw, -⟩⟩
    · use n + 1
      simp
    · exact absurd hw.symm <| append_ne_one w y
    · obtain ⟨i, hi, rfl⟩ := ih hw
      use i
      grind

end tallyOf

section IsProduct

lemma IsMulTable.eq_tallyOf (hw : IsMulTable (tallyOf (m + 1)) w) :
    ∀ n z, IsTally 1 z → IsEntry z (tallyOf (n + 1)) w → z = tallyOf ((m + 1) * (n + 1))
  | 0, z, hz, h => by
    rcases hw z _ hz (isTally_tallyOf_add_one 0) h with ⟨rfl, -⟩ | ⟨u, v, -, -, -, h, -⟩
    · simp
    · exact absurd h.symm <| append_ne_one v 1
  | n + 1, z, hz, h => by
    rcases hw z _ hz (isTally_tallyOf_add_one (n + 1)) h with ⟨-, h⟩ | ⟨u, v, hu, -, rfl, h, he⟩
    · exact absurd h <| append_ne_one _ 1
    · rw [eq_tallyOf_of_tallyOf_eq_append_one h] at he
      obtain rfl := hw.eq_tallyOf n u hu he
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (n := (m + 1) * (n + 1)) (by simp)
      rw [hk, tallyOf_add_one_append, ← hk, Nat.mul_succ (m + 1) (n + 1)]

lemma isEntry_ofFreeSemigroup_iff {a b c : FreeSemigroup Bool} :
    IsEntry (ofFreeSemigroup a : M) (ofFreeSemigroup b) (ofFreeSemigroup c) ↔ IsEntry a b c := by
  have h : (0 ++ 0 ++ pairOf (ofFreeSemigroup a) (ofFreeSemigroup b) ++ 0 ++ 0 : M) =
      ofFreeSemigroup (0 ++ 0 ++ pairOf a b ++ 0 ++ 0) := by simp [pairOf]
  rw [IsEntry, h, isSubstring_ofFreeSemigroup_ofFreeSemigroup_iff, IsEntry]

lemma IsEntry.exists_eq_ofFreeSemigroup {c : FreeSemigroup Bool}
    (h : IsEntry u v (ofFreeSemigroup c)) :
    ∃ a b, u = ofFreeSemigroup a ∧ v = ofFreeSemigroup b := by
  obtain ⟨t, ht, -⟩ := isSubstring_ofFreeSemigroup_iff.mp h
  obtain ⟨t, -, ht, -, -⟩ := exists_of_append_eq_ofFreeSemigroup ht
  obtain ⟨t, -, ht, -, -⟩ := exists_of_append_eq_ofFreeSemigroup ht
  obtain ⟨-, t, -, ht, -⟩ := exists_of_append_eq_ofFreeSemigroup ht
  obtain ⟨t, b, ht, hb, -⟩ := exists_of_append_eq_ofFreeSemigroup ht
  obtain ⟨a, -, ha, -, -⟩ := exists_of_append_eq_ofFreeSemigroup ht
  use a, b

lemma IsMulTable.ofFreeSemigroup {a c : FreeSemigroup Bool} (h : IsMulTable a c) :
    IsMulTable (ofFreeSemigroup a : M) (ofFreeSemigroup c) := by
  intro u' v' hu hv he
  obtain ⟨u', v', rfl, rfl⟩ := he.exists_eq_ofFreeSemigroup
  rw [← ofFreeSemigroup_one, isTally_ofFreeSemigroup_iff] at hu hv
  rcases h u' v' hu hv (isEntry_ofFreeSemigroup_iff.mp he) with
    ⟨rfl, rfl⟩ | ⟨u, v, hu', hv', rfl, rfl, he'⟩
  · simp
  · right
    use ConcatenationStructure.ofFreeSemigroup u, ConcatenationStructure.ofFreeSemigroup v
    rw [← ofFreeSemigroup_one, isTally_ofFreeSemigroup_iff, isTally_ofFreeSemigroup_iff,
      isEntry_ofFreeSemigroup_iff]
    simp [hu', hv', he']

lemma isProduct_tallyOf_iff :
    IsProduct z (tallyOf (m + 1)) (tallyOf (n + 1)) ↔ z = tallyOf ((m + 1) * (n + 1)) := by
  have h (z) (hz : IsProduct z (tallyOf (m + 1) : M) (tallyOf (n + 1))) :
      z = tallyOf ((m + 1) * (n + 1)) := by
    obtain ⟨hz, -, -, w, hw, he⟩ := hz
    exact hw.eq_tallyOf n z hz he
  suffices ∃ z, IsProduct z (tallyOf (m + 1) : M) (tallyOf (n + 1)) by
    obtain ⟨z', hz'⟩ := this
    constructor
    · exact h z
    · rintro rfl
      exact h z' hz' ▸ hz'
  obtain ⟨w, hw⟩ := exists_isMulSeq_tallyOf (M := FreeSemigroup Bool)
    (isTally_tallyOf_succ m) n
  obtain ⟨a, ha, hl⟩ := hw.exists_isLast
  use ofFreeSemigroup a
  and_intros
  · rwa [← ofFreeSemigroup_one, isTally_ofFreeSemigroup_iff]
  · exact isTally_tallyOf_add_one m
  · exact isTally_tallyOf_add_one n
  use ofFreeSemigroup w
  rw [← ofFreeSemigroup_tallyOf (m + 1), ← ofFreeSemigroup_tallyOf (n + 1),
    isEntry_ofFreeSemigroup_iff]
  exact ⟨(isMulTable_of_isMulSeq hw).ofFreeSemigroup, hl.isSubstring⟩

end IsProduct

section graph

lemma addGraph_tallyOf (m n : ℕ) : AddGraph (tallyOf (m + n) : M) (tallyOf m) (tallyOf n) := by
  match m, n with
  | m, 0 => exact .inl ⟨rfl, rfl⟩
  | 0, n + 1 => exact .inr <| .inl ⟨tallyOf_add_one_ne_zero n, rfl, by simp⟩
  | m + 1, n + 1 => exact .inr <| .inr <|
      ⟨tallyOf_add_one_ne_zero n, tallyOf_add_one_ne_zero m, (tallyOf_add_one_append m n).symm⟩

lemma mulGraph_tallyOf (m n : ℕ) : MulGraph (tallyOf (m * n) : M) (tallyOf m) (tallyOf n) := by
  have h0 : ¬IsTally (1 : M) 0 := fun h ↦ WTC.zero_ne_one <| h 0 isAtom_zero <| .refl 0
  match m, n with
  | m, 0 => simp [MulGraph, IsProduct, h0]
  | 0, n + 1 => simp [MulGraph, IsProduct, h0]
  | m + 1, n + 1 => simp [MulGraph, isProduct_tallyOf_iff]

lemma ltGraph_tallyOf_iff : LtGraph x (tallyOf n) ↔ ∃ i < n, x = tallyOf i := by
  constructor
  · rintro (⟨rfl, hn⟩ | ⟨v, h⟩)
    · use 0
      rcases n with _ | n <;> simp_all
    · exact exists_eq_tallyOf_of_tallyOf_eq_append h
  · rintro ⟨i, hi, rfl⟩
    match i, n, hi with
    | 0, n + 1, _ => exact .inl ⟨rfl, tallyOf_add_one_ne_zero n⟩
    | i + 1, n, hi =>
      right
      use tallyOf (n - (i + 1) - 1 + 1)
      rw [tallyOf_add_one_append]
      grind

end graph

section model

namespace arithmeticTranslation

/-- The constants, the operations and the order of the strings of a model of $\mathsf{WTC}$. -/
noncomputable abbrev oRingStructure : ORingStructure (arithmeticTranslation.Model M) where
  zero := ⟨0, arithmeticTranslation_dom 0⟩
  one := ⟨1, arithmeticTranslation_dom 1⟩
  add a b := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.add ![a, b]
  mul a b := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul ![a, b]
  lt a b := LtGraph (a : M) b

/-- The structure of the model of `arithmeticTranslation` is the one of `oRingStructure`. -/
lemma struc_eq : Model.struc arithmeticTranslation M = @Arithmetic.standardModel _ oRingStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      case zero | one =>
        symm
        apply Model.func_iff.mpr
        simp [arithmeticTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
        rfl
      case add | mul =>
        conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      · exact propext <| Model.eq_iff v
      · change (arithmeticTranslation.rel .lt).val (fun i ↦ (v i : M)) = LtGraph (v 0 : M) (v 1)
        rw [Matrix.fun_eq_vec_two (fun i ↦ (v i : M))]
        simp [arithmeticTranslation, Semiformula.Operator.val])

section

attribute [local instance] oRingStructure

variable {a b : arithmeticTranslation.Model M}

lemma val_add_eq_iff : ((a + b : arithmeticTranslation.Model M) : M) = z ↔ AddGraph z a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := M) Language.ORing.Func.add ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model M) i : M)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_addGraph] at h
  exact ⟨fun e ↦ e ▸ h, (existsUnique_addGraph _ _).unique h⟩

lemma val_mul_eq_iff : ((a * b : arithmeticTranslation.Model M) : M) = z ↔ MulGraph z a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := M) Language.ORing.Func.mul ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model M) i : M)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_mulGraph] at h
  exact ⟨fun e ↦ e ▸ h, (existsUnique_mulGraph _ _).unique h⟩

@[simp]
lemma val_numeral :
    ∀ n, ((ORingStructure.numeral n : arithmeticTranslation.Model M) : M) = tallyOf n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [ORingStructure.numeral, val_add_eq_iff, val_numeral (n + 1)]
    exact addGraph_tallyOf (n + 1) 1

end

/--
The strings of a model of $\mathsf{WTC}$ form a model of $\mathsf{R}_0$.
- [Hor12, §4, Corollary 4.9]
-/
instance : (arithmeticTranslation.Model M)↓[ℒₒᵣ] ⊧* 𝗥₀ := by
  rw [struc_eq]
  let := oRingStructure (M := M)
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case Ω₁ m n =>
    suffices (ORingStructure.numeral m + ORingStructure.numeral n : arithmeticTranslation.Model M) =
        ORingStructure.numeral (m + n) by simpa [models_iff] using this
    apply Model.ext
    simpa [val_add_eq_iff] using addGraph_tallyOf m n
  case Ω₂ m n =>
    suffices (ORingStructure.numeral m * ORingStructure.numeral n : arithmeticTranslation.Model M) =
        ORingStructure.numeral (m * n) by simpa [models_iff] using this
    apply Model.ext
    simpa [val_mul_eq_iff] using mulGraph_tallyOf m n
  case Ω₃ n =>
    suffices ∀ x : arithmeticTranslation.Model M, x < ORingStructure.numeral n ↔
        ∃ i < n, x = ORingStructure.numeral i by simpa [models_iff] using this
    intro x
    change LtGraph (x : M) _ ↔ _
    simp [ltGraph_tallyOf_iff, ← Model.val_inj_iff]

end arithmeticTranslation

end model

end WTC

/--
$\mathsf{WTC}$ interprets $\mathsf{R}_0$.
- [Hor12, §4, Corollary 4.9]
-/
instance : 𝗪𝗧𝗖 ⊳ 𝗥₀ where
  trln := WTC.arithmeticTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end arithmetic

section embedding

open LetterStructure

section initial

variable {α : Type} {M : Type*} [LetterStructure α M]

/--
`c` embeds the nonempty strings onto an initial part of `M`: if a concatenation is a standard
string, then so are its arguments.
-/
structure IsInitialEmbedding (c : FreeSemigroup α → M) : Prop where
  injective : Function.Injective c
  map_letter (a : α) : c (FreeSemigroup.of a) = ofLetter a
  map_append (u v : FreeSemigroup α) : c (u ++ v) = c u ++ c v
  exists_of_append_eq {x y : M} {w : FreeSemigroup α} (h : x ++ y = c w) :
    ∃ u v, x = c u ∧ y = c v

namespace IsInitialEmbedding

variable {c : FreeSemigroup α → M} (hc : IsInitialEmbedding c) {x y : M} {w : FreeSemigroup α}
include hc

lemma stringValue_eq (w : FreeSemigroup α) : stringValue ofLetter w = c w :=
  stringValue_eq_of_map_append hc.map_letter hc.map_append w

lemma exists_of_isSubstring (h : IsSubstring x (c w)) : ∃ u, x = c u :=
  h.of_forall_append (P := fun x ↦ ∃ u, x = c u)
    (fun _ _ ⟨_, h⟩ ↦ let ⟨u, v, hu, hv⟩ := hc.exists_of_append_eq h; ⟨⟨u, hu⟩, ⟨v, hv⟩⟩) ⟨w, rfl⟩

lemma exists_of_isSubstring_append (h : IsSubstring (x ++ y) (c w)) :
    ∃ u v, x = c u ∧ y = c v := by
  obtain ⟨w', hw'⟩ := hc.exists_of_isSubstring h
  exact hc.exists_of_append_eq hw'

lemma append_assoc_of_isSubstring {z : M}
    (h : IsSubstring (x ++ y ++ z) (c w) ∨ IsSubstring (x ++ (y ++ z)) (c w)) :
    x ++ y ++ z = x ++ (y ++ z) := by
  obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, x = c u ∧ y = c v ∧ z = c w := by
    rcases h with h | h
    · obtain ⟨a, e, ha, rfl⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use u, v, e
    · obtain ⟨u, a, rfl, ha⟩ := hc.exists_of_isSubstring_append h
      obtain ⟨v, e, rfl, rfl⟩ := hc.exists_of_append_eq ha
      use u, v, e
  simp only [← hc.map_append, append_eq_mul, mul_assoc]

lemma editor_of_isSubstring {s t : M} (h : x ++ y = s ++ t) (hw : IsSubstring (x ++ y) (c w)) :
    (x = s ∧ y = t) ∨ ∃ u, (x ++ u = s ∧ y = u ++ t) ∨ (x = s ++ u ∧ u ++ y = t) := by
  obtain ⟨a, b, rfl, rfl⟩ := hc.exists_of_isSubstring_append hw
  obtain ⟨d, e, rfl, rfl⟩ := hc.exists_of_append_eq (h.symm.trans (hc.map_append a b).symm)
  rw [← hc.map_append, ← hc.map_append, hc.injective.eq_iff] at h
  rcases FreeSemigroup.mul_eq_mul_iff.mp h with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp
  all_goals
    right
    use c u
    simp [← hc.map_append]

lemma append_ne_letter (a : α) : x ++ y ≠ ofLetter a := by
  rw [← hc.map_letter]
  intro h
  obtain ⟨u, v, rfl, rfl⟩ := hc.exists_of_append_eq h
  rw [← hc.map_append, hc.injective.eq_iff] at h
  exact FreeSemigroup.of_ne_mul a u v h.symm

/-- A structure with an initial embedding of the nonempty strings is a model of `𝗪𝗧𝗖[α]`. -/
lemma models_WTCLetters [Nonempty M] : M↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := ⟨by
  intro σ h
  cases h
  case equal hφ =>
    have : M↓[ℒ⌢[α]] ⊧* 𝗘𝗤 ℒ⌢[α] := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc w =>
    simpa [models_iff, hc.stringValue_eq]
      using fun x y z : M ↦ hc.append_assoc_of_isSubstring (x := x) (y := y) (z := z) (w := w)
  case editor w =>
    simpa [models_iff, hc.stringValue_eq]
      using fun x y s t : M ↦ hc.editor_of_isSubstring (x := x) (y := y) (s := s) (t := t) (w := w)
  case concatNeLetter a =>
    simpa [models_iff] using fun x y : M ↦ hc.append_ne_letter (x := x) (y := y) a
  case letterNeLetter a b h =>
    simpa [models_iff, ← hc.map_letter, hc.injective.eq_iff, FreeSemigroup.of] using h⟩

end IsInitialEmbedding

end initial

open DirectTranslation ORingStructure Arithmetic Arithmetic.R0

variable (α : Type) [Primcodable α]

variable {M : Type*} [ORingStructure M] {x y z : M}

/-- `z` is the concatenation of `x` and `y`, or `0` if there is none. -/
def ConcatGraph (z x y : M) : Prop :=
  IsValue₂ (FreeSemigroup.mulCode α) x y z ∨
    (z = 0 ∧ ∀ w, ¬IsValue₂ (FreeSemigroup.mulCode α) x y w)

/-- `z` is the concatenation of `x` and `y`, or `0` if there is none. -/
noncomputable def concatGraph : ArithmeticSemisentence 3 :=
  “z x y. !(isValue₂ (FreeSemigroup.mulCode α)) x y z ∨
    (z = 0 ∧ ∀ w, ¬!(isValue₂ (FreeSemigroup.mulCode α)) x y w)”

@[simp]
lemma eval_concatGraph : M ⊧/![z, x, y] (concatGraph α) ↔ ConcatGraph α z x y := by
  simp [concatGraph, ConcatGraph]

variable {α}

variable (α) in
lemma existsUnique_concatGraph (x y : M) : ∃! z, ConcatGraph α z x y :=
  existsUnique_isValue₂_or _ x y 0

section R0

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma concatGraph_numeral (u v : FreeSemigroup α) :
    ConcatGraph α (numeral (u * v).code : M) (numeral u.code) (numeral v.code) := by
  have h := isValue₂_numeral (M := M) (f := FreeSemigroup.mulCode α) (m := u.code) (n := v.code)
    FreeSemigroup.primrec₂_mulCode.to_comp
  rw [FreeSemigroup.mulCode_code] at h
  exact .inl <| h (u.code_le_code_mul_left v) (u.code_le_code_mul_right v)

lemma ConcatGraph.exists_of_numeral {w : FreeSemigroup α}
    (h : ConcatGraph α (numeral w.code) x y) :
    ∃ u v : FreeSemigroup α, x = numeral u.code ∧ y = numeral v.code := by
  rcases h with h | ⟨h, -⟩
  · obtain ⟨m, n, rfl, rfl, h'⟩ := h.exists_of_numeral FreeSemigroup.primrec₂_mulCode.to_comp
    obtain ⟨u, v, rfl, rfl⟩ := FreeSemigroup.eq_code_of_mulCode_ne_zero (h' ▸ w.code_ne_zero)
    use u, v
  · have : w.code = 0 := numeral_inj_iff (M := M).mp <| by simpa using h
    exact absurd this w.code_ne_zero

end R0

variable (α) in
/--
The translation of the language of concatenation with the letters `α` into $\mathsf{R}_0$: a
nonempty string is the numeral of its code.
-/
noncomputable def codeTranslation : DirectTranslation 𝗥₀ ℒ⌢[α] where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .letter a => ⟨“z. z = ↑(FreeSemigroup.code (FreeSemigroup.of a))”⟩
    | .concat => ⟨concatGraph α⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_concatGraph α (e 0) (e 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma codeTranslation_dom (x : M) : (codeTranslation α).Dom x := by
  simp [dom_iff, codeTranslation, Semiformula.Operator.val]

namespace codeTranslation

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

/-- The numeral of the code of a nonempty string. -/
def ofString (u : FreeSemigroup α) : (codeTranslation α).Model M := ⟨numeral u.code, by simp⟩

/-- The letters and the concatenation of the codes in `M`. -/
noncomputable abbrev letterStructure : LetterStructure α ((codeTranslation α).Model M) where
  ofLetter a := ofString (FreeSemigroup.of a)
  append x y := Tarski.Structure.func (L := ℒ⌢[α]) .concat ![x, y]

/-- The structure of the model of `codeTranslation` is the one of `letterStructure`. -/
lemma struc_eq : Model.struc (codeTranslation α) M = @lettersModel α _ letterStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [codeTranslation, Semiformula.Operator.val]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] letterStructure

lemma append_eq_iff {x y z : (codeTranslation α).Model M} :
    x ++ y = z ↔ ConcatGraph α (z : M) x y := by
  have := Model.func_iff (π := codeTranslation α) (M := M) (f := .concat) (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → (codeTranslation α).Model M) i : M)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_concatGraph] at this
  exact eq_comm.trans this

/-- The strings are embedded onto an initial part of the model of `codeTranslation`. -/
lemma isInitialEmbedding_ofString :
    IsInitialEmbedding (ofString : FreeSemigroup α → (codeTranslation α).Model M) where
  injective u v h := by simpa [ofString] using h
  map_letter _ := rfl
  map_append u v := (append_eq_iff.mpr <| concatGraph_numeral u v).symm
  exists_of_append_eq h := by
    obtain ⟨u, v, hu, hv⟩ := (append_eq_iff.mp h).exists_of_numeral
    use u, v, Model.ext hu, Model.ext hv

end

/-- The model of `codeTranslation` satisfies `𝗪𝗧𝗖[α]`. -/
instance : ((codeTranslation α).Model M)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := by
  rw [struc_eq]
  let := letterStructure (α := α) (M := M)
  exact isInitialEmbedding_ofString.models_WTCLetters

end codeTranslation

/--
$\mathsf{R}_0$ interprets the weak theory of concatenation with the letters `α`.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗧𝗖[α] where
  trln := codeTranslation α
  interpret_theory φ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{R}_0$ interprets $\mathsf{WTC}$.
- [Hor11, §3, Theorem 3.9]
-/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗧𝗖 :=
  DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖[Bool] ⊳ 𝗪𝗧𝗖) inferInstance

end embedding

/--
$\mathsf{WTC}$ and $\mathsf{R}_0$ are mutually interpretable.
- [Hor11, §3, Theorem 3.15]
- [Hor12, §4, Theorem 4.1]
-/
noncomputable instance : 𝗪𝗧𝗖 ⋈ 𝗥₀ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{WTC}$ is essentially undecidable.
- [Hor11, §3, Corollary 3.17]
- [Hor12, §4, Corollary 4.11]
-/
instance : (𝗪𝗧𝗖 : ConcatenationTheory).EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀)

instance {α : Type} [Nonempty α] : (FreeSemigroup α)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] :=
  IsInitialEmbedding.models_WTCLetters (c := id)
    { injective := Function.injective_id
      map_letter := fun _ ↦ rfl
      map_append := fun _ _ ↦ rfl
      exists_of_append_eq := fun {x y} _ _ ↦ ⟨x, y, rfl, rfl⟩ }

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := models_WTC_concatenationStructure Bool.false_ne_true

instance : Entailment.Consistent 𝗪𝗧𝗖 :=
  let : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

/--
$\mathsf{WTC}$ is undecidable.
- [Hor11, §3, Corollary 3.17]
-/
theorem WTC.undecidable : Entailment.Undecidable 𝗪𝗧𝗖 :=
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖

section letters

variable {α β : Type} [Primcodable α] [Nontrivial α] [Primcodable β] [Nontrivial β]

/--
The weak theory of concatenation with at least two letters and $\mathsf{R}_0$ are mutually
interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗥₀ where
  r := DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀) inferInstance
  l := inferInstance

/--
The weak theory of concatenation with at least two letters and $\mathsf{WTC}$ are mutually
interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖 where
  r := inferInstance
  l := DirectInterpretation.comp (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖[α]) inferInstance

/--
Any two weak theories of concatenation with at least two letters are mutually interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖[β] :=
  MutualDirectInterpretation.trans (inferInstance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖)
    (MutualDirectInterpretation.symm inferInstance)

/--
For all $m, n \ge 2$, $\mathsf{WTC}_m$ and $\mathsf{WTC}_n$ are mutually interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
noncomputable abbrev WTCLetters.mutualInterpretation {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    𝗪𝗧𝗖[Fin m] ⋈ 𝗪𝗧𝗖[Fin n] :=
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  inferInstance

instance {α : Type} [Nonempty α] : Entailment.Consistent 𝗪𝗧𝗖[α] :=
  let : (FreeSemigroup α)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

variable {n : ℕ}

/--
For every $n \ge 2$, $\mathsf{WTC}_n$ is essentially undecidable.
- [Hor11, §3, Corollary 3.17, Theorem 3.18]
- [Hor12, §4, Corollary 4.11, Theorem 4.13]
-/
theorem WTCLetters.essentiallyUndecidable (hn : 2 ≤ n) : 𝗪𝗧𝗖[Fin n].EssentiallyUndecidable :=
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖[Fin n] ⋈ 𝗥₀).r

/--
For every $n \ge 2$, $\mathsf{WTC}_n$ is undecidable.
- [Hor11, §3, Corollary 3.17, Theorem 3.18]
- [Hor12, §4, Corollary 4.11, Theorem 4.13]
-/
theorem WTCLetters.undecidable (hn : 2 ≤ n) : Entailment.Undecidable 𝗪𝗧𝗖[Fin n] :=
  have := essentiallyUndecidable hn
  have : Nonempty (Fin n) := ⟨⟨0, by lia⟩⟩
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖[Fin n]

end letters

section interpretability

open Arithmetic

/--
$\mathsf{WTC}$ is locally finitely satisfiable.
- [Hor11, §3, Corollary 3.16]
- [Hor12, §4, Theorem 4.10]
-/
theorem WTC.locallyFinitelySatisfiable :
    (𝗪𝗧𝗖 : ConcatenationTheory).LocallyFinitelySatisfiable :=
  (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖).locallyFinitelySatisfiable R0.locallyFinitelySatisfiable

theorem WTC.notInterprets_Q : 𝗪𝗧𝗖 ⋫ 𝗤 := R0.notInterprets_Q.of_left (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖)

/--
$\mathsf{WTC}$ does not interpret $\mathsf{TC}$.
- [Hor11, §3, Corollary 3.17]
- [Hor12, §4, Corollary 4.11]
-/
theorem WTC.notInterprets_TC : 𝗪𝗧𝗖 ⋫ 𝗧𝗖 :=
  R0.notInterprets_TC.of_left (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖)

variable {L : Language} [L.Eq] [L.Finite] [L.Encodable] [L.Primcodable] {T : Theory L} [𝗘𝗤 L ⪯ T]

/--
A recursively enumerable theory of a finite language is interpretable in $\mathsf{WTC}$ if and only
if it is locally finitely satisfiable.
- [Hor11, §3, Corollary 3.16]
- [Hor12, §4, Corollary 4.12]
- [HH14, Theorem 2]
-/
theorem WTC.nonempty_interpretation_iff_locallyFinitelySatisfiable (hT : REPred (· ∈ T)) :
    Nonempty (𝗪𝗧𝗖 ⊳ T) ↔ T.LocallyFinitelySatisfiable :=
  Iff.trans ⟨fun ⟨π⟩ ↦ ⟨π.comp (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖)⟩,
      fun ⟨π⟩ ↦ ⟨π.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀)⟩⟩
    (R0.nonempty_interpretation_iff_locallyFinitelySatisfiable hT)

/--
A recursively enumerable theory of a finite language is not interpretable in $\mathsf{WTC}$ if and
only if it is not locally finitely satisfiable.
- [Hor12, §4, Corollary 4.12]
-/
theorem WTC.notInterprets_iff_not_locallyFinitelySatisfiable (hT : REPred (· ∈ T)) :
    𝗪𝗧𝗖 ⋫ T ↔ ¬T.LocallyFinitelySatisfiable :=
  notInterprets_iff.trans (nonempty_interpretation_iff_locallyFinitelySatisfiable hT).not

end interpretability

/--
Are $\mathsf{R}$ and $\mathsf{WTC}$,
which are mutually interpretable by the cited theorem, bi-interpretable?
- [HH14, Theorem 1]
-/
open_problem R_biInterpretable_WTC := Nonempty (BiInterpretation 𝗥 𝗪𝗧𝗖)

/--
Are $\mathsf{R}$ and $\mathsf{WTC}$,
which are mutually interpretable by the cited theorem, definitionally equivalent?
- [HH14, Theorem 1]
-/
open_problem R_definitionallyEquivalent_WTC := Nonempty (DefinitionalEquivalence 𝗥 𝗪𝗧𝗖)

end FFL.FirstOrder.Concatenation

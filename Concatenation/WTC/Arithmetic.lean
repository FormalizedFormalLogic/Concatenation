module

public import Concatenation.TC.Representation
public import Concatenation.WTC.Standard

/-!
# The arithmetic translation of $\mathsf{WTC}$

The translation of the language of arithmetic into $\mathsf{WTC}$ that interprets $\mathsf{R}_0$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

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

lemma exists_isMulSeq_tallyOf (hx : IsTally 1 x) : ∀ n, ∃ z, IsMulSeq x (tallyOf (n + 1)) z
  | 0 => (existsUnique_isMulSeq_one hx).exists
  | n + 1 => by
    obtain ⟨z, hz⟩ := exists_isMulSeq_tallyOf hx n
    obtain ⟨w, hw, hl⟩ := hz.exists_isLast
    exact ⟨_, hz.extend hw hl⟩

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
    use u, v
    and_intros
    · exact hu
    · exact hv
    · exact hu''
    · exact hv''
    · have h₁ : 0 ++ 0 ++ pairOf u v ++ (0 ++ 0) = 0 ++ 0 ++ pairOf u v ++ 0 ++ 0 := by
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
  rcases n with _ | n
  · exact WTC.zero_ne_one.symm
  · exact append_ne_zero _ _

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
  · use ofFreeSemigroup w
    rw [← ofFreeSemigroup_tallyOf (m + 1), ← ofFreeSemigroup_tallyOf (n + 1),
      isEntry_ofFreeSemigroup_iff]
    and_intros
    · exact (isMulTable_of_isMulSeq hw).ofFreeSemigroup
    · exact hl.isSubstring

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
      rcases n with _ | n
      · exact absurd rfl hn
      · simp
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
      · symm
        apply Model.func_iff.mpr
        simp [arithmeticTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
        rfl
      · symm
        apply Model.func_iff.mpr
        simp [arithmeticTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl
      · conv_lhs => rw [Matrix.fun_eq_vec_two v]
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

end FFL.FirstOrder.Concatenation

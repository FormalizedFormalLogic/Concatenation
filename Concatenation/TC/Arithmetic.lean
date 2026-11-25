module

public import Concatenation.TC.MulSeq
public import Foundation.FirstOrder.Arithmetic.Q.Basic

/-!
# The arithmetic translation of $\mathsf{TC}^+$

The translation of the language of arithmetic into $\mathsf{TC}^+$ on the `1`-tallies with `0`
and the ideal element `0 0`, which interprets $\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

variable {M : Type*} [ConcatenationStructure M] {x y z z' : M}

/--
`x` is a number: a `1`-tally, the zero `0`, or the ideal element `0 0`.
- [Gan09, §1, Definition 2]
- [Sve09, §3]
-/
def IsNumber (x : M) : Prop := IsTally 1 x ∨ x = 0 ∨ x = 0 ++ 0

/--
`z` is the sum of `x` and `y`: the concatenation of `1`-tallies, with `0` neutral and `0 0`
absorbing.
- [Gan09, §1, Definition 2]
- [Sve09, §3]
-/
def AddGraph (z x y : M) : Prop :=
  ((x = 0 ++ 0 ∨ y = 0 ++ 0) ∧ z = 0 ++ 0) ∨ (x = 0 ∧ y ≠ 0 ++ 0 ∧ z = y) ∨
    (y = 0 ∧ x ≠ 0 ++ 0 ∧ z = x) ∨ (IsTally 1 x ∧ IsTally 1 y ∧ z = x ++ y)

/--
`z` is the product of `x` and `y`: `0` if `y` is `0`; `0 0` if `y` is not `0` and one of `x` and `y`
is `0 0`; `0` if `x` is `0` and `y` is a `1`-tally; for `1`-tallies `x` and `y`, the first component
of the last member of the multiplication sequence for `x` and `y` if there is exactly one, and `0 0`
otherwise.
- [Gan09, §1, Definition 2]
- [Sve09, §3]
-/
def MulGraph (z x y : M) : Prop :=
  (y = 0 ∧ z = 0) ∨ (y ≠ 0 ∧ (x = 0 ++ 0 ∨ y = 0 ++ 0) ∧ z = 0 ++ 0) ∨
    (x = 0 ∧ IsTally 1 y ∧ z = 0) ∨
    (IsTally 1 x ∧ IsTally 1 y ∧
      (((∃! r, IsMulSeq x y r) ∧ IsTally 1 z ∧ ∃ r, IsMulSeq x y r ∧ IsLast (pairOf z y) r) ∨
        (¬(∃! r, IsMulSeq x y r) ∧ z = 0 ++ 0)))

/-- `x` is less than `y`: the translation of `∃ c, x + (c + 1) = y`. -/
def LtGraph (x y : M) : Prop := ∃ c, IsNumber c ∧ ∃ d, AddGraph d c 1 ∧ AddGraph y x d

/-- `x` is a number. -/
def isNumber : Semisentence ℒ⌢ 1 :=
  “x. !isTally !!(op(1).const) x ∨ x = !!(op(0).const) ∨
    x = !!(op(0).const) ⌢ !!(op(0).const)”

/-- `z` is the sum of `x` and `y`. -/
def addGraph : Semisentence ℒ⌢ 3 :=
  “z x y. ((x = !!(op(0).const) ⌢ !!(op(0).const) ∨ y = !!(op(0).const) ⌢ !!(op(0).const)) ∧
      z = !!(op(0).const) ⌢ !!(op(0).const)) ∨
    (x = !!(op(0).const) ∧ y ≠ !!(op(0).const) ⌢ !!(op(0).const) ∧ z = y) ∨
    (y = !!(op(0).const) ∧ x ≠ !!(op(0).const) ⌢ !!(op(0).const) ∧ z = x) ∨
    (!isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧ z = x ⌢ y)”

/-- `z` is the product of `x` and `y`. -/
def mulGraph : Semisentence ℒ⌢ 3 :=
  “z x y. (y = !!(op(0).const) ∧ z = !!(op(0).const)) ∨
    (y ≠ !!(op(0).const) ∧
      (x = !!(op(0).const) ⌢ !!(op(0).const) ∨ y = !!(op(0).const) ⌢ !!(op(0).const)) ∧
      z = !!(op(0).const) ⌢ !!(op(0).const)) ∨
    (x = !!(op(0).const) ∧ !isTally !!(op(1).const) y ∧ z = !!(op(0).const)) ∨
    (!isTally !!(op(1).const) x ∧ !isTally !!(op(1).const) y ∧
      (((∃! r, !isMulSeq x y r) ∧ !isTally !!(op(1).const) z ∧
          ∃ r, !isMulSeq x y r ∧ !isLast (z ⌢ !!(op(0).const) ⌢ y) r) ∨
        (¬(∃! r, !isMulSeq x y r) ∧ z = !!(op(0).const) ⌢ !!(op(0).const))))”

/-- `x` is less than `y`. -/
def ltGraph : Semisentence ℒ⌢ 2 :=
  “x y. ∃ c, !isNumber c ∧ ∃ d, !addGraph d c !!(op(1).const) ∧ !addGraph y x d”

@[simp]
lemma eval_isNumber : M ⊧/![x] isNumber ↔ IsNumber x := by simp [isNumber, IsNumber]

@[simp]
lemma eval_addGraph : M ⊧/![z, x, y] addGraph ↔ AddGraph z x y := by simp [addGraph, AddGraph]

@[simp]
lemma eval_mulGraph : M ⊧/![z, x, y] mulGraph ↔ MulGraph z x y := by
  simp [mulGraph, MulGraph, pairOf]

@[simp]
lemma eval_ltGraph : M ⊧/![x, y] ltGraph ↔ LtGraph x y := by simp [ltGraph, LtGraph]

lemma isNumber_zero : IsNumber (0 : M) := Or.inr <| Or.inl rfl

lemma isNumber_zero_append_zero : IsNumber (0 ++ 0 : M) := Or.inr <| Or.inr rfl

lemma IsTally.isNumber (hx : IsTally 1 x) : IsNumber x := Or.inl hx

lemma exists_addGraph (hx : IsNumber x) (hy : IsNumber y) : ∃ z, AddGraph z x y := by
  by_cases hxy : x = 0 ++ 0 ∨ y = 0 ++ 0
  · use 0 ++ 0
    exact Or.inl ⟨hxy, rfl⟩
  push Not at hxy
  rcases hx with hx | rfl | rfl
  · rcases hy with hy | rfl | rfl
    · use x ++ y
      exact Or.inr <| Or.inr <| Or.inr ⟨hx, hy, rfl⟩
    · use x
      exact Or.inr <| Or.inr <| Or.inl ⟨rfl, hxy.1, rfl⟩
    · exact absurd rfl hxy.2
  · use y
    exact Or.inr <| Or.inl ⟨rfl, hxy.2, rfl⟩
  · exact absurd rfl hxy.1

lemma MulGraph.isNumber (h : MulGraph z x y) : IsNumber z := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ⟨-, hz, -⟩ | ⟨-, rfl⟩⟩
  · exact isNumber_zero
  · exact isNumber_zero_append_zero
  · exact isNumber_zero
  · exact hz.isNumber
  · exact isNumber_zero_append_zero

lemma exists_mulGraph (hx : IsNumber x) (hy : IsNumber y) : ∃ z, MulGraph z x y := by
  by_cases hy0 : y = 0
  · use 0
    exact Or.inl ⟨hy0, rfl⟩
  by_cases hxy : x = 0 ++ 0 ∨ y = 0 ++ 0
  · use 0 ++ 0
    exact Or.inr <| Or.inl ⟨hy0, hxy, rfl⟩
  push Not at hxy
  replace hy : IsTally 1 y := by rcases hy with hy | hy | hy <;> simp_all
  rcases hx with hx | rfl | hx
  · by_cases hr : ∃! r, IsMulSeq x y r
    · obtain ⟨r, hr'⟩ := hr.exists
      obtain ⟨w, hw, hwr⟩ := hr'.2.2.2.2.1
      use w
      exact Or.inr <| Or.inr <| Or.inr ⟨hx, hy, Or.inl ⟨hr, hw, r, hr', hwr⟩⟩
    · use 0 ++ 0
      exact Or.inr <| Or.inr <| Or.inr ⟨hx, hy, Or.inr ⟨hr, rfl⟩⟩
  · use 0
    exact Or.inr <| Or.inr <| Or.inl ⟨rfl, hy, rfl⟩
  · exact absurd hx hxy.1

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma isNumber_one : IsNumber (1 : M) := Or.inl isTally_one_one

lemma AddGraph.unique (h : AddGraph z x y) (h' : AddGraph z' x y) : z = z' := by
  have h00 := zero_ne_append (0 : M) 0
  rcases h with ⟨hxy, rfl⟩ | ⟨rfl, hy, rfl⟩ | ⟨rfl, hx, rfl⟩ | ⟨hx, hy, rfl⟩ <;>
    rcases h' with ⟨hxy', rfl⟩ | ⟨hx', hy', rfl⟩ | ⟨hy', hx', rfl⟩ | ⟨hx', hy', rfl⟩
  all_goals first
    | rfl
    | grind [IsTally.ne_zero, IsTally.ne_zero_append_zero]

lemma AddGraph.isNumber (hx : IsNumber x) (hy : IsNumber y) (h : AddGraph z x y) : IsNumber z := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨hx, hy, rfl⟩
  · exact isNumber_zero_append_zero
  · exact hy
  · exact hx
  · exact (hx.append hy).isNumber

lemma existsUnique_addGraph (hx : IsNumber x) (hy : IsNumber y) :
    ∃! z, IsNumber z ∧ AddGraph z x y := by
  obtain ⟨z, hz⟩ := exists_addGraph hx hy
  use z
  and_intros
  · exact hz.isNumber hx hy
  · exact hz
  · exact fun z' hz' ↦ hz'.2.unique hz

end TC

section TCPlus

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

lemma MulGraph.unique (h : MulGraph z x y) (h' : MulGraph z' x y) : z = z' := by
  have h00 := zero_ne_append (0 : M) 0
  rcases h with ⟨hy, rfl⟩ | ⟨hy, hxy, rfl⟩ | ⟨hx, hy, rfl⟩ |
      ⟨hx, hy, ⟨hr, hz, r, hrm, hzr⟩ | ⟨hr, rfl⟩⟩ <;>
    rcases h' with ⟨hy', rfl⟩ | ⟨hy', hxy', rfl⟩ | ⟨hx', hy', rfl⟩ |
      ⟨hx', hy', ⟨hr', hz', r', hrm', hzr'⟩ | ⟨hr', rfl⟩⟩
  all_goals first
    | rfl
    | (obtain rfl := hr.unique hrm hrm'; exact (hzr.pairOf_inj hz hy hz' hy hzr').1)
    | grind [IsTally.ne_zero, IsTally.ne_zero_append_zero, not_isTally_one_zero]

lemma existsUnique_mulGraph (hx : IsNumber x) (hy : IsNumber y) :
    ∃! z, IsNumber z ∧ MulGraph z x y := by
  obtain ⟨z, hz⟩ := exists_mulGraph hx hy
  use z
  and_intros
  · exact hz.isNumber
  · exact hz
  · exact fun z' hz' ↦ hz'.2.unique hz

end TCPlus

/--
The translation of the language of arithmetic into $\mathsf{TC}^+$: the numbers are the
`1`-tallies, `0` and `0 0`; `0` is `0`, `1` is `1`, `+`, `*` and `<` are `AddGraph`, `MulGraph` and
`LtGraph`.
- [Gan09, §1, Definition 2]
- [Sve09, §3]
-/
def arithmeticTranslation : DirectTranslation 𝗧𝗖⁺ ℒₒᵣ where
  domain := ⟨isNumber⟩
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
    simpa [Semiformula.Operator.val] using isNumber_zero
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsNumber (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, IsNumber y ∧ y = 0 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 0
      simp [isNumber_zero]
    · suffices ∃! y : M, IsNumber y ∧ y = 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 1
      simp [isNumber_one]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_addGraph (he 0) (he 1)
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_mulGraph (he 0) (he 1)
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma arithmeticTranslation_dom_iff : arithmeticTranslation.Dom x ↔ IsNumber x := by
  simp [dom_iff, arithmeticTranslation, Semiformula.Operator.val]

lemma arithmeticTranslation.isNumber_val (a : arithmeticTranslation.Model M) : IsNumber (a : M) :=
  arithmeticTranslation_dom_iff.mp a.dom

section model

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺]

namespace arithmeticTranslation

/-- The constants, the operations and the order of the numbers of a model of $\mathsf{TC}^+$. -/
noncomputable abbrev oRingStructure : ORingStructure (arithmeticTranslation.Model M) where
  zero := ⟨0, arithmeticTranslation_dom_iff.mpr isNumber_zero⟩
  one := ⟨1, arithmeticTranslation_dom_iff.mpr isNumber_one⟩
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

@[simp]
lemma val_zero : ((0 : arithmeticTranslation.Model M) : M) = 0 := rfl

@[simp]
lemma val_one : ((1 : arithmeticTranslation.Model M) : M) = 1 := rfl

lemma addGraph_val_add (a b : arithmeticTranslation.Model M) :
    AddGraph ((a + b : arithmeticTranslation.Model M) : M) a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := M) Language.ORing.Func.add ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model M) i : M)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_addGraph] at h
  exact h

lemma mulGraph_val_mul (a b : arithmeticTranslation.Model M) :
    MulGraph ((a * b : arithmeticTranslation.Model M) : M) a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := M) Language.ORing.Func.mul ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model M) i : M)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_mulGraph] at h
  exact h

lemma val_add_eq_iff : ((a + b : arithmeticTranslation.Model M) : M) = z ↔ AddGraph z a b :=
  ⟨fun h ↦ h ▸ addGraph_val_add a b, (addGraph_val_add a b).unique⟩

lemma val_mul_eq_iff : ((a * b : arithmeticTranslation.Model M) : M) = z ↔ MulGraph z a b :=
  ⟨fun h ↦ h ▸ mulGraph_val_mul a b, (mulGraph_val_mul a b).unique⟩

lemma val_add_of_isTally (ha : IsTally 1 (a : M)) (hb : IsTally 1 (b : M)) :
    ((a + b : arithmeticTranslation.Model M) : M) = a ++ b :=
  val_add_eq_iff.mpr <| Or.inr <| Or.inr <| Or.inr ⟨ha, hb, rfl⟩

lemma isTally_val_add (ha : IsTally 1 (a : M)) (hb : IsTally 1 (b : M)) :
    IsTally 1 ((a + b : arithmeticTranslation.Model M) : M) :=
  val_add_of_isTally ha hb ▸ ha.append hb

protected lemma add_zero (a : arithmeticTranslation.Model M) : a + 0 = a := by
  apply Model.ext
  apply val_add_eq_iff.mpr
  by_cases ha : (a : M) = 0 ++ 0
  · exact Or.inl ⟨Or.inl ha, ha⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨rfl, ha, rfl⟩

protected lemma zero_add (a : arithmeticTranslation.Model M) : 0 + a = a := by
  apply Model.ext
  apply val_add_eq_iff.mpr
  by_cases ha : (a : M) = 0 ++ 0
  · exact Or.inl ⟨Or.inr ha, ha⟩
  · exact Or.inr <| Or.inl ⟨rfl, ha, rfl⟩

lemma add_eq_left_of_val_eq_zero_append_zero (ha : (a : M) = 0 ++ 0)
    (b : arithmeticTranslation.Model M) : a + b = a :=
  Model.ext <| val_add_eq_iff.mpr <| Or.inl ⟨Or.inl ha, ha⟩

lemma add_eq_right_of_val_eq_zero_append_zero (hb : (b : M) = 0 ++ 0)
    (a : arithmeticTranslation.Model M) : a + b = b :=
  Model.ext <| val_add_eq_iff.mpr <| Or.inl ⟨Or.inr hb, hb⟩

/--
The successor of a number: `x ↦ x 1` on the `1`-tallies, `0 ↦ 1`, and `0 0 ↦ 0 0`.
- [Sve09, §3]
-/
lemma val_add_one_cases (a : arithmeticTranslation.Model M) :
    (IsTally 1 (a : M) ∧ ((a + 1 : arithmeticTranslation.Model M) : M) = a ++ 1) ∨
      ((a : M) = 0 ∧ ((a + 1 : arithmeticTranslation.Model M) : M) = 1) ∨
      ((a : M) = 0 ++ 0 ∧ ((a + 1 : arithmeticTranslation.Model M) : M) = 0 ++ 0) := by
  rcases isNumber_val a with ha | ha | ha
  · exact Or.inl ⟨ha, val_add_of_isTally ha isTally_one_one⟩
  · obtain rfl : a = 0 := Model.ext ha
    exact Or.inr <| Or.inl ⟨rfl, by rw [arithmeticTranslation.zero_add]; rfl⟩
  · exact Or.inr <| Or.inr ⟨ha, by rw [add_eq_left_of_val_eq_zero_append_zero ha]; exact ha⟩

protected lemma mul_zero (a : arithmeticTranslation.Model M) : a * 0 = 0 :=
  Model.ext <| val_mul_eq_iff.mpr <| Or.inl ⟨rfl, rfl⟩

lemma zero_mul_of_isTally (hb : IsTally 1 (b : M)) : 0 * b = 0 :=
  Model.ext <| val_mul_eq_iff.mpr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, hb, rfl⟩

lemma mul_eq_left_of_val_eq_zero_append_zero (ha : (a : M) = 0 ++ 0) (hb : (b : M) ≠ 0) :
    a * b = a :=
  Model.ext <| val_mul_eq_iff.mpr <| Or.inr <| Or.inl ⟨hb, Or.inl ha, ha⟩

lemma mul_eq_right_of_val_eq_zero_append_zero (hb : (b : M) = 0 ++ 0)
    (a : arithmeticTranslation.Model M) : a * b = b :=
  Model.ext <| val_mul_eq_iff.mpr <| Or.inr <| Or.inl
    ⟨hb ▸ (zero_ne_append 0 0).symm, Or.inr hb, hb⟩

protected lemma mul_one (a : arithmeticTranslation.Model M) : a * 1 = a := by
  rcases isNumber_val a with ha | ha | ha
  · apply Model.ext
    apply val_mul_eq_iff.mpr
    exact Or.inr <| Or.inr <| Or.inr ⟨ha, isTally_one_one, Or.inl
      ⟨existsUnique_isMulSeq_one ha, ha, _, (isMulSeq_one_iff ha).mpr rfl, IsEndSegment.refl _⟩⟩
  · obtain rfl : a = 0 := Model.ext ha
    exact zero_mul_of_isTally isTally_one_one
  · exact mul_eq_left_of_val_eq_zero_append_zero ha isTally_one_one.ne_zero

lemma mul_add_one_of_isTally (ha : IsTally 1 (a : M)) (hb : IsTally 1 (b : M)) :
    a * (b + 1) = a * b + a := by
  have hb1 := val_add_of_isTally hb (b := 1) isTally_one_one
  rw [val_one] at hb1
  apply Model.ext
  rw [val_mul_eq_iff, hb1]
  rcases mulGraph_val_mul a b with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ |
      ⟨-, -, ⟨h, hz, r, hr, hl⟩ | ⟨h, hz⟩⟩
  · exact absurd h hb.ne_zero
  · exact absurd h <| not_or_intro ha.ne_zero_append_zero hb.ne_zero_append_zero
  · exact absurd h ha.ne_zero
  · rw [val_add_of_isTally hz ha]
    exact Or.inr <| Or.inr <| Or.inr ⟨ha, hb.append_one, Or.inl
      ⟨(existsUnique_isMulSeq_succ_iff ha).mpr h, hz.append ha, _, hr.extend hz hl,
        hr.isLast_extend⟩⟩
  · rw [add_eq_left_of_val_eq_zero_append_zero hz]
    exact Or.inr <| Or.inr <| Or.inr ⟨ha, hb.append_one, Or.inr
      ⟨(existsUnique_isMulSeq_succ_iff ha).not.mpr h, hz⟩⟩

lemma add_one_ne_zero (a : arithmeticTranslation.Model M) : a + 1 ≠ 0 := by
  intro h
  rw [← Model.val_inj_iff] at h
  rcases val_add_one_cases a with ⟨-, ha⟩ | ⟨-, ha⟩ | ⟨-, ha⟩ <;> rw [ha] at h
  all_goals first
    | exact (zero_ne_append _ _).symm h
    | exact Concatenation.zero_ne_one h.symm

lemma add_one_inj (h : a + 1 = b + 1) : a = b := by
  rw [← Model.val_inj_iff] at h ⊢
  rcases val_add_one_cases a with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
    rcases val_add_one_cases b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
    rw [ha', hb'] at h
  all_goals first
    | exact ha.trans hb.symm
    | exact isAtom_one.append_right_cancel h
    | exact absurd h (one_ne_append _ _)
    | exact absurd h.symm (one_ne_append _ _)
    | exact absurd h (append_one_ne_zero_append_zero _)
    | exact absurd h.symm (append_one_ne_zero_append_zero _)

lemma eq_zero_or_exists_eq_add_one (a : arithmeticTranslation.Model M) :
    a = 0 ∨ ∃ b, a = b + 1 := by
  rcases isNumber_val a with ha | ha | ha
  · right
    rcases ha.eq_or_exists_append with ha' | ⟨x, hx, ha'⟩
    · use 0
      rw [arithmeticTranslation.zero_add]
      exact Model.ext ha'
    · use ⟨x, arithmeticTranslation_dom_iff.mpr hx.isNumber⟩
      apply Model.ext
      rw [val_add_of_isTally hx isTally_one_one]
      exact ha'
  · exact Or.inl <| Model.ext ha
  · right
    use a
    exact (add_eq_left_of_val_eq_zero_append_zero ha 1).symm

lemma add_add_one (a b : arithmeticTranslation.Model M) : a + (b + 1) = a + b + 1 := by
  rcases isNumber_val a with ha | ha | ha
  · rcases isNumber_val b with hb | hb | hb
    · apply Model.ext
      rw [val_add_of_isTally ha (isTally_val_add hb (b := 1) isTally_one_one),
        val_add_of_isTally (isTally_val_add ha hb) isTally_one_one,
        val_add_of_isTally hb isTally_one_one, val_add_of_isTally ha hb, Concatenation.append_assoc]
    · obtain rfl : b = 0 := Model.ext hb
      rw [arithmeticTranslation.zero_add, arithmeticTranslation.add_zero]
    · simp only [add_eq_left_of_val_eq_zero_append_zero hb,
        add_eq_right_of_val_eq_zero_append_zero hb]
  · obtain rfl : a = 0 := Model.ext ha
    simp only [arithmeticTranslation.zero_add]
  · simp only [add_eq_left_of_val_eq_zero_append_zero ha]

/--
The numbers satisfy $a \cdot (b + 1) = a \cdot b + a$.
- [Sve09, §3]
- [Gan09, §3, Theorem 4]
-/
lemma mul_add_one (a b : arithmeticTranslation.Model M) : a * (b + 1) = a * b + a := by
  rcases isNumber_val b with hb | hb | hb
  · have hb1 := isTally_val_add hb (b := 1) isTally_one_one
    rcases isNumber_val a with ha | ha | ha
    · exact mul_add_one_of_isTally ha hb
    · obtain rfl : a = 0 := Model.ext ha
      rw [zero_mul_of_isTally hb1, zero_mul_of_isTally hb, arithmeticTranslation.add_zero]
    · simp only [mul_eq_left_of_val_eq_zero_append_zero ha hb1.ne_zero,
        mul_eq_left_of_val_eq_zero_append_zero ha hb.ne_zero,
        add_eq_left_of_val_eq_zero_append_zero ha]
  · obtain rfl : b = 0 := Model.ext hb
    rw [arithmeticTranslation.mul_zero, arithmeticTranslation.zero_add,
      arithmeticTranslation.zero_add, arithmeticTranslation.mul_one]
  · simp only [add_eq_left_of_val_eq_zero_append_zero hb,
      mul_eq_right_of_val_eq_zero_append_zero hb]

lemma lt_iff : a < b ↔ ∃ c, a + (c + 1) = b := by
  change LtGraph (a : M) b ↔ _
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    have hc' : arithmeticTranslation.Dom c := arithmeticTranslation_dom_iff.mpr hc
    use ⟨c, hc'⟩
    apply Model.ext
    rw [val_add_eq_iff, (val_add_eq_iff (a := ⟨c, hc'⟩) (b := 1)).mpr hd]
    exact h
  · rintro ⟨c, rfl⟩
    use c
    and_intros
    · exact isNumber_val c
    · use (c + 1 : arithmeticTranslation.Model M)
      and_intros
      · exact addGraph_val_add c 1
      · exact addGraph_val_add a (c + 1)

end

/--
The numbers of a model of $\mathsf{TC}^+$ form a model of $\mathsf{Q}$.
- [Sve09, §3]
- [Gan09, §3, Theorem 4]
-/
instance : (arithmeticTranslation.Model M)↓[ℒₒᵣ] ⊧* 𝗤 := by
  rw [struc_eq]
  let := oRingStructure (M := M)
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case succNeZero => simpa [models_iff] using add_one_ne_zero (M := M)
  case succInj => simpa [models_iff] using fun a b ↦ add_one_inj (M := M) (a := a) (b := b)
  case zeroOrSucc => simpa [models_iff] using eq_zero_or_exists_eq_add_one (M := M)
  case addZero => simpa [models_iff] using arithmeticTranslation.add_zero (M := M)
  case addSucc => simpa [models_iff] using add_add_one (M := M)
  case mulZero => simpa [models_iff] using arithmeticTranslation.mul_zero (M := M)
  case mulSucc => simpa [models_iff] using mul_add_one (M := M)
  case ltDef => simpa [models_iff] using fun a b ↦ lt_iff (M := M) (a := a) (b := b)

end arithmeticTranslation

end model

/--
$\mathsf{TC}^+$ interprets $\mathsf{Q}$.
- [Sve09, §3]
- [Gan09, §3, Theorem 4]
-/
instance : 𝗧𝗖⁺ ⊳ 𝗤 where
  trln := arithmeticTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

/--
$\mathsf{TC}$ interprets $\mathsf{Q}$.
- [Gan09, §3, Theorem 5]
- [Sve09, §3]
-/
instance : 𝗧𝗖 ⊳ 𝗤 :=
  DirectInterpretation.comp (inferInstance : 𝗧𝗖⁺ ⊳ 𝗤) (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖⁺)

end FFL.FirstOrder.Concatenation

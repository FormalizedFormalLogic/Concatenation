module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Seq.Basic
public import Foundation.FirstOrder.Arithmetic.R0.Basic

/-!
# $\mathsf{WSeq}$ interprets $\mathsf{R}_0$

The number `n` is the sequence of `n` empty sequences, the sum is the concatenation, and a product
is read off a multiplication table.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace FiniteSequence

/-- The sequence of `n` empty sequences. -/
def tally : ℕ → FiniteSequence
  | 0 => nil
  | n + 1 => (tally n).snoc nil

@[simp]
lemma tally_append_tally (m : ℕ) : ∀ n, tally m ++ tally n = tally (m + n)
  | 0 => rfl
  | n + 1 => by simp [tally, tally_append_tally m n]

lemma tally_injective : Function.Injective tally
  | 0, 0, _ => rfl
  | m + 1, n + 1, h => by simpa using tally_injective (FiniteSequence.snoc.inj h).1

@[simp]
lemma tally_inj {m n : ℕ} : tally m = tally n ↔ m = n := tally_injective.eq_iff

end FiniteSequence

namespace Sequence

open DirectTranslation FiniteSequence SequenceStructure

section definitions

variable {M : Type*} [SequenceStructure M] {u v w x y z : M}

/-- The pair of `u` and `v` is an entry of `w`. -/
def IsEntry (u v w : M) : Prop := ∃ s, s ◨ w ∧ snoc s (snoc (snoc ∅ u) v) ◨ w

/-- The pair of `u` and `v` is an entry of `w`. -/
def isEntry : Semisentence ℒ⊢ 3 :=
  “u v w. ∃ s, !isPrefix s w ∧ !isPrefix (s ⊢ ((⋆ ⊢ u) ⊢ v)) w”

@[simp]
lemma eval_isEntry : M ⊧/![u, v, w] isEntry ↔ IsEntry u v w := by simp [isEntry, IsEntry]

/--
`w` is a multiplication table for `x`, up to the pair of `z` and `y`: each pair of initial segments
of `z` and of `y` that is an entry of `w` is $(0, 0)$ or is $(u + x, v + 1)$ for such a pair
$(u, v)$.
-/
def IsMulTable (x y z w : M) : Prop := ∀ u' v', u' ◨ z → v' ◨ y → IsEntry u' v' w →
  (u' = ∅ ∧ v' = ∅) ∨
    ∃ u v, u ◨ z ∧ v ◨ y ∧ u' = u ++ x ∧ v' = v ++ snoc ∅ ∅ ∧ IsEntry u v w

/--
`w` is a multiplication table for `x`, up to the pair of `z` and `y`: each pair of initial segments
of `z` and of `y` that is an entry of `w` is $(0, 0)$ or is $(u + x, v + 1)$ for such a pair
$(u, v)$.
-/
def isMulTable : Semisentence ℒ⊢ 4 :=
  “x y z w. ∀ u' v', !isPrefix u' z → !isPrefix v' y → !isEntry u' v' w →
    (u' = ⋆ ∧ v' = ⋆) ∨
      ∃ u v, !isPrefix u z ∧ !isPrefix v y ∧ u' = u ⌢ x ∧ v' = v ⌢ (⋆ ⊢ ⋆) ∧ !isEntry u v w”

@[simp]
lemma eval_isMulTable : M ⊧/![x, y, z, w] isMulTable ↔ IsMulTable x y z w := by
  simp [isMulTable, IsMulTable]

/-- `z` is a product of `x` and `y`, read off a multiplication table. -/
def IsProduct (z x y : M) : Prop := z ◨ z ∧ ∃ w, IsMulTable x y z w ∧ IsEntry z y w

/-- `z` is a product of `x` and `y`, read off a multiplication table. -/
def isProduct : Semisentence ℒ⊢ 3 :=
  “z x y. !isPrefix z z ∧ ∃ w, !isMulTable x y z w ∧ !isEntry z y w”

@[simp]
lemma eval_isProduct : M ⊧/![z, x, y] isProduct ↔ IsProduct z x y := by simp [isProduct, IsProduct]

/-- `z` is the product of `x` and `y` if there is exactly one, and `∅` otherwise. -/
def MulGraph (z x y : M) : Prop :=
  ((∃! r, IsProduct r x y) ∧ IsProduct z x y) ∨ (¬(∃! r, IsProduct r x y) ∧ z = ∅)

/-- `z` is the product of `x` and `y` if there is exactly one, and `∅` otherwise. -/
def mulGraph : Semisentence ℒ⊢ 3 :=
  “z x y. ((∃! r, !isProduct r x y) ∧ !isProduct z x y) ∨ (¬(∃! r, !isProduct r x y) ∧ z = ⋆)”

@[simp]
lemma eval_mulGraph : M ⊧/![z, x, y] mulGraph ↔ MulGraph z x y := by simp [mulGraph, MulGraph]

/-- `x` is less than `y`: a proper initial segment of `y`. -/
def LtGraph (x y : M) : Prop := x ◨ y ∧ x ≠ y

/-- `x` is less than `y`: a proper initial segment of `y`. -/
def ltGraph : Semisentence ℒ⊢ 2 := “x y. !isPrefix x y ∧ x ≠ y”

@[simp]
lemma eval_ltGraph : M ⊧/![x, y] ltGraph ↔ LtGraph x y := by simp [ltGraph, LtGraph]

lemma existsUnique_mulGraph (x y : M) : ∃! z, MulGraph z x y := by
  by_cases h : ∃! r, IsProduct r x y
  · simp [MulGraph, h]
  · use ∅
    simp [MulGraph, h]

end definitions

/--
The translation of the language of arithmetic into $\mathsf{WSeq}$: `0` is the empty sequence, `1`
is its one-element sequence, `+` is the concatenation, `*` is `MulGraph`, and `<` is `LtGraph`.
-/
def arithmeticTranslation : DirectTranslation 𝗪𝗦𝗲𝗾 ℒₒᵣ where
  domain := ⟨“x. ⊤”⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨ltGraph⟩
  func
    | .zero => ⟨“z. z = ⋆”⟩
    | .one => ⟨“z. z = ⋆ ⊢ ⋆”⟩
    | .add => ⟨“z x y. z = x ⌢ y”⟩
    | .mul => ⟨mulGraph⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use ∅
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_mulGraph (e 0) (e 1)
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma arithmeticTranslation_dom {M : Type*} [SequenceStructure M] (x : M) :
    arithmeticTranslation.Dom x := by
  simp [dom_iff, arithmeticTranslation, Semiformula.Operator.val]

section FiniteSequence

variable {a b p s t w : FiniteSequence} {m n : ℕ}

@[simp]
lemma isPrefix_tally_iff : ∀ {n}, s ◨ tally n ↔ ∃ i ≤ n, s = tally i
  | 0 => by simp [tally]
  | n + 1 => by simp [tally, isPrefix_snoc_iff, isPrefix_tally_iff, Nat.le_succ_iff, or_and_right,
      exists_or, or_comm]

lemma IsPrefix.of_snoc (h : s.snoc t ◨ w) : s ◨ w := by
  induction w with
  | nil => simp at h
  | snoc w p hw =>
    rw [isPrefix_snoc_iff] at h ⊢
    rcases h with h | h
    · obtain ⟨rfl, -⟩ := FiniteSequence.snoc.inj h
      exact .inr ⟨nil, rfl⟩
    · exact .inr <| hw h

@[simp]
lemma not_isEntry_nil : ¬IsEntry a b nil := by simp [IsEntry]

@[simp]
lemma isEntry_snoc_iff :
    IsEntry a b (w.snoc p) ↔ p = (nil.snoc a).snoc b ∨ IsEntry a b w := by
  have h {w} : IsEntry a b w ↔ ∃ s : FiniteSequence, s.snoc ((nil.snoc a).snoc b) ◨ w :=
    exists_congr fun s ↦ and_iff_right_of_imp IsPrefix.of_snoc
  simp [h, isPrefix_snoc_iff, exists_or, eq_comm]

/-- The multiplication table for `m` up to `n`. -/
def mulTable (m : ℕ) : ℕ → FiniteSequence
  | 0 => nil.snoc ((nil.snoc nil).snoc nil)
  | n + 1 => (mulTable m n).snoc ((nil.snoc (tally (m * (n + 1)))).snoc (tally (n + 1)))

lemma isEntry_mulTable_iff :
    ∀ {n}, IsEntry a b (mulTable m n) ↔ ∃ k ≤ n, a = tally (m * k) ∧ b = tally k
  | 0 => by simp [mulTable, tally, eq_comm]
  | n + 1 => by simp [mulTable, isEntry_mulTable_iff, Nat.le_succ_iff, or_and_right, exists_or,
      or_comm, eq_comm]

end FiniteSequence

variable {M : Type*} [SequenceStructure M] {u w x z : M} {m n : ℕ}

lemma toStructure_tally_one : ((tally 1).toStructure : M) = snoc ∅ ∅ := rfl

variable [M↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾]

lemma isPrefix_toStructure_tally_iff :
    x ◨ (tally n).toStructure ↔ ∃ i ≤ n, x = (tally i).toStructure := by
  simp only [isPrefix_toStructure_iff, isPrefix_tally_iff]
  grind

lemma isEntry_toStructure_iff {a b c : FiniteSequence} :
    IsEntry (a.toStructure : M) b.toStructure c.toStructure ↔ IsEntry a b c := by
  have h (s : FiniteSequence) : (snoc s.toStructure (snoc (snoc ∅ a.toStructure) b.toStructure) : M)
      = (s.snoc ((nil.snoc a).snoc b)).toStructure := rfl
  constructor
  · rintro ⟨_, hs, h'⟩
    obtain ⟨s, -, rfl⟩ := isPrefix_toStructure_iff.mp hs
    exact ⟨s, by simpa using hs, by simpa [h] using h'⟩
  · rintro ⟨s, hs, h'⟩
    exact ⟨s.toStructure, by simpa using hs, by simpa [h] using h'⟩

lemma IsMulTable.eq_tally
    (hw : IsMulTable (tally m).toStructure (tally n).toStructure z w) :
    ∀ k ≤ n, ∀ u, u ◨ z → IsEntry u (tally k).toStructure w → u = (tally (m * k)).toStructure := by
  intro k
  induction k with
  | zero =>
    intro hk u hu h
    rcases hw u _ hu (by simp) h with ⟨rfl, -⟩ | ⟨_, v, -, hv, -, h, -⟩
    · rfl
    · obtain ⟨i, -, rfl⟩ := isPrefix_toStructure_tally_iff.mp hv
      rw [← toStructure_tally_one, ← toStructure_append] at h
      simp at h
  | succ k ih =>
    intro hk u hu h
    rcases hw u _ hu (by simpa using hk) h with ⟨-, h⟩ | ⟨u, v, hu', hv, rfl, h, he⟩
    · exact absurd (toStructure_inj (t := nil).mp h) nofun
    · obtain ⟨i, -, rfl⟩ := isPrefix_toStructure_tally_iff.mp hv
      rw [← toStructure_tally_one, ← toStructure_append] at h
      obtain rfl : k = i := by simpa using h
      rw [ih (by omega) u hu' he, ← toStructure_append, tally_append_tally, Nat.mul_succ]

/-- The only product of two standard numbers is their standard product. -/
lemma isProduct_tally_iff :
    IsProduct z (tally m).toStructure (tally n).toStructure ↔
      z = (tally (m * n)).toStructure := by
  constructor
  · rintro ⟨hz, w, hw, he⟩
    exact hw.eq_tally n le_rfl z hz he
  · rintro rfl
    and_intros
    · simp
    · use (mulTable m n).toStructure
      and_intros
      · intro u v hu hv he
        obtain ⟨i, -, rfl⟩ := isPrefix_toStructure_tally_iff.mp hu
        obtain ⟨j, -, rfl⟩ := isPrefix_toStructure_tally_iff.mp hv
        obtain ⟨k, hk, hi, hj⟩ := isEntry_mulTable_iff.mp <| isEntry_toStructure_iff.mp he
        rw [hi, hj]
        rcases k with _ | k
        · exact .inl ⟨rfl, rfl⟩
        · right
          use (tally (m * k)).toStructure, (tally k).toStructure
          rw [← toStructure_tally_one, ← toStructure_append, ← toStructure_append,
            isEntry_toStructure_iff, isEntry_mulTable_iff]
          and_intros
          · simpa using Nat.mul_le_mul_left m (by omega : k ≤ n)
          · simpa using (by omega : k ≤ n)
          · simp [Nat.mul_succ]
          · simp
          · use k
            simp
            omega
      · rw [isEntry_toStructure_iff, isEntry_mulTable_iff]
        use n

lemma mulGraph_tally (m n : ℕ) :
    MulGraph ((tally (m * n)).toStructure : M) (tally m).toStructure (tally n).toStructure := by
  simp [MulGraph, isProduct_tally_iff]

lemma ltGraph_tally_iff : LtGraph x (tally n).toStructure ↔
    ∃ i < n, x = (tally i).toStructure := by
  simp only [LtGraph, isPrefix_toStructure_tally_iff]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, h⟩
    use i
    simp_all
    omega
  · rintro ⟨i, hi, rfl⟩
    simp [hi.le, hi.ne]

namespace arithmeticTranslation

/-- The constants, the operations and the order of the sequences of a model of $\mathsf{WSeq}$. -/
noncomputable abbrev oRingStructure : ORingStructure (arithmeticTranslation.Model M) where
  zero := ⟨∅, arithmeticTranslation_dom _⟩
  one := ⟨snoc ∅ ∅, arithmeticTranslation_dom _⟩
  add a b := ⟨(a : M) ++ (b : M), arithmeticTranslation_dom _⟩
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
      · symm
        apply Model.func_iff.mpr
        simp [arithmeticTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
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

lemma val_add : ((a + b : arithmeticTranslation.Model M) : M) = (a : M) ++ (b : M) := rfl

lemma val_mul_eq_iff : ((a * b : arithmeticTranslation.Model M) : M) = z ↔ MulGraph z a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := M) Language.ORing.Func.mul ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model M) i : M)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val, eval_mulGraph] at h
  exact ⟨fun e ↦ e ▸ h, (existsUnique_mulGraph _ _).unique h⟩

@[simp]
lemma val_numeral : ∀ n, ((ORingStructure.numeral n : arithmeticTranslation.Model M) : M) =
    (tally n).toStructure
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [ORingStructure.numeral, val_add, val_numeral (n + 1)]
    exact (toStructure_append (tally (n + 1)) (tally 1)).symm

end

/-- The sequences of a model of $\mathsf{WSeq}$ form a model of $\mathsf{R}_0$. -/
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
    simp [val_add, ← toStructure_append]
  case Ω₂ m n =>
    suffices (ORingStructure.numeral m * ORingStructure.numeral n : arithmeticTranslation.Model M) =
        ORingStructure.numeral (m * n) by simpa [models_iff] using this
    apply Model.ext
    simpa [val_mul_eq_iff] using mulGraph_tally m n
  case Ω₃ n =>
    suffices ∀ x : arithmeticTranslation.Model M, x < ORingStructure.numeral n ↔
        ∃ i < n, x = ORingStructure.numeral i by simpa [models_iff] using this
    intro x
    change LtGraph (x : M) _ ↔ _
    simp [ltGraph_tally_iff, ← Model.val_inj_iff]

end arithmeticTranslation

end Sequence

/-- $\mathsf{WSeq}$ interprets $\mathsf{R}_0$. -/
instance : 𝗪𝗦𝗲𝗾 ⊳ 𝗥₀ where
  trln := Sequence.arithmeticTranslation
  interpret_theory φ hφ := Sequence.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder

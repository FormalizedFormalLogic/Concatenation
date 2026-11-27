module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.Seq.Basic
public import Concatenation.ToFoundation.Arithmetic.R.Interpretability
public import Concatenation.ToFoundation.Arithmetic.R0.Representation

/-!
# Mutual interpretability of $\mathsf{WSeq}$ and $\mathsf{R}_0$

$\mathsf{WSeq}$ interprets $\mathsf{R}_0$ with the sequences of empty sequences for the numbers, and
$\mathsf{R}_0$ interprets $\mathsf{WSeq}$ with numerals for the sequences.
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

variable {V : Type*} [SequenceStructure V] {u v w x y z : V}

/-- The pair of `u` and `v` is an entry of `w`. -/
def IsEntry (u v w : V) : Prop := ∃ s, IsPrefix s w ∧ IsPrefix (snoc s (snoc (snoc ∅ u) v)) w

/-- The pair of `u` and `v` is an entry of `w`. -/
def isEntry : Semisentence ℒ⊢ 3 :=
  “u v w. ∃ s, !isPrefix s w ∧ !isPrefix (s ⊢ ((⋆ ⊢ u) ⊢ v)) w”

instance isEntry_defined : ℒ⊢-relation₃[V] IsEntry via isEntry :=
  ⟨fun v ↦ by simp [isEntry, IsEntry]⟩

instance isEntry_definable : ℒ⊢-relation₃[V] IsEntry := isEntry_defined.to_definable

/--
`w` is a multiplication table for `x`, up to the pair of `z` and `y`: each pair of initial segments
of `z` and of `y` that is an entry of `w` is $(0, 0)$ or is $(u + x, v + 1)$ for such a pair
$(u, v)$.
-/
def IsMulTable (x y z w : V) : Prop := ∀ u' v', IsPrefix u' z → IsPrefix v' y → IsEntry u' v' w →
  (u' = ∅ ∧ v' = ∅) ∨
    ∃ u v, IsPrefix u z ∧ IsPrefix v y ∧ u' = u ++ x ∧ v' = v ++ snoc ∅ ∅ ∧ IsEntry u v w

/--
`w` is a multiplication table for `x`, up to the pair of `z` and `y`: each pair of initial segments
of `z` and of `y` that is an entry of `w` is $(0, 0)$ or is $(u + x, v + 1)$ for such a pair
$(u, v)$.
-/
def isMulTable : Semisentence ℒ⊢ 4 :=
  “x y z w. ∀ u' v', !isPrefix u' z → !isPrefix v' y → !isEntry u' v' w →
    (u' = ⋆ ∧ v' = ⋆) ∨
      ∃ u v, !isPrefix u z ∧ !isPrefix v y ∧ u' = u ⌢ x ∧ v' = v ⌢ (⋆ ⊢ ⋆) ∧ !isEntry u v w”

instance isMulTable_defined : ℒ⊢-relation₄[V] IsMulTable via isMulTable :=
  ⟨fun v ↦ by simp [isMulTable, IsMulTable]⟩

instance isMulTable_definable : ℒ⊢-relation₄[V] IsMulTable := isMulTable_defined.to_definable

/-- `z` is a product of `x` and `y`, read off a multiplication table. -/
def IsProduct (z x y : V) : Prop := IsPrefix z z ∧ ∃ w, IsMulTable x y z w ∧ IsEntry z y w

/-- `z` is a product of `x` and `y`, read off a multiplication table. -/
def isProduct : Semisentence ℒ⊢ 3 :=
  “z x y. !isPrefix z z ∧ ∃ w, !isMulTable x y z w ∧ !isEntry z y w”

instance isProduct_defined : ℒ⊢-relation₃[V] IsProduct via isProduct :=
  ⟨fun v ↦ by simp [isProduct, IsProduct]⟩

instance isProduct_definable : ℒ⊢-relation₃[V] IsProduct := isProduct_defined.to_definable

/-- `z` is the product of `x` and `y` if there is exactly one, and `∅` otherwise. -/
def MulGraph (z x y : V) : Prop :=
  ((∃! r, IsProduct r x y) ∧ IsProduct z x y) ∨ (¬(∃! r, IsProduct r x y) ∧ z = ∅)

/-- `z` is the product of `x` and `y` if there is exactly one, and `∅` otherwise. -/
def mulGraph : Semisentence ℒ⊢ 3 :=
  “z x y. ((∃! r, !isProduct r x y) ∧ !isProduct z x y) ∨ (¬(∃! r, !isProduct r x y) ∧ z = ⋆)”

instance mulGraph_defined : ℒ⊢-relation₃[V] MulGraph via mulGraph :=
  ⟨fun v ↦ by simp [mulGraph, MulGraph]⟩

instance mulGraph_definable : ℒ⊢-relation₃[V] MulGraph := mulGraph_defined.to_definable

/-- `x` is less than `y`: a proper initial segment of `y`. -/
def LtGraph (x y : V) : Prop := IsPrefix x y ∧ x ≠ y

/-- `x` is less than `y`: a proper initial segment of `y`. -/
def ltGraph : Semisentence ℒ⊢ 2 := “x y. !isPrefix x y ∧ x ≠ y”

instance ltGraph_defined : ℒ⊢-relation[V] LtGraph via ltGraph :=
  ⟨fun v ↦ by simp [ltGraph, LtGraph]⟩

instance ltGraph_definable : ℒ⊢-relation[V] LtGraph := ltGraph_defined.to_definable

lemma existsUnique_mulGraph (x y : V) : ∃! z, MulGraph z x y := by
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
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use ∅
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    case mul =>
      rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_mulGraph (e 0) (e 1)
    all_goals simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma arithmeticTranslation.dom {V : Type*} [SequenceStructure V] (x : V) :
    arithmeticTranslation.Dom x := by
  simp [dom_iff, arithmeticTranslation, Semiformula.Operator.val]

section FiniteSequence

variable {a b p s t w : FiniteSequence} {m n : ℕ}

@[simp]
lemma isPrefix_tally_iff : ∀ {n}, IsPrefix s (tally n) ↔ ∃ i ≤ n, s = tally i
  | 0 => by simp [tally]
  | n + 1 => by simp [tally, isPrefix_snoc_iff, isPrefix_tally_iff, Nat.le_succ_iff, or_and_right,
      exists_or, or_comm]

private lemma IsPrefix.of_snoc (h : IsPrefix (s.snoc t) w) : IsPrefix s w := by
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
  have h {w} : IsEntry a b w ↔ ∃ s : FiniteSequence, IsPrefix (s.snoc ((nil.snoc a).snoc b)) w :=
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

variable {V : Type*} [SequenceStructure V] {u w x z : V} {m n : ℕ}

lemma toStructure_tally_one : ((tally 1).toStructure : V) = snoc ∅ ∅ := rfl

variable [V↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾]

lemma isPrefix_toStructure_tally_iff :
    IsPrefix x (tally n).toStructure ↔ ∃ i ≤ n, x = (tally i).toStructure := by
  simp only [isPrefix_toStructure_iff, isPrefix_tally_iff]
  grind

lemma isEntry_toStructure_iff {a b c : FiniteSequence} :
    IsEntry (a.toStructure : V) b.toStructure c.toStructure ↔ IsEntry a b c := by
  have h (s : FiniteSequence) : (snoc s.toStructure (snoc (snoc ∅ a.toStructure) b.toStructure) : V)
      = (s.snoc ((nil.snoc a).snoc b)).toStructure := rfl
  constructor
  · rintro ⟨_, hs, h'⟩
    obtain ⟨s, -, rfl⟩ := isPrefix_toStructure_iff.mp hs
    exact ⟨s, by simpa using hs, by simpa [h] using h'⟩
  · rintro ⟨s, hs, h'⟩
    exact ⟨s.toStructure, by simpa using hs, by simpa [h] using h'⟩

private lemma IsMulTable.eq_tally
    (hw : IsMulTable (tally m).toStructure (tally n).toStructure z w) :
    ∀ k ≤ n, ∀ u, IsPrefix u z → IsEntry u (tally k).toStructure w →
      u = (tally (m * k)).toStructure := by
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

private lemma mulGraph_tally (m n : ℕ) :
    MulGraph ((tally (m * n)).toStructure : V) (tally m).toStructure (tally n).toStructure := by
  simp [MulGraph, isProduct_tally_iff]

private lemma ltGraph_tally_iff : LtGraph x (tally n).toStructure ↔
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
noncomputable abbrev oRingStructure : ORingStructure (arithmeticTranslation.Model V) where
  zero := ⟨∅, arithmeticTranslation.dom _⟩
  one := ⟨snoc ∅ ∅, arithmeticTranslation.dom _⟩
  add a b := ⟨(a : V) ++ (b : V), arithmeticTranslation.dom _⟩
  mul a b := Tarski.Structure.func (L := ℒₒᵣ) Language.ORing.Func.mul ![a, b]
  lt a b := LtGraph (a : V) b

/-- The structure of the model of `arithmeticTranslation` is the one of `oRingStructure`. -/
lemma struc_eq : Model.struc arithmeticTranslation V = @Arithmetic.standardModel _ oRingStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      case mul =>
        conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl
      all_goals
        symm
        apply Model.func_iff.mpr
        simp [arithmeticTranslation, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      · exact propext <| Model.eq_iff v
      · change (arithmeticTranslation.rel .lt).val (fun i ↦ (v i : V)) = LtGraph (v 0 : V) (v 1)
        rw [Matrix.fun_eq_vec_two (fun i ↦ (v i : V))]
        simp [arithmeticTranslation, Semiformula.Operator.val])

section

attribute [local instance] oRingStructure

variable {a b : arithmeticTranslation.Model V}

lemma val_add : ((a + b : arithmeticTranslation.Model V) : V) = (a : V) ++ (b : V) := rfl

lemma val_mul_eq_iff : ((a * b : arithmeticTranslation.Model V) : V) = z ↔ MulGraph z a b := by
  have h := Model.eval_func (π := arithmeticTranslation) (M := V) Language.ORing.Func.mul ![a, b]
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![a, b] : Fin 2 → arithmeticTranslation.Model V) i : V)] at h
  simp only [arithmeticTranslation, Semiformula.Operator.val, Matrix.cons_val,
    Defined.eval_iff] at h
  exact ⟨fun e ↦ e ▸ h, (existsUnique_mulGraph _ _).unique h⟩

@[simp]
lemma val_numeral : ∀ n, ((ORingStructure.numeral n : arithmeticTranslation.Model V) : V) =
    (tally n).toStructure
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    rw [ORingStructure.numeral, val_add, val_numeral (n + 1)]
    exact (toStructure_append (tally (n + 1)) (tally 1)).symm

end

/-- The sequences of a model of $\mathsf{WSeq}$ form a model of $\mathsf{R}_0$. -/
instance : (arithmeticTranslation.Model V)↓[ℒₒᵣ] ⊧* 𝗥₀ := by
  rw [struc_eq]
  let := oRingStructure (V := V)
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case Ω₁ m n =>
    suffices (ORingStructure.numeral m + ORingStructure.numeral n : arithmeticTranslation.Model V) =
        ORingStructure.numeral (m + n) by simpa [models_iff] using this
    apply Model.ext
    simp [val_add, ← toStructure_append]
  case Ω₂ m n =>
    suffices (ORingStructure.numeral m * ORingStructure.numeral n : arithmeticTranslation.Model V) =
        ORingStructure.numeral (m * n) by simpa [models_iff] using this
    apply Model.ext
    simpa [val_mul_eq_iff] using mulGraph_tally m n
  case Ω₃ n =>
    suffices ∀ x : arithmeticTranslation.Model V, x < ORingStructure.numeral n ↔
        ∃ i < n, x = ORingStructure.numeral i by simpa [models_iff] using this
    intro x
    change LtGraph (x : V) _ ↔ _
    simp [ltGraph_tally_iff, ← Model.val_inj_iff]

end arithmeticTranslation

end Sequence

/-- $\mathsf{WSeq}$ interprets $\mathsf{R}_0$. -/
instance : 𝗪𝗦𝗲𝗾 ⊳ 𝗥₀ where
  trln := Sequence.arithmeticTranslation
  interpret_theory _ hφ := Sequence.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

namespace FiniteSequence

open Encodable Denumerable

/-- The code of a sequence. -/
def code : FiniteSequence → ℕ
  | nil => 0
  | .snoc s t => Nat.pair t.code s.code + 1

lemma code_injective : Function.Injective code := by
  intro s
  induction s with
  | nil => rintro (_ | _) <;> simp [code]
  | snoc s t hs ht =>
    rintro (_ | ⟨s', t'⟩)
    · simp [code]
    · simp only [code, Nat.add_right_cancel_iff, Nat.pair_eq_pair, snoc.injEq, and_imp]
      exact fun h₁ h₂ ↦ ⟨hs h₂, ht h₁⟩

@[simp]
lemma code_inj {s t : FiniteSequence} : s.code = t.code ↔ s = t := code_injective.eq_iff

lemma code_surjective : Function.Surjective code := by
  intro n
  induction n using Nat.strongRec with
  | ind n ih =>
    rcases n with _ | n
    · use nil
      rfl
    · obtain ⟨t, ht⟩ := ih _ <| Nat.lt_succ_of_le n.unpair_left_le
      obtain ⟨s, hs⟩ := ih _ <| Nat.lt_succ_of_le n.unpair_right_le
      use s.snoc t
      simp [code, hs, ht]

lemma code_le_code_append_left (s t : FiniteSequence) : s.code ≤ (s ++ t).code := by
  induction t with
  | nil => simp
  | snoc t u ht =>
    rw [append_snoc, code]
    exact ht.trans <| (Nat.right_le_pair _ _).trans <| Nat.le_succ _

lemma code_le_code_append_right (s t : FiniteSequence) : t.code ≤ (s ++ t).code := by
  induction t with
  | nil => simp [code]
  | snoc t u ht =>
    rw [append_snoc, code, code, Nat.add_le_add_iff_right]
    rcases ht.eq_or_lt with h | h
    · rw [h]
    · exact (Nat.pair_lt_pair_right _ h).le

/-- The code of the concatenation of the sequences coded by `m` and `n`. -/
def appendCode (m n : ℕ) : ℕ := encode (ofNat (List ℕ) n ++ ofNat (List ℕ) m)

@[simp]
lemma appendCode_code (s t : FiniteSequence) : appendCode s.code t.code = (s ++ t).code := by
  induction t with
  | nil => simp [appendCode, code]
  | snoc t u ht => simpa [appendCode, code] using ht

lemma primrec₂_appendCode : Primrec₂ appendCode :=
  Primrec.encode.comp <| Primrec.list_append.comp ((Primrec.ofNat _).comp Primrec.snd)
    ((Primrec.ofNat _).comp Primrec.fst)

end FiniteSequence

namespace Sequence

open DirectTranslation FiniteSequence ORingStructure Arithmetic Arithmetic.R0
open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] {x y z : V}

/-- `z` is $\langle y, x \rangle + 1$, in the pairing `Nat.pair`. -/
def SnocGraph (z x y : V) : Prop :=
  (y < x ∧ z = x * x + y + 1) ∨ (¬y < x ∧ z = y * y + y + x + 1)

/-- `z` is $\langle y, x \rangle + 1$, in the pairing `Nat.pair`. -/
def snocGraphDef : 𝚺ᴬ₀.Semisentence 3 :=
  .mkSigma “z x y. (y < x ∧ z = x * x + y + 1) ∨ (¬y < x ∧ z = y * y + y + x + 1)”

instance snocGraph_defined : 𝚺ᴬ₀-Relation₃[V] SnocGraph via snocGraphDef := .mk fun v ↦ by
  simp [snocGraphDef, SnocGraph, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq]

instance snocGraph_definable : 𝚺ᴬ₀-Relation₃[V] SnocGraph := snocGraph_defined.to_definable

private lemma existsUnique_snocGraph (x y : V) : ∃! z, SnocGraph z x y := by
  by_cases h : y < x
  · use x * x + y + 1
    simp [SnocGraph, h]
  · use y * y + y + x + 1
    simp [SnocGraph, h]

/-- `z` is the concatenation of `x` and `y`, or `x` if there is none. -/
def ConcatGraph (z x y : V) : Prop :=
  IsValue₂ appendCode x y z ∨ (z = x ∧ ∀ w, ¬IsValue₂ appendCode x y w)

/-- `z` is the concatenation of `x` and `y`, or `x` if there is none. -/
noncomputable def concatGraphDef : ArithmeticSemisentence 3 :=
  “z x y. !(isValue₂Def appendCode) x y z ∨ (z = x ∧ ∀ w, ¬!(isValue₂Def appendCode) x y w)”

instance concatGraph_defined : ℒₒᵣ-relation₃[V] ConcatGraph via concatGraphDef :=
  ⟨fun v ↦ by simp [concatGraphDef, ConcatGraph]⟩

instance concatGraph_definable : ℒₒᵣ-relation₃[V] ConcatGraph := concatGraph_defined.to_definable

lemma existsUnique_concatGraph (x y : V) : ∃! z, ConcatGraph z x y :=
  existsUnique_isValue₂_or _ x y x

/--
The translation of the language of sequences into $\mathsf{R}_0$: a sequence is the numeral of its
code.
-/
noncomputable def codeTranslation : DirectTranslation 𝗥₀ ℒ⊢ where
  domain := ⟨⊤⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
  func
    | .empty => ⟨“z. z = 0”⟩
    | .snoc => ⟨snocGraphDef.val⟩
    | .concat => ⟨concatGraphDef⟩
  domain_nonempty := Arithmetic.complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := Arithmetic.complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    cases f
    · simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_snocGraph (e 0) (e 1)
    · rw [Matrix.fun_eq_vec_two e]
      simpa [Semiformula.Operator.val] using existsUnique_concatGraph (e 0) (e 1)
  preserve_eq := Arithmetic.complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

@[simp]
lemma codeTranslation.dom (x : V) : codeTranslation.Dom x := by
  simp [dom_iff, codeTranslation, Semiformula.Operator.val]

variable [V↓[ℒₒᵣ] ⊧* 𝗥₀]

private lemma snocGraph_numeral (s t : FiniteSequence) :
    SnocGraph (numeral (s.snoc t).code : V) (numeral s.code) (numeral t.code) := by
  by_cases h : t.code < s.code <;>
    simp [SnocGraph, FiniteSequence.code, Nat.pair, h, numeral_mul_numeral, numeral_add_numeral,
      numeral_add_one_of_R0]

lemma concatGraph_numeral (s t : FiniteSequence) :
    ConcatGraph (numeral (s ++ t).code : V) (numeral s.code) (numeral t.code) := by
  have h := isValue₂_numeral (V := V) (m := s.code) (n := t.code) primrec₂_appendCode.to_comp
  rw [appendCode_code] at h
  exact .inl <| h (s.code_le_code_append_left t) (s.code_le_code_append_right t)

private lemma ConcatGraph.exists_of_numeral {s : FiniteSequence}
    (h : ConcatGraph (numeral s.code) x y) : ∃ u, IsPrefix u s ∧ x = numeral u.code := by
  rcases h with h | ⟨rfl, -⟩
  · obtain ⟨m, n, rfl, rfl, h'⟩ := h.exists_of_numeral primrec₂_appendCode.to_comp
    obtain ⟨u, rfl⟩ := code_surjective m
    obtain ⟨v, rfl⟩ := code_surjective n
    use u, ⟨v, by simpa using h'⟩
  · use s, ⟨nil, rfl⟩

namespace codeTranslation

/-- The numeral of the code of a sequence. -/
def ofSequence (s : FiniteSequence) : codeTranslation.Model V := ⟨numeral s.code, by simp⟩

/-- The empty sequence and the operations on codes in `V`. -/
noncomputable abbrev sequenceStructure : SequenceStructure (codeTranslation.Model V) where
  emptyCollection := ofSequence .nil
  snoc x y := Tarski.Structure.func (L := ℒ⊢) Language.Sequence.Func.snoc ![x, y]
  append x y := Tarski.Structure.func (L := ℒ⊢) Language.Sequence.Func.concat ![x, y]

/-- The structure of the model of `codeTranslation` is the one of `sequenceStructure`. -/
lemma struc_eq : Model.struc codeTranslation V = @standardModel _ sequenceStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      cases f
      · symm
        apply Model.func_iff.mpr
        simp [codeTranslation, Semiformula.Operator.val]
        rfl
      all_goals
        conv_lhs => rw [Matrix.fun_eq_vec_two v]
        rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

section

attribute [local instance] sequenceStructure

variable {x y z : codeTranslation.Model V}

private lemma snoc_eq_iff : SequenceStructure.snoc x y = z ↔ SnocGraph (z : V) x y := by
  have := Model.func_iff (π := codeTranslation) (M := V) (f := Language.Sequence.Func.snoc)
    (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → codeTranslation.Model V) i : V)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val,
    Bounding.HierarchySymbol.Defined.iff] at this
  exact eq_comm.trans this

lemma append_eq_iff : x ++ y = z ↔ ConcatGraph (z : V) x y := by
  have := Model.func_iff (π := codeTranslation) (M := V) (f := Language.Sequence.Func.concat)
    (y := z) (v := ![x, y])
  rw [Matrix.fun_eq_vec_two fun i ↦ ((![x, y] : Fin 2 → codeTranslation.Model V) i : V)] at this
  simp only [codeTranslation, Semiformula.Operator.val, Matrix.cons_val, Defined.eval_iff] at this
  exact eq_comm.trans this

/-- The sequences are embedded onto an initial part of the model of `codeTranslation`. -/
private lemma isInitialEmbedding_ofSequence :
    IsInitialEmbedding (ofSequence : FiniteSequence → codeTranslation.Model V) where
  injective s t h := by simpa [ofSequence] using h
  map_nil := rfl
  map_snoc s t := (snoc_eq_iff.mpr <| snocGraph_numeral s t).symm
  map_append s t := (append_eq_iff.mpr <| concatGraph_numeral s t).symm
  exists_of_isPrefix := by
    rintro x s ⟨y, h⟩
    obtain ⟨u, hu, hx⟩ := (append_eq_iff.mp h).exists_of_numeral
    exact ⟨u, hu, Model.ext hx⟩

end

/-- The model of `codeTranslation` satisfies $\mathsf{WSeq}$. -/
instance : (codeTranslation.Model V)↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾 := by
  rw [struc_eq]
  let := sequenceStructure (V := V)
  exact isInitialEmbedding_ofSequence.models_WSeq

end codeTranslation

end Sequence

/-- $\mathsf{R}_0$ interprets $\mathsf{WSeq}$. -/
noncomputable instance : 𝗥₀ ⊳ 𝗪𝗦𝗲𝗾 where
  trln := Sequence.codeTranslation
  interpret_theory _ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

/--
$\mathsf{WSeq}$ and $\mathsf{R}$ are mutually interpretable.
- [KM24, §2]
-/
noncomputable instance : 𝗪𝗦𝗲𝗾 ⋈ 𝗥 :=
  MutualDirectInterpretation.trans (T₂ := 𝗥₀) ⟨inferInstance, inferInstance⟩ inferInstance

end FFL.FirstOrder

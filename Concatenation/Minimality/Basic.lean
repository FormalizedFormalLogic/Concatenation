module

public import Concatenation.BT.Basic
public import Concatenation.Coding
public import Concatenation.D.Basic
public import Concatenation.Semantics.Basic
public import Concatenation.ToFoundation.Decidability

/-!
# Axioms of $\mathsf{D}$, $\mathsf{ID}$ and $\mathsf{BT}$

The axioms of $\mathsf{D}$, $\mathsf{ID}$ and $\mathsf{BT}$ whose removal is studied, as sentences,
and the one-element model of $\mathsf{ID}$ and $\mathsf{BT}$ without $x0 \neq y1$.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation


/-- The axiom on the prefixes of $y0$. -/
def prefixConcatZero : Sentence ℒ⌢⊑ :=
  “∀ x y, x ⊑ y ⌢ !!(op(0).const) ↔ x = y ⌢ !!(op(0).const) ∨ x ⊑ y”

lemma prefixConcatZero_mem_D : prefixConcatZero ∈ 𝗗 := IsDAxiom.prefixConcatZero

/-- The axiom on the prefixes of $y1$. -/
def prefixConcatOne : Sentence ℒ⌢⊑ :=
  “∀ x y, x ⊑ y ⌢ !!(op(1).const) ↔ x = y ⌢ !!(op(1).const) ∨ x ⊑ y”

lemma prefixConcatOne_mem_D : prefixConcatOne ∈ 𝗗 := IsDAxiom.prefixConcatOne

section

variable {L : Language} [L.Zero] [L.One] [L.Concat] [L.Eq]

/-- Associativity of the concatenation. -/
def concatAssoc : Sentence L := “∀ x y z, (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)”

/-- Right cancellation for the letters. -/
def concatRightCancel : Sentence L :=
  “∀ x y, x ≠ y →
    x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(0).const) ∧ x ⌢ !!(op(1).const) ≠ y ⌢ !!(op(1).const)”

/-- A string does not end with both letters. -/
def concatZeroNeConcatOne : Sentence L :=
  “∀ x y, x ⌢ !!(op(0).const) ≠ y ⌢ !!(op(1).const)”

end

lemma concatRightCancel_mem_ID : concatRightCancel ∈ 𝗜𝗗 := IsIDAxiom.concatRightCancel

lemma concatZeroNeConcatOne_mem_ID : concatZeroNeConcatOne ∈ 𝗜𝗗 := IsIDAxiom.concatZeroNeConcatOne

lemma concatAssoc_mem_BT : concatAssoc ∈ 𝗕𝗧 := IsBTAxiom.concatAssoc

lemma concatRightCancel_mem_BT : concatRightCancel ∈ 𝗕𝗧 := IsBTAxiom.concatRightCancel

lemma concatZeroNeConcatOne_mem_BT : concatZeroNeConcatOne ∈ 𝗕𝗧 := IsBTAxiom.concatZeroNeConcatOne


open Language

local instance : ConcatenationStructure Unit where
  zero := ()
  one := ()
  append _ _ := ()

lemma unit_models_BT_diff_concatZeroNeConcatOne :
    Unit↓[ℒ⌢] ⊧* (𝗕𝗧 \ {concatZeroNeConcatOne} : Theory ℒ⌢) := ⟨by
  rintro σ ⟨h, hσ⟩
  cases h
  case equal hφ =>
    have : Unit↓[ℒ⌢] ⊧* 𝗘𝗤 ℒ⌢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simp [models_iff]
  case concatRightCancel => simp [models_iff]
  case concatZeroNeConcatOne => exact absurd rfl hσ
  case substring α =>
    simp only [models_iff]
    simpa using ⟨α, FreeSemigroup.mem_substrings_iff.mpr <| .inl rfl⟩⟩

/--
$\mathsf{BT}$ without the axiom $x0 \neq y1$ is not essentially undecidable.
- [Mur22, Open Problem 3]
-/
theorem not_essentiallyUndecidable_BT_diff_concatZeroNeConcatOne :
    ¬(𝗕𝗧 \ {concatZeroNeConcatOne} : Theory ℒ⌢).EssentiallyUndecidable := by
  have := unit_models_BT_diff_concatZeroNeConcatOne
  have : Unit↓[ℒ⌢] ⊧* ({“∀ x y, x = y”} : Theory ℒ⌢) := ⟨by simp [models_iff]⟩
  have : ({“∀ x y, x = y”} : Theory ℒ⌢).RE := Theory.RE.ofFinite <| Set.toFinite _
  apply Theory.not_essentiallyUndecidable_of_models_of_rel _ {“∀ x y, x = y”} Unit
  · rintro k ⟨⟩ v
    exact Subsingleton.elim _ _
  · intro M _ s hM k r v
    rcases r
    have e (w : Fin 2 → M) : Semiterm.val (L := ℒ⌢) w Empty.elim ∘ Semiterm.bvar = w := by
      funext i
      simp
    have h : ∀ a b : M, s.rel (L := ℒ⌢) Language.Eq.eq ![a, b] := by
      simpa [models_iff, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
        Semiformula.eval_rel, e] using hM
    exact Matrix.fun_eq_vec_two (v := v) ▸ h (v 0) (v 1)

lemma unit_models_ID_diff_concatZeroNeConcatOne :
    Unit↓[ℒ⌢⊑] ⊧* (𝗜𝗗 \ {concatZeroNeConcatOne} : Theory ℒ⌢⊑) := ⟨by
  rintro σ ⟨h, hσ⟩
  cases h
  case equal hφ =>
    have : Unit↓[ℒ⌢⊑] ⊧* 𝗘𝗤 ℒ⌢⊑ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case concatAssoc => simp [models_iff]
  case concatRightCancel => simp [models_iff]
  case concatZeroNeConcatOne => exact absurd rfl hσ
  case pref α =>
    simp only [models_iff]
    simpa using ⟨α, FreeSemigroup.mem_prefixes_iff.mpr <| .inl rfl⟩⟩

/--
$\mathsf{ID}$, also called $\mathsf{C}$, without the axiom $x0 \neq y1$ is not essentially
undecidable.
- [Mur22, Open Problem 3]
-/
theorem not_essentiallyUndecidable_ID_diff_concatZeroNeConcatOne :
    ¬(𝗜𝗗 \ {concatZeroNeConcatOne} : Theory ℒ⌢⊑).EssentiallyUndecidable := by
  have := unit_models_ID_diff_concatZeroNeConcatOne
  have : Unit↓[ℒ⌢⊑] ⊧* ({“∀ x y, x = y”, “∀ x y, x ⊑ y”} : Theory ℒ⌢⊑) := ⟨by
    simp [models_iff]⟩
  have : ({“∀ x y, x = y”, “∀ x y, x ⊑ y”} : Theory ℒ⌢⊑).RE :=
    Theory.RE.ofFinite <| Set.toFinite _
  apply Theory.not_essentiallyUndecidable_of_models_of_rel _
    {“∀ x y, x = y”, “∀ x y, x ⊑ y”} Unit
  · rintro k (r | r) v <;> rcases r
    · exact Subsingleton.elim (v 0) (v 1)
    · exact le_refl (v 0)
  · intro M _ s hM k r v
    have e (w : Fin 2 → M) : Semiterm.val (L := ℒ⌢⊑) w Empty.elim ∘ Semiterm.bvar = w := by
      funext i
      simp
    have h : (∀ a b : M, s.rel (L := ℒ⌢⊑) Language.Eq.eq ![a, b]) ∧
        ∀ a b : M, s.rel (L := ℒ⌢⊑) Language.Prefix.pref ![a, b] := by
      simpa [models_iff, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
        Semiformula.Operator.Prefix.sentence_eq, Semiformula.eval_rel, e] using hM
    rcases r with r | r <;> rcases r
    · exact Matrix.fun_eq_vec_two (v := v) ▸ h.1 (v 0) (v 1)
    · exact Matrix.fun_eq_vec_two (v := v) ▸ h.2 (v 0) (v 1)

end Concatenation

end FFL.FirstOrder

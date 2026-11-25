module

public import Concatenation.Seq.Language
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-!
# The weak theory of sequences $\mathsf{WSeq}$

The theory $\mathsf{WSeq}$, and structures with an empty sequence, an operation that appends an
element and a concatenation, read as structures for `ℒ⊢`.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A type with an empty sequence `∅`, an operation `snoc`, and a concatenation `++`. -/
class SequenceStructure (α : Type*) extends EmptyCollection α, Append α where
  /-- `snoc x y` is `x` with `y` appended. -/
  snoc : α → α → α

namespace FiniteSequence

instance : SequenceStructure FiniteSequence where
  snoc := FiniteSequence.snoc

@[simp]
lemma empty_eq_nil : (∅ : FiniteSequence) = nil := rfl

@[simp]
lemma snoc_eq_snoc (s t : FiniteSequence) : SequenceStructure.snoc s t = s.snoc t := rfl

/-- The value of a sequence in a structure. -/
def toStructure {M : Type*} [SequenceStructure M] : FiniteSequence → M
  | nil => ∅
  | .snoc s t => SequenceStructure.snoc s.toStructure t.toStructure

end FiniteSequence

namespace Sequence

open Language FiniteSequence SequenceStructure

/--
`x` is an initial segment of `y`.
- [KM24, §2]
-/
def isPrefix : Semisentence ℒ⊢ 2 := “x y. ∃ z, x ⌢ z = y”

/-- `x` is one of the sequences in the list. -/
def isOneOf (l : List FiniteSequence) : Semisentence ℒ⊢ 1 := l.disj' fun s ↦ “x. x = !!s.sequeral”

/--
Axioms of the weak theory of sequences $\mathsf{WSeq}$.
- [KM24, §2, Figure 2]
-/
inductive IsWSeqAxiom : SequenceSentence → Prop
  | equal : ∀ φ ∈ 𝗘𝗤 ℒ⊢, IsWSeqAxiom φ
  | ne (s t : FiniteSequence) (h : s ≠ t) : IsWSeqAxiom “!!s.sequeral ≠ !!t.sequeral”
  | concat (s t : FiniteSequence) : IsWSeqAxiom
      “!!s.sequeral ⌢ !!t.sequeral = !!(s ++ t).sequeral”
  | pref (s : FiniteSequence) : IsWSeqAxiom
      “∀ x, !isPrefix x !!s.sequeral → !(isOneOf s.prefixes) x”

/--
The weak theory of sequences $\mathsf{WSeq}$.
- [KM24, §2, Figure 2]
-/
abbrev WSeq : SequenceTheory := Set.ofPred IsWSeqAxiom

@[inherit_doc]
notation "𝗪𝗦𝗲𝗾" => WSeq

instance : 𝗘𝗤 ℒ⊢ ⪯ 𝗪𝗦𝗲𝗾 := Entailment.WeakerThan.ofSubset fun φ hφ ↦ IsWSeqAxiom.equal φ hφ

section semantics

variable (M : Type*) [SequenceStructure M]

instance : Nonempty M := ⟨∅⟩

instance standardModel : Tarski.Structure ℒ⊢ M where
  func := fun _ f ↦
    match f with
    | Sequence.Func.empty => fun _ ↦ ∅
    | Sequence.Func.snoc => fun v ↦ snoc (v 0) (v 1)
    | Sequence.Func.concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | Sequence.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⊢ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Concat ℒ⊢ M := ⟨fun _ _ ↦ rfl⟩

@[simp]
lemma val_star : (Semiterm.Operator.Star.star : Semiterm.Const ℒ⊢).val ![] = (∅ : M) := rfl

@[simp]
lemma val_snoc (x y : M) : Semiterm.Operator.snoc.val ![x, y] = snoc x y := rfl

lemma complete (T : SequenceTheory) [𝗘𝗤 ℒ⊢ ⪯ T] (φ : SequenceSentence)
    (H : ∀ (M : Type*) [SequenceStructure M] [M↓[ℒ⊢] ⊧* T], M↓[ℒ⊢] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    have hr (v : Fin 2 → M) : s.rel Language.Eq.eq v ↔ v 0 = v 1 := by simp
    let c : SequenceStructure M :=
      { emptyCollection := s.func Language.Sequence.Func.empty ![]
        snoc a b := s.func Language.Sequence.Func.snoc ![a, b]
        append a b := s.func Language.Sequence.Func.concat ![a, b] }
    have e : s = standardModel M := Tarski.Structure.ext
      (funext₃ fun k f v ↦ by
        cases f
        · rw [Matrix.empty_eq v]; rfl
        · conv_lhs => rw [Matrix.fun_eq_vec_two v]
          rfl
        · conv_lhs => rw [Matrix.fun_eq_vec_two v]
          rfl)
      (funext₃ fun k r v ↦ by
        cases r
        exact propext <| hr v)
    rw [e] at hT ⊢
    exact H M

end semantics

section eval

variable {M : Type*} [SequenceStructure M] {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M}
  {x y z : M} {s t u : FiniteSequence}

@[simp]
lemma val_sequeral (s : FiniteSequence) :
    (s.sequeral : Semiterm ℒ⊢ ξ n).val e ε = s.toStructure := by
  induction s with
  | nil => simp [sequeral, toStructure]
  | snoc s t hs ht => simp [sequeral, toStructure, hs, ht]

/--
`x` is an initial segment of `y`.
- [KM24, §2]
-/
def IsPrefix (x y : M) : Prop := ∃ z, x ++ z = y

/-- `x ◨ y`: `x` is an initial segment of `y`. -/
scoped infix:50 " ◨ " => IsPrefix

@[simp]
lemma eval_isPrefix : M ⊧/![x, y] isPrefix ↔ x ◨ y := by simp [isPrefix, IsPrefix]

@[simp]
lemma eval_isOneOf {l : List FiniteSequence} :
    M ⊧/![x] (isOneOf l) ↔ ∃ s ∈ l, x = s.toStructure := by
  simp [isOneOf]

end eval

section FiniteSequence

variable {s t u : FiniteSequence}

@[simp]
lemma toStructure_self (s : FiniteSequence) : s.toStructure = s := by
  induction s with
  | nil => rfl
  | snoc s t hs ht => simp [toStructure, hs, ht]

@[simp]
lemma isPrefix_nil_iff : s ◨ nil ↔ s = nil := by
  constructor
  · rintro ⟨_ | _, h⟩
    · simpa using h
    · simp at h
  · rintro rfl
    exact ⟨nil, rfl⟩

lemma isPrefix_snoc_iff : s ◨ t.snoc u ↔ s = t.snoc u ∨ s ◨ t := by
  constructor
  · rintro ⟨_ | ⟨v, w⟩, h⟩
    · simp_all
    · right
      use v
      simp_all
  · rintro (rfl | ⟨v, rfl⟩)
    · exact ⟨nil, rfl⟩
    · exact ⟨v.snoc u, rfl⟩

@[simp]
lemma mem_prefixes_iff : s ∈ t.prefixes ↔ s ◨ t := by
  induction t with
  | nil => simp [prefixes]
  | snoc t u ht => simp [prefixes, isPrefix_snoc_iff, ht]

end FiniteSequence

section initial

variable {M : Type*} [SequenceStructure M]

/--
`c` embeds the sequences into `M` as a part closed under initial segments: the initial segments
of a standard sequence in `M` are its standard initial segments.
-/
structure IsInitialEmbedding (c : FiniteSequence → M) : Prop where
  injective : Function.Injective c
  map_nil : c nil = ∅
  map_snoc (s t : FiniteSequence) : c (s.snoc t) = snoc (c s) (c t)
  map_append (s t : FiniteSequence) : c (s ++ t) = c s ++ c t
  exists_of_isPrefix {x : M} {s : FiniteSequence} (h : x ◨ c s) : ∃ u, u ◨ s ∧ x = c u

/-- A structure with an initial embedding of the sequences is a model of $\mathsf{WSeq}$. -/
lemma IsInitialEmbedding.models_WSeq {c : FiniteSequence → M} (hc : IsInitialEmbedding c) :
    M↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾 := by
  have hv (s : FiniteSequence) : s.toStructure = c s := by
    induction s with
    | nil => exact hc.map_nil.symm
    | snoc s t hs ht => rw [toStructure, hs, ht, hc.map_snoc]
  constructor
  intro σ h
  cases h
  case equal hφ =>
    have : M↓[ℒ⊢] ⊧* 𝗘𝗤 ℒ⊢ := inferInstance
    exact models_theory_iff.mp this _ hφ
  case ne s t h => simpa [models_iff, hv, hc.injective.eq_iff] using h
  case concat s t => simp [models_iff, hv, hc.map_append]
  case pref s =>
    simpa [models_iff, hv] using fun x h ↦ hc.exists_of_isPrefix (x := x) (s := s) h

/--
The sequences are a model of $\mathsf{WSeq}$.
- [KM24, §2]
-/
instance : FiniteSequence↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾 := IsInitialEmbedding.models_WSeq (c := id) {
  injective := Function.injective_id
  map_nil := rfl
  map_snoc _ _ := rfl
  map_append _ _ := rfl
  exists_of_isPrefix h := ⟨_, h, rfl⟩ }

end initial

section WSeq

variable {M : Type*} [SequenceStructure M] [M↓[ℒ⊢] ⊧* 𝗪𝗦𝗲𝗾] {x : M} {s t : FiniteSequence}

@[simp]
lemma toStructure_inj : (s.toStructure : M) = t.toStructure ↔ s = t := by
  constructor
  · contrapose
    intro h
    simpa [models_iff] using Theory.models M _ (IsWSeqAxiom.ne s t h)
  · rintro rfl
    rfl

lemma toStructure_append (s t : FiniteSequence) :
    ((s ++ t).toStructure : M) = s.toStructure ++ t.toStructure := by
  have := by simpa [models_iff] using Theory.models M _ (IsWSeqAxiom.concat s t)
  exact this.symm

/--
The initial segments of a standard sequence are its standard initial segments.
- [KM24, §2]
-/
lemma isPrefix_toStructure_iff : x ◨ s.toStructure ↔ ∃ u, u ◨ s ∧ x = u.toStructure := by
  constructor
  · have := by simpa [models_iff] using Theory.models M _ (IsWSeqAxiom.pref s)
    exact this x
  · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
    use v.toStructure
    rw [toStructure_append]

@[simp]
lemma toStructure_isPrefix_toStructure_iff : (s.toStructure : M) ◨ t.toStructure ↔ s ◨ t := by
  simp [isPrefix_toStructure_iff]

end WSeq

end Sequence

end FFL.FirstOrder

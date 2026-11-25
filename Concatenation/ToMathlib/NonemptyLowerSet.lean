module

public import Mathlib.Order.Sum.Order
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Hom

/-!
# Nonempty lower sets of a linear order

The linear order of nonempty lower sets, and its compatibility with lexicographic sums.
-/

@[expose] public section

/-- The nonempty lower sets of `α`. -/
abbrev NonemptyLowerSet (α : Type*) [LE α] : Type _ := {s : LowerSet α // (s : Set α).Nonempty}

namespace NonemptyLowerSet

variable {α β : Type*} [LinearOrder α] [LinearOrder β]

/-- The order isomorphism of nonempty lower sets induced by an order isomorphism. -/
def congr (e : α ≃o β) : NonemptyLowerSet α ≃o NonemptyLowerSet β where
  toEquiv := (LowerSet.map e).toEquiv.subtypeEquiv fun s ↦ by simp
  map_rel_iff' {s t} := (LowerSet.map e).le_iff_le (x := s.1) (y := t.1)

instance [Nonempty α] : Nonempty (NonemptyLowerSet α) := ⟨⊤, Set.univ_nonempty⟩

instance [IsEmpty α] : IsEmpty (NonemptyLowerSet α) := ⟨fun s ↦ isEmptyElim s.2.choose⟩

instance [Subsingleton α] : Subsingleton (NonemptyLowerSet α) where
  allEq s t := by
    ext x
    obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := And.intro s.2 t.2
    exact iff_of_true (Subsingleton.elim y x ▸ hy) (Subsingleton.elim z x ▸ hz)

/-- The nonempty lower set of `α ⊕ₗ β` that a nonempty lower set of `α` or of `β` gives. -/
def ofSum : NonemptyLowerSet α ⊕ₗ NonemptyLowerSet β → NonemptyLowerSet (α ⊕ₗ β)
  | .inl s => ⟨⟨{x | Sum.elim (· ∈ s.1) (fun _ ↦ False) (ofLex x)}, by
      rintro (a | a) (b | b) hab ha
      · exact s.1.lower (Sum.Lex.inl_le_inl_iff.mp hab) ha
      · exact Sum.Lex.not_inr_le_inl hab
      · exact (ha : False).elim
      · exact ha⟩, toLex (.inl s.2.choose), s.2.choose_spec⟩
  | .inr t => ⟨⟨{x | Sum.elim (fun _ ↦ True) (· ∈ t.1) (ofLex x)}, by
      rintro (a | a) (b | b) hab ha
      · trivial
      · exact (Sum.Lex.not_inr_le_inl hab).elim
      · trivial
      · exact t.1.lower (Sum.Lex.inr_le_inr_iff.mp hab) ha⟩,
      toLex (.inr t.2.choose), t.2.choose_spec⟩

lemma ofSum_le_ofSum : ∀ {x y : NonemptyLowerSet α ⊕ₗ NonemptyLowerSet β},
    ofSum x ≤ ofSum y ↔ x ≤ y
  | .inl _, .inl _ => ⟨fun h ↦ Sum.Lex.inl_le_inl_iff.mpr fun a ha ↦ h (a := toLex (.inl a)) ha,
    fun h ↦ by rintro (a | a) ha; exacts [Sum.Lex.inl_le_inl_iff.mp h ha, ha]⟩
  | .inl _, .inr _ => iff_of_true (by rintro (a | a) ha; exacts [trivial, ha.elim])
    (Sum.Lex.inl_le_inr _ _)
  | .inr t, .inl _ => iff_of_false
    (fun h ↦ h (a := toLex (.inr t.2.choose)) t.2.choose_spec) Sum.Lex.not_inr_le_inl
  | .inr _, .inr _ => ⟨fun h ↦ Sum.Lex.inr_le_inr_iff.mpr fun a ha ↦ h (a := toLex (.inr a)) ha,
    fun h ↦ by rintro (a | a) ha; exacts [trivial, Sum.Lex.inr_le_inr_iff.mp h ha]⟩

lemma ofSum_surjective : Function.Surjective (ofSum (α := α) (β := β)) := by
  intro s
  by_cases h : ∃ b : β, toLex (.inr b) ∈ s.1
  · use toLex (.inr ⟨⟨{b : β | (toLex (.inr b) : α ⊕ₗ β) ∈ s.1}, fun _ _ hab ha ↦
      s.1.lower (Sum.Lex.inr_le_inr_iff.mpr hab) ha⟩, h⟩)
    ext (a | b)
    · exact iff_of_true trivial (s.1.lower (Sum.Lex.inl_le_inr _ _) h.choose_spec)
    · exact Iff.rfl
  · push Not at h
    use toLex (.inl ⟨⟨{a : α | (toLex (.inl a) : α ⊕ₗ β) ∈ s.1}, fun _ _ hab ha ↦
      s.1.lower (Sum.Lex.inl_le_inl_iff.mpr hab) ha⟩, by
        obtain ⟨a | b, hx⟩ := s.2
        · exact ⟨a, hx⟩
        · exact (h b hx).elim⟩)
    ext (a | b)
    · exact Iff.rfl
    · exact iff_of_false id (h b)

/-- A nonempty lower set of a lexicographic sum is one of the left or of the right summand. -/
noncomputable def sumLex : NonemptyLowerSet α ⊕ₗ NonemptyLowerSet β ≃o NonemptyLowerSet (α ⊕ₗ β) :=
  RelIso.ofSurjective (OrderEmbedding.ofMapLEIff ofSum fun _ _ ↦ ofSum_le_ofSum) ofSum_surjective

end NonemptyLowerSet

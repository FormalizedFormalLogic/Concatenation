module

public import Concatenation.TC.NotationInduction
public import Concatenation.TC.Sequence

/-!
# Multiplication of tallies under notation induction

The multiplication sequences of the nonempty strings, and the multiplication of tallies that they
define in the models of $\Sigma_1\text{-}\mathsf{TCI}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open Bounding

section nonemptyPart

variable (V : Type*) [ConcatenationEmptyStructure V]

/-- The nonempty strings of `V`. -/
def NonemptyPart : Type _ := {x : V // x ≠ ∅}

variable {V} [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

/-- The letters and the concatenation of `V` restricted to the nonempty strings. -/
instance : ConcatenationStructure (NonemptyPart V) where
  zero := ⟨0, TCEmpty.zero_ne_empty⟩
  one := ⟨1, TCEmpty.one_ne_empty⟩
  append x y := ⟨x.1 ++ y.1, fun h ↦ x.2 (TCEmpty.eq_empty_of_append_eq_empty h).1⟩

namespace NonemptyPart

variable {x y z : NonemptyPart V} {c : V}

@[simp]
lemma val_zero : (0 : NonemptyPart V).1 = 0 := rfl

@[simp]
lemma val_one : (1 : NonemptyPart V).1 = 1 := rfl

@[simp]
lemma val_append (x y : NonemptyPart V) : (x ++ y).1 = x.1 ++ y.1 := rfl

omit [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] in
lemma ext_iff' : x = y ↔ x.1 = y.1 := Subtype.ext_iff

omit [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] in
lemma forall_iff {P : NonemptyPart V → Prop} : (∀ x, P x) ↔ ∀ x (hx : x ≠ ∅), P ⟨x, hx⟩ :=
  Subtype.forall

omit [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] in
lemma exists_iff {P : NonemptyPart V → Prop} : (∃ x, P x) ↔ ∃ x, ∃ hx : x ≠ ∅, P ⟨x, hx⟩ :=
  Subtype.exists

lemma isAtom_iff : IsAtom x ↔ IsAtom x.1 := by
  simp [IsAtom, ext_iff']

lemma isSubstring_iff : IsSubstring x y ↔ IsSubstring x.1 y.1 := by
  constructor
  · rintro (rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩)
    · exact IsSubstring.refl _
    · exact isSubstring_append_right _ _
    · exact isSubstring_append_left _ _
    · exact isSubstring_append_append _ _ _
    · simpa [TCEmpty.append_assoc] using isSubstring_append_append u.1 x.1 v.1
  · intro h
    obtain ⟨u, v, h⟩ := TCEmpty.isSubstring_iff.mp h
    by_cases hu : u = ∅ <;> by_cases hv : v = ∅
    · subst hu hv
      exact .inl (Subtype.ext (by simpa using h.symm))
    · subst hu
      exact .inr <| .inr <| .inl ⟨⟨v, hv⟩, Subtype.ext (by simpa using h : y.1 = x.1 ++ v)⟩
    · subst hv
      exact .inr <| .inl ⟨⟨u, hu⟩, Subtype.ext (by simpa using h : y.1 = u ++ x.1)⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨⟨u, hu⟩, ⟨v, hv⟩, Subtype.ext h⟩

lemma isPrefix_iff : x ◨ y ↔ IsPrefix x.1 y.1 := by
  constructor
  · rintro (rfl | ⟨v, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨v.1, rfl⟩
  · rintro (h | ⟨v, h⟩)
    · exact .inl (Subtype.ext h)
    · by_cases hv : v = ∅
      · exact .inl (Subtype.ext (by simpa [hv] using h.symm))
      · exact .inr ⟨⟨v, hv⟩, Subtype.ext h⟩

lemma isSuffix_iff : x ◧ y ↔ IsSuffix y.1 x.1 := by
  constructor
  · rintro (rfl | ⟨u, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨u.1, rfl⟩
  · rintro (h | ⟨u, h⟩)
    · exact .inl (Subtype.ext h)
    · by_cases hu : u = ∅
      · exact .inl (Subtype.ext (by simpa [hu] using h.symm))
      · exact .inr ⟨⟨u, hu⟩, Subtype.ext h⟩

lemma isTally_iff : IsTally y x ↔ IsTally y.1 x.1 := by
  constructor
  · intro h z hz hzx
    have := h ⟨z, TCEmpty.isAtom_ne_empty hz⟩ (isAtom_iff.mpr hz) (isSubstring_iff.mpr hzx)
    exact congrArg Subtype.val this
  · intro h z hz hzx
    exact Subtype.ext <| h z.1 (isAtom_iff.mp hz) (isSubstring_iff.mp hzx)

@[simp]
lemma val_pairOf (x y : NonemptyPart V) : (pairOf x y).1 = pairOf x.1 y.1 := rfl

end NonemptyPart

/--
The nonempty strings of a model of $\mathsf{TC}$ with the empty string form a model of
$\mathsf{TC}$.
- [Vis09, Appendix A]
-/
instance NonemptyPart.models_TC : (NonemptyPart V)↓[ℒ⌢] ⊧* 𝗧𝗖 := by
  constructor
  intro σ hσ
  cases hσ
  case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
  case editor =>
    suffices ∀ x y z w : NonemptyPart V, x ++ y = z ++ w → (x = z ∧ y = w) ∨
        ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by simpa [models_iff]
    intro x y z w h
    obtain ⟨u, hu⟩ := TCEmpty.editor (congrArg Subtype.val h)
    by_cases hu' : u = ∅
    · subst hu'
      exact .inl <| by simpa [NonemptyPart.ext_iff'] using hu
    · refine .inr ⟨⟨u, hu'⟩, ?_⟩
      rcases hu with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact .inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩
      · exact .inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩
  case zeroNeConcat =>
    simpa [models_iff] using fun (x y : NonemptyPart V) (h : 0 = x ++ y) ↦
      (TCEmpty.eq_empty_of_append_isAtom (x := x.1) (y := y.1) <| by
        rw [← show (0 : V) = x.1 ++ y.1 from congrArg Subtype.val h]; simp).elim x.2 y.2
  case oneNeConcat =>
    simpa [models_iff] using fun (x y : NonemptyPart V) (h : 1 = x ++ y) ↦
      (TCEmpty.eq_empty_of_append_isAtom (x := x.1) (y := y.1) <| by
        rw [← show (1 : V) = x.1 ++ y.1 from congrArg Subtype.val h]; simp).elim x.2 y.2
  case concatAssoc =>
    have h (x y z : NonemptyPart V) : x ++ (y ++ z) = x ++ y ++ z :=
      NonemptyPart.ext_iff'.mpr (TCEmpty.append_assoc x.1 y.1 z.1).symm
    simpa [models_iff] using h
  case zeroNeOne =>
    simp [models_iff, NonemptyPart.ext_iff']

/--
The nonempty strings of a model of $\Delta_0$ notation induction form a model of $\mathsf{TC}^+$.
- [Gan09, §3]
-/
instance NonemptyPart.models_TCPlus [V↓[ℒ⌢ₑ] ⊧* TCISigma 1] : (NonemptyPart V)↓[ℒ⌢] ⊧* 𝗧𝗖⁺ := by
  have h (x : NonemptyPart V) : IsBounded x := by
    by_cases hx : IsAtom x
    · exact .inl hx
    refine .inr ⟨?_, ?_⟩
    · rcases TCISigma.eq_empty_or_eq_isAtom_append x.1 with h | ⟨c, u, hc, hu⟩
      · exact absurd h x.2
      by_cases hu' : u = ∅
      · exact absurd (NonemptyPart.isAtom_iff.mpr (by simpa [hu, hu'] using hc)) hx
      · exact ⟨⟨c, TCEmpty.isAtom_ne_empty hc⟩, ⟨u, hu'⟩, NonemptyPart.isAtom_iff.mpr hc,
          Subtype.ext hu⟩
    · rcases TCISigma.eq_empty_or_eq_append_isAtom x.1 with h | ⟨u, c, hc, hu⟩
      · exact absurd h x.2
      by_cases hu' : u = ∅
      · exact absurd (NonemptyPart.isAtom_iff.mpr (by simpa [hu, hu'] using hc)) hx
      · exact ⟨⟨c, TCEmpty.isAtom_ne_empty hc⟩, ⟨u, hu'⟩, NonemptyPart.isAtom_iff.mpr hc,
          Subtype.ext hu⟩
  have hT : (NonemptyPart V)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  simpa [models_iff, allIsBounded] using ⟨h, fun φ hφ ↦ models_theory_iff.mp hT φ hφ⟩

end nonemptyPart

section boundedDefinitions

local notation "ℬₛ" => substringBounding ℒ⌢ₑ

variable {V : Type*} [ConcatenationEmptyStructure V]

/-- `x` is a prefix of `y`. -/
def isPrefixBoundedDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “x y. ∃¹[%(substringOperator _) #0 y] y = x ⌢ #0”

instance isPrefix_bounded_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    𝚺-[ℬₛ, 0]-Relation[V] IsPrefix via isPrefixBoundedDef := .mk fun v ↦ by
  suffices (∃ u, IsSubstring u (v 1) ∧ v 1 = v 0 ++ u) ↔ IsPrefix (v 0) (v 1) by
    simpa [isPrefixBoundedDef]
  constructor
  · rintro ⟨u, -, h⟩
    exact .inr ⟨u, h⟩
  · rintro (h | ⟨u, h⟩)
    · exact ⟨∅, by simp, by simp [h]⟩
    · exact ⟨u, h ▸ isSubstring_append_right _ _, h⟩

/-- `x` is a suffix of `y`. -/
def isSuffixBoundedDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “x y. ∃¹[%(substringOperator _) #0 y] y = #0 ⌢ x”

instance isSuffix_bounded_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    𝚺-[ℬₛ, 0]-Relation[V] IsSuffix via isSuffixBoundedDef := .mk fun v ↦ by
  suffices (∃ u, IsSubstring u (v 1) ∧ v 1 = u ++ v 0) ↔ IsSuffix (v 0) (v 1) by
    simpa [isSuffixBoundedDef]
  constructor
  · rintro ⟨u, -, h⟩
    exact .inr ⟨u, h⟩
  · rintro (h | ⟨u, h⟩)
    · exact ⟨∅, by simp, by simp [h]⟩
    · exact ⟨u, h ▸ isSubstring_append_left _ _, h⟩

/-- `x` is a `c`-tally. -/
def isTallyBoundedDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “c x. ∀¹[%(substringOperator _) #0 x]
    (#0 = !!(op(0).const) ∨ #0 = !!(op(1).const) → #0 = c)”

instance isTally_bounded_defined : 𝚺-[ℬₛ, 0]-Relation[V] IsTally via isTallyBoundedDef :=
  .mk fun v ↦ by simp [isTallyBoundedDef, IsTally, Concatenation.IsAtom]; grind

/-- `x` is a substring of `y`. -/
def isSubstringBoundedDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “x y. ∃¹[%(substringOperator _) #0 y] #0 = x”

instance isSubstring_bounded_defined :
    𝚺-[ℬₛ, 0]-Relation[V] IsSubstring via isSubstringBoundedDef :=
  .mk fun v ↦ by simp [isSubstringBoundedDef]

/--
`r` is a sequence of nonempty strings: it begins with `001`, ends with `100`, and its only
nonempty `0`-tally substrings are `0` and `00`.
- [Gan09, §1, Definition 1(d)]
-/
def IsSeqₑ (r : V) : Prop :=
  IsPrefix (0 ++ 0 ++ 1) r ∧ IsSuffix (1 ++ 0 ++ 0) r ∧
    ∀ t, IsSubstring t r → t ≠ ∅ → IsTally 0 t → t = 0 ∨ t = 0 ++ 0

/-- `r` is a sequence of nonempty strings. -/
def isSeqₑDef : 𝚺-[ℬₛ, 0].Semisentence 1 :=
  .mkSigma “r. !isPrefixBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const) ⌢ !!(op(1).const)) r ∧
    !isSuffixBoundedDef.val (!!(op(1).const) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) r ∧
    ∀¹[%(substringOperator _) #0 r] (#0 ≠ ⋆ → !isTallyBoundedDef.val !!(op(0).const) #0 →
      #0 = !!(op(0).const) ∨ #0 = !!(op(0).const) ⌢ !!(op(0).const))”

instance isSeqₑ_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : 𝚺-[ℬₛ, 0]-Predicate[V] IsSeqₑ via isSeqₑDef :=
  .mk fun v ↦ by simp [isSeqₑDef, IsSeqₑ]

/--
`y` is a member of the sequence `r`.
- [Gan09, §1, Definition 1(e)]
-/
def Memₑ (y r : V) : Prop :=
  IsSeqₑ r ∧ ¬IsSubstring (0 ++ 0) y ∧ IsSubstring (0 ++ 0 ++ y ++ 0 ++ 0) r

/-- `y` is a member of the sequence `r`. -/
def memₑDef : 𝚺-[ℬₛ, 0].Semisentence 2 :=
  .mkSigma “y r. !isSeqₑDef.val r ∧
    ¬!isSubstringBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const)) y ∧
    !isSubstringBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const) ⌢ y ⌢ !!(op(0).const) ⌢
      !!(op(0).const)) r”

instance memₑ_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] : 𝚺-[ℬₛ, 0]-Relation[V] Memₑ via memₑDef :=
  .mk fun v ↦ by simp [memₑDef, Memₑ]

/--
`r` is a sequence of ordered pairs of nonempty `1`-tallies.
- [Gan09, §1, Definition 1(e)]
-/
def IsPairSeqₑ (r : V) : Prop :=
  IsSeqₑ r ∧ ∀ y, IsSubstring y r → y ≠ ∅ → Memₑ y r →
    ∃ a, IsSubstring a y ∧ ∃ b, IsSubstring b y ∧
      a ≠ ∅ ∧ b ≠ ∅ ∧ IsTally 1 a ∧ IsTally 1 b ∧ y = pairOf a b

/-- `r` is a sequence of ordered pairs of nonempty `1`-tallies. -/
def isPairSeqₑDef : 𝚺-[ℬₛ, 0].Semisentence 1 :=
  .mkSigma “r. !isSeqₑDef.val r ∧ ∀¹[%(substringOperator _) #0 r] (#0 ≠ ⋆ → !memₑDef.val #0 r →
    ∃¹[%(substringOperator _) #0 #1] ∃¹[%(substringOperator _) #0 #2]
      (#1 ≠ ⋆ ∧ #0 ≠ ⋆ ∧ !isTallyBoundedDef.val !!(op(1).const) #1 ∧
        !isTallyBoundedDef.val !!(op(1).const) #0 ∧ #2 = #1 ⌢ !!(op(0).const) ⌢ #0))”

instance isPairSeqₑ_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    𝚺-[ℬₛ, 0]-Predicate[V] IsPairSeqₑ via isPairSeqₑDef :=
  .mk fun v ↦ by simp [isPairSeqₑDef, IsPairSeqₑ, pairOf]

/--
`r` is a multiplication sequence for the nonempty `1`-tallies `x` and `y`.
- [Gan09, §1, Definition 1(g)]
- [Sve09, §3]
-/
def IsMulSeqₑ (x y r : V) : Prop :=
  x ≠ ∅ ∧ y ≠ ∅ ∧ r ≠ ∅ ∧ IsTally 1 x ∧ IsTally 1 y ∧ IsPairSeqₑ r ∧
    IsPrefix (0 ++ 0 ++ pairOf x 1 ++ 0 ++ 0) r ∧
    (∃ w, IsSubstring w r ∧ w ≠ ∅ ∧ IsTally 1 w ∧ IsSuffix (0 ++ 0 ++ pairOf w y ++ 0 ++ 0) r) ∧
    ∀ s, IsSubstring s r → ∀ u', IsSubstring u' r → ∀ v', IsSubstring v' r →
      s ≠ ∅ → u' ≠ ∅ → v' ≠ ∅ → IsTally 1 u' → IsTally 1 v' →
      IsPrefix (s ++ 0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) r →
      ∃ u, IsSubstring u u' ∧ ∃ v, IsSubstring v v' ∧ u ≠ ∅ ∧ v ≠ ∅ ∧
        IsTally 1 u ∧ IsTally 1 v ∧ u' = u ++ x ∧ v' = v ++ 1 ∧
        IsSuffix (0 ++ 0 ++ pairOf u v) s

/-- `r` is a multiplication sequence for the nonempty `1`-tallies `x` and `y`. -/
def isMulSeqₑDef : 𝚺-[ℬₛ, 0].Semisentence 3 :=
  .mkSigma “x y r. x ≠ ⋆ ∧ y ≠ ⋆ ∧ r ≠ ⋆ ∧ !isTallyBoundedDef.val !!(op(1).const) x ∧
    !isTallyBoundedDef.val !!(op(1).const) y ∧ !isPairSeqₑDef.val r ∧
    !isPrefixBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const) ⌢
      (x ⌢ !!(op(0).const) ⌢ !!(op(1).const)) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) r ∧
    (∃¹[%(substringOperator _) #0 r] (#0 ≠ ⋆ ∧ !isTallyBoundedDef.val !!(op(1).const) #0 ∧
      !isSuffixBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const) ⌢
        (#0 ⌢ !!(op(0).const) ⌢ y) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) r)) ∧
    ∀¹[%(substringOperator _) #0 r] ∀¹[%(substringOperator _) #0 r] ∀¹[%(substringOperator _) #0 r]
      (#2 ≠ ⋆ → #1 ≠ ⋆ → #0 ≠ ⋆ → !isTallyBoundedDef.val !!(op(1).const) #1 →
        !isTallyBoundedDef.val !!(op(1).const) #0 →
        !isPrefixBoundedDef.val (#2 ⌢ !!(op(0).const) ⌢ !!(op(0).const) ⌢
          (#1 ⌢ !!(op(0).const) ⌢ #0) ⌢ !!(op(0).const) ⌢ !!(op(0).const)) r →
        ∃¹[%(substringOperator _) #0 #2] ∃¹[%(substringOperator _) #0 #2]
          (#1 ≠ ⋆ ∧ #0 ≠ ⋆ ∧ !isTallyBoundedDef.val !!(op(1).const) #1 ∧
            !isTallyBoundedDef.val !!(op(1).const) #0 ∧ #3 = #1 ⌢ x ∧
            #2 = #0 ⌢ !!(op(1).const) ∧
            !isSuffixBoundedDef.val (!!(op(0).const) ⌢ !!(op(0).const) ⌢
              (#1 ⌢ !!(op(0).const) ⌢ #0)) #4))”

instance isMulSeqₑ_defined [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ] :
    𝚺-[ℬₛ, 0]-Relation₃[V] IsMulSeqₑ via isMulSeqₑDef :=
  .mk fun v ↦ by simp [isMulSeqₑDef, IsMulSeqₑ, pairOf]

end boundedDefinitions

section transfer

variable {V : Type*} [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* 𝗧𝗖ₑ]

namespace NonemptyPart

variable {x y z r : NonemptyPart V}

lemma isSeq_iff_isSeqₑ : IsSeq r ↔ IsSeqₑ r.1 := by
  simp only [Concatenation.isSeq_iff, IsSeqₑ, isPrefix_iff, isSuffix_iff, isTally_iff, isSubstring_iff,
    ext_iff', val_append, val_zero, forall_iff]
  exact and_congr Iff.rfl <| and_congr Iff.rfl
    ⟨fun h t ht hn hT ↦ h t hn hT ht, fun h t hn hT ht ↦ h t ht hn hT⟩

lemma mem_iff_memₑ : Mem y r ↔ Memₑ y.1 r.1 := by
  simp only [Mem, Memₑ, isSeq_iff_isSeqₑ, isSubstring_iff, val_append, val_zero]

lemma isSubstring_of_memₑ {y r : V} (h : Memₑ y r) : IsSubstring y r :=
  TCEmpty.isSubstring_trans (TCEmpty.isSubstring_append_right_of
    (isSubstring_append_append (0 ++ 0) y 0) 0) h.2.2

lemma isPairSeq_iff_isPairSeqₑ : IsPairSeq r ↔ IsPairSeqₑ r.1 := by
  simp only [Concatenation.isPairSeq_iff, IsPairSeqₑ, isSeq_iff_isSeqₑ, mem_iff_memₑ, IsPair, isTally_iff, ext_iff',
    val_pairOf, val_one, forall_iff, exists_iff]
  refine and_congr Iff.rfl ⟨fun h y hyr hy hm ↦ ?_, fun h y hy hm ↦ ?_⟩
  · obtain ⟨a, ha, b, hb, hta, htb, rfl⟩ := h y hy hm
    exact ⟨a, TCEmpty.isSubstring_append_right_of (isSubstring_append_left a 0) b, b,
      isSubstring_append_right _ b, ha, hb, hta, htb, rfl⟩
  · obtain ⟨a, -, b, -, ha, hb, hta, htb, rfl⟩ := h y (isSubstring_of_memₑ hm) hy hm
    exact ⟨a, ha, b, hb, hta, htb, rfl⟩

lemma isMulSeq_iff_isMulSeqₑ : IsMulSeq x y r ↔ IsMulSeqₑ x.1 y.1 r.1 := by
  have hsub {a b : V} (u v : V) (h : IsSubstring (u ++ a ++ v) b) : IsSubstring a b :=
    TCEmpty.isSubstring_trans (isSubstring_append_append u a v) h
  simp only [Concatenation.isMulSeq_iff, IsMulSeqₑ, isTally_iff, isPairSeq_iff_isPairSeqₑ,
    IsFirst, IsLast, isPrefix_iff, isSuffix_iff, val_append, val_pairOf, val_zero, val_one,
    forall_iff, exists_iff, ext_iff']
  constructor
  · rintro ⟨tx, ty, ps, first, ⟨w, hw, tw, last⟩, pred⟩
    refine ⟨x.2, y.2, r.2, tx, ty, ps, first, ⟨w, ?_, hw, tw, last⟩, ?_⟩
    · exact hsub (0 ++ 0) (0 ++ y.1 ++ 0 ++ 0) <| by
        simpa [pairOf, TCEmpty.append_assoc] using last.isSubstring
    · intro s _ u' _ v' _ hs hu' hv' tu' tv' pre
      obtain ⟨u, hu, v, hv, tu, tv, rfl, rfl, suf⟩ := pred s hs u' hu' v' hv' tu' tv' pre
      exact ⟨u, isSubstring_append_left u x.1, v, isSubstring_append_left v 1, hu, hv, tu, tv,
        rfl, rfl, suf⟩
  · rintro ⟨-, -, -, tx, ty, ps, first, ⟨w, -, hw, tw, last⟩, pred⟩
    refine ⟨tx, ty, ps, first, ⟨w, hw, tw, last⟩, ?_⟩
    intro s hs u' hu' v' hv' tu' tv' pre
    have hpre := pre.isSubstring
    obtain ⟨u, -, v, -, hu, hv, tu, tv, h₁, h₂, suf⟩ := pred
      s (hsub ∅ (0 ++ 0 ++ pairOf u' v' ++ 0 ++ 0) <| by
        simpa [TCEmpty.append_assoc] using hpre)
      u' (hsub (s ++ 0 ++ 0) (0 ++ v' ++ 0 ++ 0) <| by
        simpa [pairOf, TCEmpty.append_assoc] using hpre)
      v' (hsub (s ++ 0 ++ 0 ++ u' ++ 0) (0 ++ 0) <| by
        simpa [pairOf, TCEmpty.append_assoc] using hpre)
      hs hu' hv' tu' tv' pre
    exact ⟨u, hu, v, hv, tu, tv, h₁, h₂, suf⟩

end NonemptyPart

end transfer

end FFL.FirstOrder.Concatenation

module

public import Concatenation.Semantics.Standard
public import Concatenation.TC.Substring
public import AlphaCentauri.Interpretability.Basic

/-!
# Thin strings

$\mathsf{TC}$ interprets $\mathsf{TC}^+$ on the strings all of whose substrings are bounded.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

variable {M : Type*} [ConcatenationStructure M] {x y : M}

/--
`x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def IsBounded (x : M) : Prop :=
  IsAtom x ∨ ((∃ c z, IsAtom c ∧ x = c ++ z) ∧ ∃ c z, IsAtom c ∧ x = z ++ c)

/--
`x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def isBounded : Semisentence ℒ⌢ 1 :=
  “x. !isAtom x ∨ ((∃ c z, !isAtom c ∧ x = c ⌢ z) ∧ (∃ c z, !isAtom c ∧ x = z ⌢ c))”

@[simp]
lemma eval_isBounded : M ⊧/![x] isBounded ↔ IsBounded x := by
  simp [isBounded, IsBounded]

/--
Every string is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def tc6 : ConcatenationSentence := “∀ x, !isBounded x”

/--
$\mathsf{TC}$ with the axiom that every string is an atom, or begins with an atom and ends with
an atom.
- [Gan09, §3]
-/
abbrev TCPlus : ConcatenationTheory := insert tc6 𝗧𝗖

@[inherit_doc]
notation "𝗧𝗖⁺" => TCPlus

instance : 𝗧𝗖 ⪯ 𝗧𝗖⁺ := Entailment.WeakerThan.ofSubset <| Set.subset_insert _ _

instance : 𝗘𝗤 ℒ⌢ ⪯ 𝗧𝗖⁺ :=
  Entailment.WeakerThan.ofSubset fun φ hφ ↦ Set.mem_insert_of_mem _ <| IsTCAxiom.equal φ hφ

/--
`x` is thin: every substring of `x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def IsThin (x : M) : Prop := ∀ y, IsSubstring y x → IsBounded y

/--
`x` is thin: every substring of `x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def isThin : Semisentence ℒ⌢ 1 := “x. ∀ y, !isSubstring y x → !isBounded y”

@[simp]
lemma eval_isThin : M ⊧/![x] isThin ↔ IsThin x := by
  simp [isThin, IsThin]

lemma TCPlus.isBounded [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺] (x : M) : IsBounded x := by
  have := by simpa [models_iff, tc6] using Theory.models M _ (Set.mem_insert tc6 𝗧𝗖)
  exact this x

instance [M↓[ℒ⌢] ⊧* 𝗧𝗖⁺] : M↓[ℒ⌢] ⊧* 𝗧𝗖 :=
  models_of_ss (U := 𝗧𝗖⁺) inferInstance <| Set.subset_insert _ _

lemma IsAtom.isBounded (h : IsAtom x) : IsBounded x := Or.inl h

lemma IsThin.isBounded (h : IsThin x) : IsBounded x := h x (IsSubstring.refl x)

section TC

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

lemma IsBounded.append (hx : IsBounded x) (hy : IsBounded y) : IsBounded (x ++ y) := by
  right
  constructor
  · rcases hx with hx | ⟨⟨c, z, hc, rfl⟩, -⟩
    · use x, y
    · use c, z ++ y
      simp [hc, Concatenation.append_assoc]
  · rcases hy with hy | ⟨-, ⟨c, z, hc, rfl⟩⟩
    · use y, x
    · use c, x ++ z
      simp [hc, Concatenation.append_assoc]

lemma IsThin.of_isSubstring (hx : IsThin x) (h : IsSubstring y x) : IsThin y :=
  fun z hz ↦ hx z (hz.trans h)

lemma IsAtom.isThin (h : IsAtom x) : IsThin x := fun _ hy ↦ (h.eq_of_isSubstring hy ▸ h).isBounded

lemma isThin_zero : IsThin (0 : M) := isAtom_zero.isThin

lemma isThin_one : IsThin (1 : M) := isAtom_one.isThin

/--
The concatenation of thin strings is thin.
- [Gan09, §3, Lemma 6]
-/
lemma IsThin.append (hx : IsThin x) (hy : IsThin y) : IsThin (x ++ y) := by
  intro z hz
  rcases hz.append_cases with h | h | ⟨z₁, z₂, rfl, h₁, h₂⟩
  · exact hx z h
  · exact hy z h
  · exact (hx z₁ h₁.isSubstring).append (hy z₂ h₂.isSubstring)

end TC

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖⁺ := by
  have h (x : FreeSemigroup Bool) : IsBounded x := by
    induction x using FreeSemigroup.recOnMul with
    | ih1 b =>
      apply IsAtom.isBounded
      cases b
      · exact isAtom_zero
      · exact isAtom_one
    | ih2 b x hb hx => exact hb.append hx
  have hT : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  simpa [models_iff, tc6] using ⟨h, fun φ hφ ↦ models_theory_iff.mp hT φ hφ⟩

/--
The translation of $\mathsf{TC}$ into itself relativized to the thin strings.
- [Gan09, §3, Lemma 6]
-/
def thinTranslation : DirectTranslation 𝗧𝗖 ℒ⌢ where
  domain := ⟨isThin⟩
  rel R := ⟨Semiformula.rel R (#·)⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using isThin_zero
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsThin (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : M, IsThin y ∧ y = 0 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 0
      simp [isThin_zero]
    · suffices ∃! y : M, IsThin y ∧ y = 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 1
      simp [isThin_one]
    · suffices ∃! y : M, IsThin y ∧ y = e 0 ++ e 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use e 0 ++ e 1
      simp [(he 0).append (he 1)]
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val]

@[simp]
lemma thinTranslation_dom_iff : thinTranslation.Dom x ↔ IsThin x := by
  simp [dom_iff, thinTranslation, Semiformula.Operator.val]

section model

variable [M↓[ℒ⌢] ⊧* 𝗧𝗖]

/-- The letters and the concatenation of `M` restricted to the thin strings. -/
abbrev thinTranslation.concatenationStructure :
    ConcatenationStructure (thinTranslation.Model M) where
  zero := ⟨0, by simpa using isThin_zero⟩
  one := ⟨1, by simpa using isThin_one⟩
  append x y := ⟨x ++ y, by
    simpa using (thinTranslation_dom_iff.mp x.dom).append (thinTranslation_dom_iff.mp y.dom)⟩

/--
The structure of the model of `thinTranslation` is the standard one of the letters and the
concatenation restricted to the thin strings.
-/
lemma thinTranslation.struc_eq :
    Model.struc thinTranslation M = @standardModel _ thinTranslation.concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [thinTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

/--
The thin strings of a model of $\mathsf{TC}$ form a model of $\mathsf{TC}^+$.
- [Gan09, §3, Lemma 6]
-/
instance : (thinTranslation.Model M)↓[ℒ⌢] ⊧* 𝗧𝗖⁺ := by
  rw [thinTranslation.struc_eq]
  let := thinTranslation.concatenationStructure (M := M)
  have thin (x : thinTranslation.Model M) : IsThin (x : M) := thinTranslation_dom_iff.mp x.dom
  constructor
  intro σ hσ
  rcases hσ with rfl | hσ
  · suffices ∀ x : thinTranslation.Model M, IsBounded x by simpa [models_iff, tc6]
    intro x
    rcases (thin x).isBounded with h | ⟨⟨c, z, hc, hcz⟩, ⟨c', z', hc', hzc⟩⟩
    · exact Or.inl <| h.imp Model.ext Model.ext
    · right
      constructor
      · use ⟨c, thinTranslation_dom_iff.mpr hc.isThin⟩,
          ⟨z, thinTranslation_dom_iff.mpr <| (thin x).of_isSubstring <| by simp [hcz]⟩
        exact ⟨hc.imp Model.ext Model.ext, Model.ext hcz⟩
      · use ⟨c', thinTranslation_dom_iff.mpr hc'.isThin⟩,
          ⟨z', thinTranslation_dom_iff.mpr <| (thin x).of_isSubstring <| by simp [hzc]⟩
        exact ⟨hc'.imp Model.ext Model.ext, Model.ext hzc⟩
  · cases hσ
    case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
    case concatAssoc =>
      suffices ∀ x y z : thinTranslation.Model M, x ++ (y ++ z) = x ++ y ++ z by
        simpa [models_iff]
      exact fun x y z ↦ Model.ext (Concatenation.append_assoc (x : M) y z).symm
    case editor =>
      suffices ∀ x y z w : thinTranslation.Model M, x ++ y = z ++ w →
          (x = z ∧ y = w) ∨ ∃ u, (x ++ u = z ∧ y = u ++ w) ∨ (x = z ++ u ∧ u ++ y = w) by
        simpa [models_iff]
      intro x y z w h
      rcases editor (congrArg Model.val h) with ⟨h₁, h₂⟩ | ⟨u, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
      · exact Or.inl ⟨Model.ext h₁, Model.ext h₂⟩
      · right
        use ⟨u, thinTranslation_dom_iff.mpr <| (thin z).of_isSubstring <| by simp [← h₁]⟩
        exact Or.inl ⟨Model.ext h₁, Model.ext h₂⟩
      · right
        use ⟨u, thinTranslation_dom_iff.mpr <| (thin x).of_isSubstring <| by simp [h₁]⟩
        exact Or.inr ⟨Model.ext h₁, Model.ext h₂⟩
    case zeroNeConcat =>
      suffices ∀ x y : thinTranslation.Model M, 0 ≠ x ++ y by simpa [models_iff]
      exact fun x y h ↦ zero_ne_append (x : M) y (congrArg Model.val h)
    case oneNeConcat =>
      suffices ∀ x y : thinTranslation.Model M, 1 ≠ x ++ y by simpa [models_iff]
      exact fun x y h ↦ one_ne_append (x : M) y (congrArg Model.val h)
    case zeroNeOne =>
      suffices (0 : thinTranslation.Model M) ≠ 1 by simpa [models_iff]
      exact fun h ↦ Concatenation.zero_ne_one (congrArg Model.val h)

end model

/--
$\mathsf{TC}$ interprets $\mathsf{TC}^+$ on the thin strings.
- [Gan09, §3, Lemma 6]
-/
instance : 𝗧𝗖 ⊳ 𝗧𝗖⁺ where
  trln := thinTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

end FFL.FirstOrder.Concatenation

module

public import AlphaCentauri.Interpretability.Basic
public import Concatenation.TC.Basic
public import Concatenation.ToFoundation.Interpretability.LocallyFinitelySatisfiable
public import Concatenation.ToMathlib.Infinite

/-!
# Substrings in models of $\mathsf{TC}$

Atoms, substrings and tallies in the models of $\mathsf{TC}$, which are infinite, and the
interpretation of $\mathsf{TC}^+$ in $\mathsf{TC}$ on the thin strings.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation

section substring

variable {V : Type*} [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗧𝗖] {c c' d t u v x y y' z : V}

lemma isSubstring_iff : IsSubstring x y ↔ x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨
    ∃ u v, y = u ++ x ++ v := by
  simp [IsSubstring, Concatenation.append_assoc]

lemma IsSubstring.append_left (h : IsSubstring x y) : IsSubstring x (u ++ y) := by
  rcases isSubstring_iff.mp h with rfl | ⟨u', rfl⟩ | ⟨v, rfl⟩ | ⟨u', v, rfl⟩
  · simp
  · simpa [Concatenation.append_assoc] using isSubstring_append_right (u ++ u') x
  · simpa [Concatenation.append_assoc] using isSubstring_append_append u x v
  · simpa [Concatenation.append_assoc] using isSubstring_append_append (u ++ u') x v

lemma IsSubstring.append_right (h : IsSubstring x y) : IsSubstring x (y ++ v) := by
  grind [isSubstring_iff, Concatenation.append_assoc]

@[trans]
lemma IsSubstring.trans (hxy : IsSubstring x y) (hyz : IsSubstring y z) : IsSubstring x z := by
  grind [isSubstring_iff, IsSubstring.append_left, IsSubstring.append_right]

@[grind .]
lemma IsAtom.ne_append (hc : IsAtom c) : c ≠ x ++ y := by
  rcases hc with rfl | rfl <;> simp

lemma IsAtom.eq_of_append_eq_append (hc : IsAtom c) (hc' : IsAtom c') (h : y ++ c = y' ++ c') :
    c = c' ∧ y = y' := by
  rcases editor h with ⟨rfl, rfl⟩ | ⟨u, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ <;> grind

lemma IsAtom.eq_of_append_eq_append_left (hc : IsAtom c) (hc' : IsAtom c') (h : c ++ y = c' ++ y') :
    c = c' ∧ y = y' := by
  rcases editor h with ⟨rfl, rfl⟩ | ⟨u, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ <;> grind

lemma IsAtom.append_right_cancel (hc : IsAtom c) (h : x ++ c = y ++ c) : x = y :=
  (hc.eq_of_append_eq_append hc h).2

lemma IsAtom.append_left_cancel (hc : IsAtom c) (h : c ++ x = c ++ y) : x = y :=
  (hc.eq_of_append_eq_append_left hc h).2

/--
A substring of `x ++ y` is a substring of `x` or of `y`, or splits into a suffix of `x`
followed by a prefix of `y`.
- [Gan09, §3, Lemma 5]
-/
lemma IsSubstring.append_cases (h : IsSubstring z (x ++ y)) :
    IsSubstring z x ∨ IsSubstring z y ∨
      ∃ z₁ z₂, z = z₁ ++ z₂ ∧ x ◧ z₁ ∧ z₂ ◨ y := by
  rcases isSubstring_iff.mp h with rfl | ⟨u, h⟩ | ⟨v, h⟩ | ⟨u, v, h⟩
  · right; right; use x, y
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · simp
    · right; right; use w, y; simp
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · right; right; use x, w; simp
    · simp
  · rcases editor h with ⟨rfl, rfl⟩ | ⟨w, ⟨hw, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · rcases editor hw with ⟨rfl, rfl⟩ | ⟨w', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · simp
      · simp
      · right; right; use w', w; simp
    · simp

lemma IsAtom.eq_of_isSubstring (hc : IsAtom c) (h : IsSubstring x c) : x = c := by
  grind [isSubstring_iff]

lemma isTally_self (hc : IsAtom c) : IsTally c c := fun _ _ h ↦ hc.eq_of_isSubstring h

lemma not_isTally_one_zero : ¬IsTally (1 : V) 0 := fun h ↦
  Concatenation.zero_ne_one <| h 0 isAtom_zero (IsSubstring.refl _)

lemma isTally_one_one : IsTally (1 : V) 1 := isTally_self isAtom_one

lemma IsTally.of_isSubstring (hx : IsTally c x) (h : IsSubstring y x) : IsTally c y :=
  fun z hz hzy ↦ hx z hz (hzy.trans h)

lemma IsTally.append (hx : IsTally c x) (hy : IsTally c y) : IsTally c (x ++ y) := by
  intro z hz h
  rcases h.append_cases with h | h | ⟨z₁, z₂, h, -, -⟩
  exacts [hx z hz h, hy z hz h, absurd h hz.ne_append]

lemma IsTally.not_isSubstring_zero (hx : IsTally 1 x) : ¬IsSubstring 0 x := fun h ↦
  Concatenation.zero_ne_one <| hx 0 isAtom_zero h

lemma IsTally.not_isSubstring_one (hx : IsTally 0 x) : ¬IsSubstring 1 x := fun h ↦
  Concatenation.zero_ne_one (hx 1 isAtom_one h).symm

lemma IsTally.append_one (hx : IsTally 1 x) : IsTally 1 (x ++ 1) := hx.append isTally_one_one

lemma IsTally.ne_zero (hx : IsTally 1 x) : x ≠ 0 := by
  rintro rfl
  exact not_isTally_one_zero hx

lemma IsTally.ne_zero_append_zero (hx : IsTally 1 x) : x ≠ 0 ++ 0 := by
  rintro rfl
  exact hx.not_isSubstring_zero <| isSubstring_append_left 0 0

lemma append_one_ne_zero_append_zero (x : V) : x ++ 1 ≠ 0 ++ 0 := fun h ↦
  Concatenation.zero_ne_one (isAtom_one.eq_of_append_eq_append isAtom_zero h).1.symm

lemma IsSuffix.append_left (h : y ◧ x) : u ++ y ◧ x := by
  rcases h with rfl | ⟨u', rfl⟩
  · simp
  · right; use u ++ u'; simp [Concatenation.append_assoc]

lemma IsPrefix.append_right (h : x ◨ y) : x ◨ y ++ v := by
  grind [IsPrefix, Concatenation.append_assoc]

lemma IsSuffix.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : x ◧ c)
    (h' : x ◧ c') : c = c' := by
  grind [IsSuffix, IsAtom.eq_of_append_eq_append]

lemma IsPrefix.eq_of_isAtom (hc : IsAtom c) (hc' : IsAtom c') (h : c ◨ x)
    (h' : c' ◨ x) : c = c' := by
  grind [IsPrefix, IsAtom.eq_of_append_eq_append_left]

@[trans]
lemma IsPrefix.trans (hxy : x ◨ y) (hyz : y ◨ z) : x ◨ z := by
  rcases hyz with rfl | ⟨v, rfl⟩
  · exact hxy
  · exact hxy.append_right

@[trans]
lemma IsSuffix.trans (hxy : y ◧ x) (hyz : z ◧ y) : z ◧ x := by
  rcases hyz with rfl | ⟨u, rfl⟩
  · exact hxy
  · exact hxy.append_left

lemma IsPrefix.total (hx : x ◨ z) (hy : y ◨ z) : x ◨ y ∨ y ◨ x := by
  grind [IsPrefix, editor]

lemma IsSuffix.total (hx : z ◧ x) (hy : z ◧ y) : y ◧ x ∨ x ◧ y := by
  grind [IsSuffix, editor]

lemma eq_and_eq_of_append_eq_append_isAtom (hc : IsAtom c) (hd : IsAtom d) (h : x ++ y = c ++ d) :
    x = c ∧ y = d := by
  rcases editor h with h | ⟨u, ⟨h, -⟩ | ⟨-, h⟩⟩ <;> grind

lemma eq_zero_or_eq_zero_zero_of_isSubstring (h : IsSubstring t (0 ++ 0 : V)) :
    t = 0 ∨ t = 0 ++ 0 := by
  rcases h.append_cases with h | h | ⟨t₁, t₂, rfl, h₁, h₂⟩
  · exact Or.inl <| isAtom_zero.eq_of_isSubstring h
  · exact Or.inl <| isAtom_zero.eq_of_isSubstring h
  · rw [isAtom_zero.eq_of_isSubstring h₁.isSubstring, isAtom_zero.eq_of_isSubstring h₂.isSubstring]
    exact Or.inr rfl

lemma eq_of_isSuffix_isAtom_zero_zero (hc : IsAtom c) (h : c ++ 0 ++ 0 ◧ t) :
    t = 0 ∨ t = 0 ++ 0 ∨ t = c ++ 0 ++ 0 := by
  rcases h with rfl | ⟨k, h⟩
  · simp
  · rcases editor h with ⟨-, rfl⟩ | ⟨u, ⟨-, h₁⟩ | ⟨h₁, rfl⟩⟩
    · simp
    · exact absurd h₁ isAtom_zero.ne_append
    · rcases editor h₁ with ⟨-, rfl⟩ | ⟨u', ⟨-, h'⟩ | ⟨h', -⟩⟩
      · simp
      · exact absurd h' isAtom_zero.ne_append
      · exact absurd h' hc.ne_append

lemma isTally_zero_zero : IsTally (0 : V) (0 ++ 0) :=
  (isTally_self isAtom_zero).append (isTally_self isAtom_zero)

lemma zero_zero_append_ne_zero_zero : (0 ++ 0 ++ x : V) ≠ 0 ++ 0 := by
  intro h
  rcases editor h with ⟨h, -⟩ | ⟨u, ⟨h, -⟩ | ⟨-, h⟩⟩ <;> simp at h

lemma IsSuffix.append_congr (h : y ◧ x) : y ++ z ◧ x ++ z := by
  grind [IsSuffix, Concatenation.append_assoc]

lemma IsPrefix.of_append_left_isAtom (hc : IsAtom c) (h : c ++ x ◨ c ++ y) : x ◨ y := by
  grind [IsPrefix, IsAtom.append_left_cancel, Concatenation.append_assoc]

end substring

lemma TC.infinite_of_models (V : Type*) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* 𝗧𝗖] : Infinite V :=
  .of_injective_of_forall_ne (f := (· ++ (0 : V))) (fun _ _ ↦ isAtom_zero.append_right_cancel)
    fun x h ↦ zero_ne_append x 0 h.symm

section thin

variable {V : Type*} [ConcatenationStructure V] {x y : V}

/--
`x` is thin: every substring of `x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def IsThin (x : V) : Prop := ∀ y, IsSubstring y x → IsBounded y

/--
`x` is thin: every substring of `x` is an atom, or begins with an atom and ends with an atom.
- [Gan09, §3]
-/
def isThin : Semisentence ℒ⌢ 1 := “x. ∀ y, !isSubstring y x → !isBounded y”

instance isThin_defined : ℒ⌢-predicate[V] IsThin via isThin := ⟨fun v ↦ by simp [isThin, IsThin]⟩

instance isThin_definable : ℒ⌢-predicate[V] IsThin := isThin_defined.to_definable

lemma TCPlus.isBounded [V↓[ℒ⌢] ⊧* 𝗧𝗖⁺] (x : V) : IsBounded x := by
  have := by
    simpa [models_iff, allIsBounded] using Theory.models V _ (Set.mem_insert allIsBounded 𝗧𝗖)
  exact this x

instance [V↓[ℒ⌢] ⊧* 𝗧𝗖⁺] : V↓[ℒ⌢] ⊧* 𝗧𝗖 :=
  models_of_subtheory (U := 𝗧𝗖⁺) inferInstance

lemma IsAtom.isBounded (h : IsAtom x) : IsBounded x := Or.inl h

lemma IsThin.isBounded (h : IsThin x) : IsBounded x := h x (IsSubstring.refl x)

section TC

variable [V↓[ℒ⌢] ⊧* 𝗧𝗖]

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

lemma isThin_zero : IsThin (0 : V) := isAtom_zero.isThin

lemma isThin_one : IsThin (1 : V) := isAtom_one.isThin

/--
The concatenation of thin strings is thin.
- [Gan09, §3, Lemma 6]
-/
lemma IsThin.append (hx : IsThin x) (hy : IsThin y) : IsThin (x ++ y) := by
  intro z hz
  rcases hz.append_cases with h | h | ⟨z₁, z₂, rfl, h₁, h₂⟩
  exacts [hx z h, hy z h, (hx z₁ h₁.isSubstring).append (hy z₂ h₂.isSubstring)]

end TC

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖⁺ := by
  have h (x : FreeSemigroup Bool) : IsBounded x := by
    induction x using FreeSemigroup.recOnMul with
    | ih1 b => exact (isAtom_of b).isBounded
    | ih2 b x hb hx => exact hb.append hx
  have hT : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗧𝗖 := inferInstance
  simpa [models_iff, allIsBounded] using ⟨h, fun φ hφ ↦ models_theory_iff.mp hT φ hφ⟩

/--
The translation of $\mathsf{TC}$ into itself relativized to the thin strings.
- [Gan09, §3, Lemma 6]
-/
def thinTranslation : DirectTranslation 𝗧𝗖 ℒ⌢ where
  domain := ⟨isThin⟩
  rel R := ⟨Semiformula.rel R (#·)⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := complete.{0} _ _ fun V _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    use 0
    simpa [Semiformula.Operator.val] using isThin_zero
  func_defined f := complete.{0} _ _ fun V _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e he
    have he (i) : IsThin (e i) := by simpa [Semiformula.Operator.val] using he i
    cases f
    · suffices ∃! y : V, IsThin y ∧ y = 0 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 0
      simp [isThin_zero]
    · suffices ∃! y : V, IsThin y ∧ y = 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use 1
      simp [isThin_one]
    · suffices ∃! y : V, IsThin y ∧ y = e 0 ++ e 1 by
        simpa [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
      use e 0 ++ e 1
      simp [(he 0).append (he 1)]
  preserve_eq := complete.{0} _ _ fun V _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val]

@[simp]
lemma thinTranslation.dom_iff : thinTranslation.Dom x ↔ IsThin x := by
  simp [DirectTranslation.dom_iff, thinTranslation, Semiformula.Operator.val]

section model

variable [V↓[ℒ⌢] ⊧* 𝗧𝗖]

/-- The letters and the concatenation of `V` restricted to the thin strings. -/
abbrev thinTranslation.concatenationStructure :
    ConcatenationStructure (thinTranslation.Model V) where
  zero := ⟨0, by simpa using isThin_zero⟩
  one := ⟨1, by simpa using isThin_one⟩
  append x y := ⟨x ++ y, by
    simpa using (thinTranslation.dom_iff.mp x.dom).append (thinTranslation.dom_iff.mp y.dom)⟩

/--
The structure of the model of `thinTranslation` is the standard one of the letters and the
concatenation restricted to the thin strings.
-/
lemma thinTranslation.struc_eq :
    Model.struc thinTranslation V = @standardModel _ thinTranslation.concatenationStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [thinTranslation, Semiformula.Operator.val] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext <| Model.eq_iff v)

namespace thinTranslation

section

attribute [local instance] concatenationStructure

variable {x y : V} {hx : thinTranslation.Dom x} {hy : thinTranslation.Dom y}

@[simp]
lemma zero_eq_mk : (0 : thinTranslation.Model V) = ⟨0, by simpa using isThin_zero⟩ := rfl

@[simp]
lemma one_eq_mk : (1 : thinTranslation.Model V) = ⟨1, by simpa using isThin_one⟩ := rfl

@[simp]
lemma mk_append_mk : (⟨x, hx⟩ ++ ⟨y, hy⟩ : thinTranslation.Model V) = ⟨x ++ y, by
    simpa using (thinTranslation.dom_iff.mp hx).append (thinTranslation.dom_iff.mp hy)⟩ := rfl

@[simp]
lemma isAtom_mk : IsAtom (⟨x, hx⟩ : thinTranslation.Model V) ↔ IsAtom x := by simp [IsAtom]

end

end thinTranslation

/--
The thin strings of a model of $\mathsf{TC}$ form a model of $\mathsf{TC}^+$.
- [Gan09, §3, Lemma 6]
-/
instance : (thinTranslation.Model V)↓[ℒ⌢] ⊧* 𝗧𝗖⁺ := by
  rw [thinTranslation.struc_eq]
  let := thinTranslation.concatenationStructure (V := V)
  constructor
  intro σ hσ
  rcases hσ with rfl | hσ
  · simpa [models_iff, allIsBounded, Model.forall_iff, Model.exists_iff, IsBounded] using
      fun (x : V) (hx : IsThin x) ↦ hx.isBounded.imp id fun ⟨⟨c, z, hc, h⟩, ⟨c', z', hc', h'⟩⟩ ↦
        ⟨⟨c, hc, hc.isThin, z, hx.of_isSubstring <| by simp [h], h⟩,
          ⟨c', hc', hc'.isThin, z', hx.of_isSubstring <| by simp [h'], h'⟩⟩
  · cases hσ
    case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
    case editor =>
      simpa [models_iff, Model.forall_iff, Model.exists_iff] using
        fun (x : V) (hx : IsThin x) (y : V) (_ : IsThin y) (z : V) (hz : IsThin z) (w : V)
          (_ : IsThin w) (h : x ++ y = z ++ w) ↦ (editor h).imp id fun ⟨u, hu⟩ ↦
            ⟨u, hu.elim (fun h ↦ hz.of_isSubstring <| by simp [← h.1])
              fun h ↦ hx.of_isSubstring <| by simp [h.1], hu⟩
    all_goals simp [models_iff, Model.forall_iff, Concatenation.append_assoc]

end model

/--
$\mathsf{TC}$ interprets $\mathsf{TC}^+$ on the thin strings.
- [Gan09, §3, Lemma 6]
-/
instance : 𝗧𝗖 ⊳ 𝗧𝗖⁺ where
  trln := thinTranslation
  interpret_theory _ hφ := complete.{0} _ _ fun _ _ _ ↦ DirectTranslation.models_translate_of_mem hφ

end thin

end FFL.FirstOrder.Concatenation

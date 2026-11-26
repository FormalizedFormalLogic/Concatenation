module

public import Concatenation.Biteral
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-!
# Semantics of the languages of concatenation

Structures with letters and a concatenation, possibly with the empty string, read as structures for
the languages of concatenation, with the substrings, prefixes, suffixes and tallies in them.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- The value of a nonempty string whose letters have the values `f`, associated to the left. -/
def Concatenation.stringValue {α M : Type*} [Append M] (f : α → M) (x : FreeSemigroup α) : M :=
  x.tail.foldl (fun m a ↦ m ++ f a) (f x.head)

/-- A type with two letters `0`, `1` and a concatenation `++`. -/
class ConcatenationStructure (α : Type*) extends Zero α, One α, Append α

instance {α : Type*} [Zero α] [One α] [Append α] : ConcatenationStructure α where

namespace ConcatenationStructure

variable {α : Type*} [ConcatenationStructure α]

/-- The value of a nonempty binary string, associated to the left. -/
def ofFreeSemigroup (x : FreeSemigroup Bool) : α :=
  Concatenation.stringValue (fun b ↦ if b then 1 else 0) x

end ConcatenationStructure

/-- The letters and the concatenation transported along a bijection. -/
abbrev ConcatenationStructure.ofEquiv {α β : Type*} [ConcatenationStructure β] (e : α ≃ β) :
    ConcatenationStructure α where
  zero := e.symm 0
  one := e.symm 1
  append x y := e.symm (e x ++ e y)

/-- A type with two letters `0`, `1`, a concatenation `++`, and the empty string `∅`. -/
class ConcatenationEmptyStructure (α : Type*) extends ConcatenationStructure α, EmptyCollection α

/-- The letters, the concatenation and the empty string transported along a bijection. -/
abbrev ConcatenationEmptyStructure.ofEquiv {α β : Type*} [ConcatenationEmptyStructure β]
    (e : α ≃ β) : ConcatenationEmptyStructure α where
  toConcatenationStructure := .ofEquiv e
  emptyCollection := e.symm ∅

namespace ConcatenationEmptyStructure

variable {α : Type*} [ConcatenationEmptyStructure α]

/-- The value of a possibly empty binary string, associated to the left. -/
def ofList : List Bool → α
  | [] => ∅
  | b :: l => ConcatenationStructure.ofFreeSemigroup ⟨b, l⟩

end ConcatenationEmptyStructure

/-- A type with a letter for every element of `α` and a concatenation `++`. -/
class LetterStructure (α : Type) (M : Type*) extends Append M where
  ofLetter : α → M

/-- The structure with two letters that the letters `a` and `b` give. -/
abbrev LetterStructure.concatenationStructure {α : Type} {M : Type*} [LetterStructure α M]
    (a b : α) : ConcatenationStructure M where
  zero := ofLetter a
  one := ofLetter b

namespace Concatenation

open Language

section semantics

variable (M : Type*) [ConcatenationStructure M]

instance standardModel : Tarski.Structure ℒ⌢ M where
  func := fun _ f ↦
    match f with
    | Concatenation.Func.zero => fun _ ↦ 0
    | Concatenation.Func.one => fun _ ↦ 1
    | Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ M := ⟨fun _ _ ↦ rfl⟩

lemma standardModel_unique (s : Tarski.Structure ℒ⌢ M) [Tarski.Structure.Zero ℒ⌢ M]
    [Tarski.Structure.One ℒ⌢ M] [Tarski.Structure.Concat ℒ⌢ M] [Tarski.Structure.Eq ℒ⌢ M] :
    s = standardModel M :=
  Tarski.Structure.ext
    (funext₃ fun k f _ ↦
      match k, f with
      | _, Language.Zero.zero => by simp [Matrix.empty_eq]
      | _, Language.One.one => by simp [Matrix.empty_eq]
      | _, Language.Concat.concat => by simp)
    (funext₃ fun k r _ ↦
      match k, r with
      | _, Language.Eq.eq => by simp)

variable {M} in
lemma standardModel_ofEquiv {α : Type*} (e : α ≃ M) :
    @standardModel α (.ofEquiv e) = Tarski.Structure.ofEquiv e.symm :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by cases f <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext e.apply_eq_iff_eq.symm)

end semantics

/-- Every structure with equality is the one of two letters and a concatenation. -/
lemma exists_eq_standardModel (M : Type*) [Nonempty M] (s : Tarski.Structure ℒ⌢ M)
    [Tarski.Structure.Eq ℒ⌢ M] : ∃ c : ConcatenationStructure M, s = @standardModel M c := by
  let c : ConcatenationStructure M :=
    { zero := s.func Language.Zero.zero ![]
      one := s.func Language.One.one ![]
      append a b := s.func Language.Concat.concat ![a, b] }
  have : Tarski.Structure.Zero ℒ⌢ M := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.One ℒ⌢ M := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.Concat ℒ⌢ M := ⟨fun a b ↦ rfl⟩
  exact ⟨c, standardModel_unique M s⟩

lemma complete (T : ConcatenationTheory) [𝗘𝗤 ℒ⌢ ⪯ T] (φ : ConcatenationSentence)
    (H : ∀ (M : Type*) [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* T], M↓[ℒ⌢] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    obtain ⟨c, rfl⟩ := exists_eq_standardModel M s
    exact H M

lemma provable_iff_of_models_iff {T : ConcatenationTheory} [𝗘𝗤 ℒ⌢ ⪯ T] {n}
    {φ ψ : ConcatenationSemisentence n}
    (h : ∀ (V : Type*) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] (e : Fin n → V),
      V ⊧/e φ ↔ V ⊧/e ψ) :
    T ⊢ ∀¹* (φ 🡘 ψ) := by
  apply complete T _
  intro V _ _
  simpa [models_iff] using h V

lemma models_iff_of_provable_iff {T : ConcatenationTheory} [𝗘𝗤 ℒ⌢ ⪯ T] {n}
    {φ ψ : ConcatenationSemisentence n} (h : T ⊢ ∀¹* (φ 🡘 ψ)) (V : Type*)
    [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T] (e : Fin n → V) :
    V ⊧/e φ ↔ V ⊧/e ψ := by
  have h' := consequence_iff.mp (Theory.Proof.sound h) V inferInstance
  simp only [models_iff, Semiformula.eval_allClosure] at h'
  simpa using h' e

lemma weakerThan_of_models (T S : ConcatenationTheory) [𝗘𝗤 ℒ⌢ ⪯ S]
    (H : ∀ (M : Type*) [ConcatenationStructure M] [M↓[ℒ⌢] ⊧* S], M↓[ℒ⌢] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ complete _ _ fun M _ _ ↦ Theory.Proof.sound h (H M)

@[simp]
lemma val_stringTerm {L : Language} [L.Concat] {α ξ M : Type*} {n : ℕ} [Tarski.Structure L M]
    [Append M] [Tarski.Structure.Concat L M] {e : Fin n → M} {ε : ξ → M}
    (f : α → Semiterm L ξ n) (x : FreeSemigroup α) :
    (stringTerm f x).val e ε = stringValue (fun a ↦ (f a).val e ε) x := by
  suffices ∀ (l : List α) (t : Semiterm L ξ n), (l.foldl (fun t a ↦ ‘!!t ⌢ !!(f a)’) t).val e ε =
      l.foldl (fun m a ↦ m ++ (f a).val e ε) (t.val e ε) from this x.tail (f x.head)
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma map_stringValue {α M N : Type*} [Append M] [Append N] (g : M → N)
    (hg : ∀ x y, g (x ++ y) = g x ++ g y) (f : α → M) (x : FreeSemigroup α) :
    g (stringValue f x) = stringValue (g ∘ f) x :=
  (List.foldl_hom g fun m a ↦ (hg m (f a)).symm).symm

section eval

variable {M : Type*} [ConcatenationStructure M] {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M}

@[simp]
lemma val_letter (b : Bool) : (letter b : Semiterm ℒ⌢ ξ n).val e ε = if b then 1 else 0 := by
  cases b <;> simp [letter]

@[simp]
lemma val_biteral (x : FreeSemigroup Bool) :
    (biteral x : Semiterm ℒ⌢ ξ n).val e ε = ConcatenationStructure.ofFreeSemigroup x := by
  simp [biteral, ConcatenationStructure.ofFreeSemigroup]

@[simp]
lemma eval_isOneOf {l : List (FreeSemigroup Bool)} {x : M} :
    M ⊧/![x] (isOneOf l : ConcatenationSemisentence 1) ↔
      ∃ γ ∈ l, x = ConcatenationStructure.ofFreeSemigroup γ := by
  simp [isOneOf]

end eval

section isSubstring

variable {M : Type*} [Append M] {x y : M}

/--
`x` is a substring of `y`. Both associations of `u ++ x ++ v` are listed, so that the relation is
the one `isSubstring` defines in any structure with a concatenation.
- [Gan09, §1, Definition 1]
-/
def IsSubstring (x y : M) : Prop :=
  x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨ (∃ u v, y = (u ++ x) ++ v) ∨
    ∃ u v, y = u ++ (x ++ v)

lemma IsSubstring.map {N : Type*} [Append N] (g : M → N) (hg : ∀ x y, g (x ++ y) = g x ++ g y)
    (h : IsSubstring x y) : IsSubstring (g x) (g y) := by
  grind [IsSubstring]

/-- A property that passes from a concatenation to its parts passes to substrings. -/
lemma IsSubstring.of_forall_append {P : M → Prop} (hP : ∀ x y, P (x ++ y) → P x ∧ P y)
    (h : IsSubstring x y) (hy : P y) : P x := by
  grind [IsSubstring]

@[simp]
lemma eval_isSubstring {L : Language} [L.Concat] [L.Eq] [Tarski.Structure L M]
    [Tarski.Structure.Concat L M] [Tarski.Structure.Eq L M] :
    M ⊧/![x, y] (isSubstring : Semisentence L 2) ↔ IsSubstring x y := by
  have : Nonempty M := ⟨x⟩
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := y)]

end isSubstring

section substring

variable {M : Type*} [ConcatenationStructure M] {c x y : M}

@[simp]
lemma val_substringOperator {v : Fin 2 → M} :
    (substringOperator ℒ⌢).val v ↔ IsSubstring (v 0) (v 1) := by
  rw [Matrix.fun_eq_vec_two (v := v)]
  exact eval_isSubstring

/-- `x` is one of the letters `0` and `1`. -/
def IsAtom (x : M) : Prop := x = 0 ∨ x = 1

/-- `x` is one of the letters `0` and `1`. -/
def isAtom : Semisentence ℒ⌢ 1 := “x. x = !!(op(0).const) ∨ x = !!(op(1).const)”

@[simp]
lemma eval_isAtom : M ⊧/![x] isAtom ↔ IsAtom x := by simp [isAtom, IsAtom]

/--
`x` is a prefix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsPrefix (x y : M) : Prop := x = y ∨ ∃ v, y = x ++ v

/-- `x ◨ y`: `x` is a prefix of `y`. -/
scoped infix:50 " ◨ " => IsPrefix

/-- `x` is a prefix of `y`. -/
def isPrefix : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ v, y = x ⌢ v”

@[simp]
lemma eval_isPrefix : M ⊧/![x, y] isPrefix ↔ x ◨ y := by
  simp [isPrefix, IsPrefix]

/--
`x` is a suffix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsSuffix (x y : M) : Prop := x = y ∨ ∃ u, y = u ++ x

/-- `x ◧ y`: `y` is a suffix of `x`. -/
scoped notation:50 x:51 " ◧ " y:51 => IsSuffix y x

/-- `x` is a suffix of `y`. -/
def isSuffix : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

@[simp]
lemma eval_isSuffix : M ⊧/![x, y] isSuffix ↔ y ◧ x := by
  simp [isSuffix, IsSuffix]

/--
`x` is a `c`-tally: every atom that is a substring of `x` is `c`.
- [Gan09, §1, Definition 1]
-/
def IsTally (c x : M) : Prop := ∀ y, IsAtom y → IsSubstring y x → y = c

/-- `x` is a `c`-tally. -/
def isTally : Semisentence ℒ⌢ 2 := “c x. ∀ y, !isAtom y → !isSubstring y x → y = c”

@[simp]
lemma eval_isTally : M ⊧/![c, x] isTally ↔ IsTally c x := by
  simp [isTally, IsTally]

@[simp]
lemma isAtom_zero : IsAtom (0 : M) := Or.inl rfl

@[simp]
lemma isAtom_one : IsAtom (1 : M) := Or.inr rfl

@[refl, simp]
lemma IsSubstring.refl (x : M) : IsSubstring x x := Or.inl rfl

@[simp]
lemma isSubstring_append_left (x y : M) : IsSubstring x (x ++ y) := by
  right; right; left; use y

@[simp]
lemma isSubstring_append_right (x y : M) : IsSubstring y (x ++ y) := by
  right; left; use x

@[simp]
lemma isSubstring_append_append (u x v : M) : IsSubstring x (u ++ x ++ v) := by
  right; right; right; left; use u, v

@[refl, simp]
lemma IsPrefix.refl (x : M) : x ◨ x := Or.inl rfl

@[simp]
lemma isPrefix_append (x y : M) : x ◨ x ++ y := by
  right; use y

@[refl, simp]
lemma IsSuffix.refl (x : M) : x ◧ x := Or.inl rfl

@[simp]
lemma isSuffix_append (x y : M) : x ++ y ◧ y := by
  right; use x

lemma IsPrefix.isSubstring (h : x ◨ y) : IsSubstring x y := by
  rcases h with rfl | ⟨v, rfl⟩ <;> simp

lemma IsSuffix.isSubstring (h : y ◧ x) : IsSubstring x y := by
  rcases h with rfl | ⟨u, rfl⟩ <;> simp

end substring

/-- The concatenation of nonempty strings. -/
instance {α : Type*} : Append (FreeSemigroup α) := ⟨(· * ·)⟩

@[simp]
lemma append_eq_mul {α : Type*} (x y : FreeSemigroup α) : x ++ y = x * y := rfl

lemma stringValue_of {α : Type*} (x : FreeSemigroup α) : stringValue FreeSemigroup.of x = x := by
  suffices ∀ (l : List α) (y : FreeSemigroup α),
      l.foldl (fun m a ↦ m ++ FreeSemigroup.of a) y = ⟨y.head, y.tail ++ l⟩ from this x.tail _
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro y
    rw [List.foldl_cons, ih]
    simp [FreeSemigroup.of, HMul.hMul, Mul.mul]

/-- The only map from the strings that respects concatenation and sends the letters to `f`. -/
lemma stringValue_eq_of_map_append {α M : Type*} [Append M] {f : α → M} {c : FreeSemigroup α → M}
    (hf : ∀ a, c (FreeSemigroup.of a) = f a) (hc : ∀ x y, c (x ++ y) = c x ++ c y)
    (x : FreeSemigroup α) : stringValue f x = c x := by
  rw [← funext hf, ← stringValue_of x, ← Function.comp_def, ← map_stringValue c hc, stringValue_of,
    stringValue_of]

/--
The nonempty binary strings under concatenation.
- [GZ08, §1]
- [Vis09, §2]
-/
instance : ConcatenationStructure (FreeSemigroup Bool) where
  zero := FreeSemigroup.of false
  one := FreeSemigroup.of true

lemma zero_eq_of_false : (0 : FreeSemigroup Bool) = FreeSemigroup.of false := rfl

lemma one_eq_of_true : (1 : FreeSemigroup Bool) = FreeSemigroup.of true := rfl

@[simp]
lemma isAtom_of (b : Bool) : IsAtom (FreeSemigroup.of b) := by
  cases b <;> simp [IsAtom, zero_eq_of_false, one_eq_of_true]

section ofFreeSemigroup

open ConcatenationStructure

variable {M : Type*} [ConcatenationStructure M] {c : FreeSemigroup Bool}

@[simp]
lemma ofFreeSemigroup_zero : (ofFreeSemigroup (0 : FreeSemigroup Bool) : M) = 0 := rfl

@[simp]
lemma ofFreeSemigroup_one : (ofFreeSemigroup (1 : FreeSemigroup Bool) : M) = 1 := rfl

lemma ofFreeSemigroup_append_of_isAtom (u : FreeSemigroup Bool) (hc : IsAtom c) :
    (ofFreeSemigroup (u ++ c) : M) = ofFreeSemigroup u ++ ofFreeSemigroup c := by
  rcases hc with rfl | rfl <;>
    simp [ofFreeSemigroup, stringValue, HMul.hMul, Mul.mul, zero_eq_of_false, one_eq_of_true,
      FreeSemigroup.of]

/-- Induction on a nonempty binary string by its last letter. -/
@[elab_as_elim]
lemma atom_append_induction {motive : FreeSemigroup Bool → Prop} (u : FreeSemigroup Bool)
    (atom : ∀ c, IsAtom c → motive c)
    (append : ∀ u c, IsAtom c → motive u → motive (u ++ c)) : motive u := by
  rcases u with ⟨b, l⟩
  induction l using List.reverseRecOn with
  | nil => exact atom _ <| isAtom_of b
  | append_singleton l d ih => exact append _ _ (isAtom_of d) ih

end ofFreeSemigroup

section semantics

variable (M : Type*) [ConcatenationEmptyStructure M]

instance standardModelEmpty : Tarski.Structure ℒ⌢ₑ M where
  func := fun _ f ↦
    match f with
    | Sum.inl Concatenation.Func.zero => fun _ ↦ 0
    | Sum.inl Concatenation.Func.one => fun _ ↦ 1
    | Sum.inl Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
    | Sum.inr (Constant.Func.const _) => fun _ ↦ ∅
  rel := fun _ r ↦
    match r with
    | Sum.inl Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ₑ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ₑ M := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ₑ M := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ₑ M := ⟨fun _ _ ↦ rfl⟩

variable {M}

@[simp]
lemma val_star : (Semiterm.Operator.Star.star : Semiterm.Operator ℒ⌢ₑ 0).val ![] = (∅ : M) := rfl

lemma standardModelEmpty_ofEquiv {α : Type*} (e : α ≃ M) :
    @standardModelEmpty α (.ofEquiv e) = Tarski.Structure.ofEquiv e.symm :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;> rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext e.apply_eq_iff_eq.symm)

end semantics

section eval

open ConcatenationStructure ConcatenationEmptyStructure

variable {M : Type*} [ConcatenationEmptyStructure M] {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M}
  {x y : M}

lemma val_biteral_empty (u : FreeSemigroup Bool) :
    (biteral u : Semiterm ℒ⌢ₑ ξ n).val e ε = ofFreeSemigroup u := by
  have hb (b : Bool) : (letter b : Semiterm ℒ⌢ₑ ξ n).val e ε = if b then 1 else 0 := by
    cases b <;> simp [letter]
  simp [biteral, ofFreeSemigroup, hb]

@[simp]
lemma val_biteralEmpty (l : List Bool) :
    (biteralEmpty l : Semiterm ℒ⌢ₑ ξ n).val e ε = ofList l := by
  cases l
  · simp [biteralEmpty, ofList]
  · simp [biteralEmpty, ofList, val_biteral_empty]

@[simp]
lemma eval_isSubstring_empty :
    M ⊧/![x, y] (isSubstring : Semisentence ℒ⌢ₑ 2) ↔ IsSubstring x y := by
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := y)]

end eval

section ofList

open ConcatenationStructure ConcatenationEmptyStructure

/--
The binary strings under concatenation.
- [HH14, §2]
-/
instance : ConcatenationEmptyStructure (List Bool) where
  zero := [false]
  one := [true]

variable {M : Type*} [ConcatenationEmptyStructure M] {u : List Bool}

@[simp]
lemma ofList_nil : (ofList [] : M) = ∅ := rfl

@[simp]
lemma ofList_false : (ofList [false] : M) = 0 := rfl

@[simp]
lemma ofList_true : (ofList [true] : M) = 1 := rfl

lemma ofList_append_singleton (hu : u ≠ []) (b : Bool) :
    (ofList (u ++ [b]) : M) = ofList u ++ ofList [b] := by
  cases u <;> simp_all [ofList, ofFreeSemigroup, stringValue]

@[simp]
lemma isAtom_ofList_singleton (b : Bool) : IsAtom (ofList [b] : M) := by
  cases b <;> simp

end ofList

lemma completeEmpty (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (φ : Sentence ℒ⌢ₑ)
    (H : ∀ (M : Type*) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* T], M↓[ℒ⌢ₑ] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    let c : ConcatenationEmptyStructure M :=
      { zero := s.func (Sum.inl Concatenation.Func.zero) ![]
        one := s.func (Sum.inl Concatenation.Func.one) ![]
        append a b := s.func (Sum.inl Concatenation.Func.concat) ![a, b]
        emptyCollection := s.func (Sum.inr <| Constant.Func.const ⟨⟩) ![] }
    have e : s = standardModelEmpty M :=
      Tarski.Structure.ext
        (funext₃ fun k f v ↦
          match k, f with
          | _, Sum.inl Concatenation.Func.zero => congrArg _ <| Matrix.empty_eq v
          | _, Sum.inl Concatenation.Func.one => congrArg _ <| Matrix.empty_eq v
          | _, Sum.inl Concatenation.Func.concat => congrArg _ <| Matrix.fun_eq_vec_two v
          | _, Sum.inr (Constant.Func.const _) => congrArg _ <| Matrix.empty_eq v)
        (funext₃ fun k r v ↦
          match k, r with
          | _, Sum.inl Concatenation.Rel.eq =>
            (Tarski.Structure.eq_lang (L := ℒ⌢ₑ) (M := M) (v := v)).eq)
    rw [e] at hT ⊢
    exact H M

lemma weakerThan_of_models_empty (T S : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ S]
    (H : ∀ (M : Type*) [ConcatenationEmptyStructure M] [M↓[ℒ⌢ₑ] ⊧* S], M↓[ℒ⌢ₑ] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ completeEmpty _ _ fun M _ _ ↦ Theory.Proof.sound h (H M)

section letters

open LetterStructure

variable {α : Type}

/-- The constant denoting the letter `a`. -/
def letterTerm {ξ : Type*} {n : ℕ} (a : α) : Semiterm ℒ⌢[α] ξ n := .func (.letter a) ![]

section semantics

variable (M : Type*) [LetterStructure α M]

instance lettersModel : Tarski.Structure ℒ⌢[α] M where
  func := fun _ f ↦
    match f with
    | .letter a => fun _ ↦ ofLetter a
    | .concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | .eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢[α] M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Concat ℒ⌢[α] M := ⟨fun _ _ ↦ rfl⟩

variable {M}

@[simp]
lemma val_letterTerm {ξ : Type*} {n : ℕ} {e : Fin n → M} {ε : ξ → M} (a : α) :
    (letterTerm a : Semiterm ℒ⌢[α] ξ n).val e ε = ofLetter a := rfl

end semantics

lemma completeLetters (T : Theory ℒ⌢[α]) [𝗘𝗤 ℒ⌢[α] ⪯ T] (φ : Sentence ℒ⌢[α])
    (H : ∀ (M : Type*) [Nonempty M] [LetterStructure α M] [M↓[ℒ⌢[α]] ⊧* T], M↓[ℒ⌢[α]] ⊧ φ) :
    T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun M _ s _ hT ↦ by
    let c : LetterStructure α M :=
      { ofLetter a := s.func (.letter a) ![]
        append x y := s.func .concat ![x, y] }
    have e : s = lettersModel M :=
      Tarski.Structure.ext
        (funext₃ fun k f v ↦
          match k, f with
          | _, .letter a => congrArg _ <| Matrix.empty_eq v
          | _, .concat => congrArg _ <| Matrix.fun_eq_vec_two v)
        (funext₃ fun k r v ↦
          match k, r with
          | _, .eq => (Tarski.Structure.eq_lang (L := ℒ⌢[α]) (M := M) (v := v)).eq)
    rw [e] at hT ⊢
    exact H M

/-- The nonempty strings of the letters `α` under concatenation. -/
instance : LetterStructure α (FreeSemigroup α) where
  ofLetter := FreeSemigroup.of

end letters

end Concatenation

end FFL.FirstOrder

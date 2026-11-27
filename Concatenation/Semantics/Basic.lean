module

public import Concatenation.Biteral
public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.FirstOrder.Tarski.Definability

/-!
# Semantics of the languages of concatenation

Structures with letters and a concatenation, possibly with the empty string, read as structures for
the languages of concatenation, with the substrings, prefixes, suffixes and tallies in them.
-/

@[expose] public section

namespace FFL.FirstOrder

/-- A type with two letters `0`, `1` and a concatenation `++`. -/
class ConcatenationStructure (α : Type*) extends Zero α, One α, Append α

instance {α : Type*} [Zero α] [One α] [Append α] : ConcatenationStructure α where

namespace ConcatenationStructure

variable {α : Type*} [ConcatenationStructure α]

/-- The value of a nonempty binary string, associated to the left. -/
def ofFreeSemigroup (x : FreeSemigroup Bool) : α :=
  FreeSemigroup.stringValue (fun b ↦ if b then 1 else 0) x

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
class LetterStructure (α : Type) (V : Type*) extends Append V where
  ofLetter : α → V

/-- The structure with two letters that the letters `a` and `b` give. -/
abbrev LetterStructure.concatenationStructure {α : Type} {V : Type*} [LetterStructure α V]
    (a b : α) : ConcatenationStructure V where
  zero := ofLetter a
  one := ofLetter b

lemma LetterStructure.ofFreeSemigroup_concatenationStructure {α : Type} {V : Type*}
    [LetterStructure α V] {a b : α} (u : FreeSemigroup Bool) :
    let := concatenationStructure (V := V) a b
    (ConcatenationStructure.ofFreeSemigroup u : V) =
      FreeSemigroup.stringValue ofLetter
        ⟨if u.head then b else a, u.tail.map fun i ↦ if i then b else a⟩ := by
  simp only [ConcatenationStructure.ofFreeSemigroup, FreeSemigroup.stringValue, List.foldl_map,
    apply_ite ofLetter]
  rfl

namespace Concatenation

open Language

section semantics

variable (V : Type*) [ConcatenationStructure V]

instance standardModel : Tarski.Structure ℒ⌢ V where
  func := fun _ f ↦
    match f with
    | Concatenation.Func.zero => fun _ ↦ 0
    | Concatenation.Func.one => fun _ ↦ 1
    | Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ V := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ V := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ V := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ V := ⟨fun _ _ ↦ rfl⟩

lemma standardModel_unique (s : Tarski.Structure ℒ⌢ V) [Tarski.Structure.Zero ℒ⌢ V]
    [Tarski.Structure.One ℒ⌢ V] [Tarski.Structure.Concat ℒ⌢ V] [Tarski.Structure.Eq ℒ⌢ V] :
    s = standardModel V :=
  Tarski.Structure.ext
    (funext₃ fun k f _ ↦
      match k, f with
      | _, Language.Zero.zero => by simp [Matrix.empty_eq]
      | _, Language.One.one => by simp [Matrix.empty_eq]
      | _, Language.Concat.concat => by simp)
    (funext₃ fun k r _ ↦
      match k, r with
      | _, Language.Eq.eq => by simp)

variable {V} in
lemma standardModel_ofEquiv {α : Type*} (e : α ≃ V) :
    @standardModel α (.ofEquiv e) = Tarski.Structure.ofEquiv e.symm :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by cases f <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      exact propext e.apply_eq_iff_eq.symm)

end semantics

/-- Every structure with equality is the one of two letters and a concatenation. -/
lemma exists_eq_standardModel (V : Type*) (s : Tarski.Structure ℒ⌢ V)
    [Tarski.Structure.Eq ℒ⌢ V] : ∃ c : ConcatenationStructure V, s = @standardModel V c := by
  let c : ConcatenationStructure V :=
    { zero := s.func Language.Zero.zero ![]
      one := s.func Language.One.one ![]
      append a b := s.func Language.Concat.concat ![a, b] }
  have : Tarski.Structure.Zero ℒ⌢ V := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.One ℒ⌢ V := ⟨by
    simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq, Matrix.empty_eq]; rfl⟩
  have : Tarski.Structure.Concat ℒ⌢ V := ⟨fun a b ↦ rfl⟩
  exact ⟨c, standardModel_unique V s⟩

lemma complete (T : ConcatenationTheory) [𝗘𝗤 ℒ⌢ ⪯ T] (φ : ConcatenationSentence)
    (H : ∀ (V : Type*) [ConcatenationStructure V] [V↓[ℒ⌢] ⊧* T], V↓[ℒ⌢] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun V _ s _ hT ↦ by
    obtain ⟨c, rfl⟩ := exists_eq_standardModel V s
    exact H V

@[simp]
lemma val_stringTerm {L : Language} [L.Concat] {α ξ V : Type*} {n : ℕ} [Tarski.Structure L V]
    [Append V] [Tarski.Structure.Concat L V] {e : Fin n → V} {ε : ξ → V}
    (f : α → Semiterm L ξ n) (x : FreeSemigroup α) :
    (stringTerm f x).val e ε = FreeSemigroup.stringValue (fun a ↦ (f a).val e ε) x := by
  suffices ∀ (l : List α) (t : Semiterm L ξ n), (l.foldl (fun t a ↦ ‘!!t ⌢ !!(f a)’) t).val e ε =
      l.foldl (fun m a ↦ m ++ (f a).val e ε) (t.val e ε) from this x.tail (f x.head)
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

section eval

variable {V : Type*} [ConcatenationStructure V] {ξ : Type*} {n : ℕ} {e : Fin n → V} {ε : ξ → V}

@[simp]
lemma val_letter (b : Bool) : (letter b : Semiterm ℒ⌢ ξ n).val e ε = if b then 1 else 0 := by
  cases b <;> simp [letter]

@[simp]
lemma val_biteral (x : FreeSemigroup Bool) :
    (biteral x : Semiterm ℒ⌢ ξ n).val e ε = ConcatenationStructure.ofFreeSemigroup x := by
  simp [biteral, ConcatenationStructure.ofFreeSemigroup]

instance isOneOf_defined {l : List (FreeSemigroup Bool)} :
    ℒ⌢-predicate[V] (fun x ↦ ∃ γ ∈ l, x = ConcatenationStructure.ofFreeSemigroup γ) via isOneOf l :=
  ⟨fun v ↦ by simp [isOneOf]⟩

instance isOneOf_definable {l : List (FreeSemigroup Bool)} :
    ℒ⌢-predicate[V] (fun x ↦ ∃ γ ∈ l, x = ConcatenationStructure.ofFreeSemigroup γ) :=
  isOneOf_defined.to_definable

end eval

section isSubstring

variable {V : Type*} [Append V] {x y : V}

/--
`x` is a substring of `y`. Both associations of `u ++ x ++ v` are listed, so that the relation is
the one `isSubstring` defines in any structure with a concatenation.
- [Gan09, §1, Definition 1]
-/
def IsSubstring (x y : V) : Prop :=
  x = y ∨ (∃ u, y = u ++ x) ∨ (∃ v, y = x ++ v) ∨ (∃ u v, y = (u ++ x) ++ v) ∨
    ∃ u v, y = u ++ (x ++ v)

/-- A property that passes from a concatenation to its parts passes to substrings. -/
lemma IsSubstring.of_forall_append {P : V → Prop} (hP : ∀ x y, P (x ++ y) → P x ∧ P y)
    (h : IsSubstring x y) (hy : P y) : P x := by
  grind [IsSubstring]

section image

variable {β : Type*} {c : β → V} {w : β}
  (hc : ∀ {x y : V} {w : β}, x ++ y = c w → ∃ u v, x = c u ∧ y = c v)
include hc

/-- If the parts of a concatenation in the range of `c` are in it, so are the substrings. -/
lemma IsSubstring.exists_eq_of_append_eq (h : IsSubstring x (c w)) : ∃ u, x = c u :=
  h.of_forall_append (P := fun x ↦ ∃ u, x = c u)
    (fun _ _ ⟨_, h⟩ ↦ let ⟨u, v, hu, hv⟩ := hc h; ⟨⟨u, hu⟩, ⟨v, hv⟩⟩) ⟨w, rfl⟩

lemma IsSubstring.exists_eq_append_of_append_eq (h : IsSubstring (x ++ y) (c w)) :
    ∃ u v, x = c u ∧ y = c v :=
  let ⟨_, h⟩ := h.exists_eq_of_append_eq hc
  hc h

/--
The concatenation is associative on the substrings of the range of `c` if it is on the range and
the parts of a concatenation in the range are in it.
-/
lemma append_assoc_of_isSubstring_of_append_eq
    (hassoc : ∀ u v w, c u ++ c v ++ c w = c u ++ (c v ++ c w)) {z : V}
    (h : IsSubstring (x ++ y ++ z) (c w) ∨ IsSubstring (x ++ (y ++ z)) (c w)) :
    x ++ y ++ z = x ++ (y ++ z) := by
  rcases h with h | h
  · obtain ⟨a, r, ha, rfl⟩ := h.exists_eq_append_of_append_eq hc
    obtain ⟨p, q, rfl, rfl⟩ := hc ha
    exact hassoc p q r
  · obtain ⟨p, a, rfl, ha⟩ := h.exists_eq_append_of_append_eq hc
    obtain ⟨q, r, rfl, rfl⟩ := hc ha
    exact hassoc p q r

end image

instance isSubstring_defined {L : Language} [L.Concat] [L.Eq] [Tarski.Structure L V]
    [Tarski.Structure.Concat L V] [Tarski.Structure.Eq L V] :
    L-relation[V] IsSubstring via isSubstring := ⟨fun v ↦ by
  have : Nonempty V := ⟨v 0⟩
  simp [isSubstring, IsSubstring, exists_or, eq_comm (b := v 1)]⟩

instance isSubstring_definable {L : Language} [L.Concat] [L.Eq] [Tarski.Structure L V]
    [Tarski.Structure.Concat L V] [Tarski.Structure.Eq L V] : L-relation[V] IsSubstring :=
  isSubstring_defined.to_definable

end isSubstring

section substring

variable {V : Type*} [ConcatenationStructure V] {c x y : V}

@[simp]
lemma val_substringOperator {v : Fin 2 → V} :
    (substringOperator ℒ⌢).val v ↔ IsSubstring (v 0) (v 1) := by
  simp [substringOperator, Semiformula.Operator.val]

/-- `x` is one of the letters `0` and `1`. -/
def IsAtom (x : V) : Prop := x = 0 ∨ x = 1

/-- `x` is one of the letters `0` and `1`. -/
def isAtom : Semisentence ℒ⌢ 1 := “x. x = !!(op(0).const) ∨ x = !!(op(1).const)”

instance isAtom_defined : ℒ⌢-predicate[V] IsAtom via isAtom := ⟨fun v ↦ by simp [isAtom, IsAtom]⟩

instance isAtom_definable : ℒ⌢-predicate[V] IsAtom := isAtom_defined.to_definable

/--
`x` is a prefix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsPrefix (x y : V) : Prop := x = y ∨ ∃ v, y = x ++ v

/-- `x ◨ y`: `x` is a prefix of `y`. -/
scoped infix:50 " ◨ " => IsPrefix

/-- `x` is a prefix of `y`. -/
def isPrefix : Semisentence ℒ⌢ 2 := “x y. x = y ∨ ∃ v, y = x ⌢ v”

instance isPrefix_defined : ℒ⌢-relation[V] IsPrefix via isPrefix :=
  ⟨fun v ↦ by simp [isPrefix, IsPrefix]⟩

instance isPrefix_definable : ℒ⌢-relation[V] IsPrefix := isPrefix_defined.to_definable

/--
`x` is an initial segment of `y`: `x` is $0$ and `y` is not, or `y` extends `x`.
- [Dam17, §1]
-/
def IsInitialSegment (x y : V) : Prop := (x = 0 ∧ y ≠ 0) ∨ ∃ z, y = x ++ z

/--
`x` is a suffix of `y`.
- [Gan09, §1, Definition 1]
-/
def IsSuffix (x y : V) : Prop := x = y ∨ ∃ u, y = u ++ x

/-- `x ◧ y`: `x` is a suffix of `y`. -/
scoped infix:50 " ◧ " => IsSuffix

/-- `x` is a suffix of `y`. -/
def isSuffix {L : Language} [L.Eq] [L.Concat] : Semisentence L 2 := “x y. x = y ∨ ∃ u, y = u ⌢ x”

section

variable {L : Language} [L.Concat] [L.Eq] [Tarski.Structure L V] [Tarski.Structure.Concat L V]
  [Tarski.Structure.Eq L V]

instance isSuffix_defined : L-relation[V] IsSuffix via isSuffix :=
  ⟨fun v ↦ by simp [isSuffix, IsSuffix]⟩

instance isSuffix_definable : L-relation[V] IsSuffix := isSuffix_defined.to_definable

end

/--
`x` is a `c`-tally: every atom that is a substring of `x` is `c`.
- [Gan09, §1, Definition 1]
-/
def IsTally (c x : V) : Prop := ∀ y, IsAtom y → IsSubstring y x → y = c

/-- `x` is a `c`-tally. -/
def isTally : Semisentence ℒ⌢ 2 := “c x. ∀ y, !isAtom y → !isSubstring y x → y = c”

instance isTally_defined : ℒ⌢-relation[V] IsTally via isTally :=
  ⟨fun v ↦ by simp [isTally, IsTally]⟩

instance isTally_definable : ℒ⌢-relation[V] IsTally := isTally_defined.to_definable

@[simp]
lemma isAtom_zero : IsAtom (0 : V) := Or.inl rfl

@[simp]
lemma isAtom_one : IsAtom (1 : V) := Or.inr rfl

@[refl, simp]
lemma IsSubstring.refl (x : V) : IsSubstring x x := Or.inl rfl

@[simp]
lemma isSubstring_append_left (x y : V) : IsSubstring x (x ++ y) := by
  grind [IsSubstring]

@[simp]
lemma isSubstring_append_right (x y : V) : IsSubstring y (x ++ y) := by
  grind [IsSubstring]

@[simp]
lemma isSubstring_append_append (u x v : V) : IsSubstring x (u ++ x ++ v) := by
  grind [IsSubstring]

@[refl, simp]
lemma IsPrefix.refl (x : V) : x ◨ x := Or.inl rfl

@[simp]
lemma isPrefix_append (x y : V) : x ◨ x ++ y := by
  right; use y

@[refl, simp]
lemma IsSuffix.refl (x : V) : x ◧ x := Or.inl rfl

@[simp]
lemma isSuffix_append (x y : V) : y ◧ x ++ y := by
  right; use x

lemma IsPrefix.isSubstring (h : x ◨ y) : IsSubstring x y := by
  rcases h with rfl | ⟨v, rfl⟩ <;> simp

lemma IsSuffix.isSubstring (h : x ◧ y) : IsSubstring x y := by
  rcases h with rfl | ⟨u, rfl⟩ <;> simp

end substring

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

variable {V : Type*} [ConcatenationStructure V] {c : FreeSemigroup Bool}

@[simp]
lemma ofFreeSemigroup_zero : (ofFreeSemigroup (0 : FreeSemigroup Bool) : V) = 0 := rfl

@[simp]
lemma ofFreeSemigroup_one : (ofFreeSemigroup (1 : FreeSemigroup Bool) : V) = 1 := rfl

lemma ofFreeSemigroup_append_of_isAtom (u : FreeSemigroup Bool) (hc : IsAtom c) :
    (ofFreeSemigroup (u ++ c) : V) = ofFreeSemigroup u ++ ofFreeSemigroup c := by
  rcases hc with rfl | rfl <;>
    simp [ofFreeSemigroup, FreeSemigroup.stringValue, HMul.hMul, Mul.mul, zero_eq_of_false,
      one_eq_of_true, FreeSemigroup.of]

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

variable (V : Type*) [ConcatenationEmptyStructure V]

instance standardModelEmpty : Tarski.Structure ℒ⌢ₑ V where
  func := fun _ f ↦
    match f with
    | Sum.inl Concatenation.Func.zero => fun _ ↦ 0
    | Sum.inl Concatenation.Func.one => fun _ ↦ 1
    | Sum.inl Concatenation.Func.concat => fun v ↦ v 0 ++ v 1
    | Sum.inr (Constant.Func.const _) => fun _ ↦ ∅
  rel := fun _ r ↦
    match r with
    | Sum.inl Concatenation.Rel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢ₑ V := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Zero ℒ⌢ₑ V := ⟨rfl⟩

instance : Tarski.Structure.One ℒ⌢ₑ V := ⟨rfl⟩

instance : Tarski.Structure.Concat ℒ⌢ₑ V := ⟨fun _ _ ↦ rfl⟩

variable {V}

@[simp]
lemma val_star : (Semiterm.Operator.Star.star : Semiterm.Operator ℒ⌢ₑ 0).val ![] = (∅ : V) := rfl

lemma standardModelEmpty_ofEquiv {α : Type*} (e : α ≃ V) :
    @standardModelEmpty α (.ofEquiv e) = Tarski.Structure.ofEquiv e.symm :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by rcases f with (_ | _ | _) | ⟨⟨⟩⟩ <;> rfl)
    (funext₃ fun k r v ↦ by
      rcases r with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      exact propext e.apply_eq_iff_eq.symm)

end semantics

section eval

open ConcatenationStructure ConcatenationEmptyStructure

variable {V : Type*} [ConcatenationEmptyStructure V] {ξ : Type*} {n : ℕ} {e : Fin n → V} {ε : ξ → V}
  {x y : V}

@[simp]
lemma val_biteralEmpty (l : List Bool) :
    (biteralEmpty l : Semiterm ℒ⌢ₑ ξ n).val e ε = ofList l := by
  have hb (b : Bool) : (letter b : Semiterm ℒ⌢ₑ ξ n).val e ε = if b then 1 else 0 := by
    cases b <;> simp [letter]
  cases l <;> simp [biteralEmpty, ofList, biteral, ofFreeSemigroup, hb]

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

variable {V : Type*} [ConcatenationEmptyStructure V] {u : List Bool}

@[simp]
lemma ofList_nil : (ofList [] : V) = ∅ := rfl

@[simp]
lemma ofList_false : (ofList [false] : V) = 0 := rfl

@[simp]
lemma ofList_true : (ofList [true] : V) = 1 := rfl

lemma ofList_append_singleton (hu : u ≠ []) (b : Bool) :
    (ofList (u ++ [b]) : V) = ofList u ++ ofList [b] := by
  cases u <;> simp_all [ofList, ofFreeSemigroup, FreeSemigroup.stringValue]

@[simp]
lemma isAtom_ofList_singleton (b : Bool) : IsAtom (ofList [b] : V) := by
  cases b <;> simp

end ofList

lemma completeEmpty (T : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ T] (φ : Sentence ℒ⌢ₑ)
    (H : ∀ (V : Type*) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* T], V↓[ℒ⌢ₑ] ⊧ φ) : T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun V _ s _ hT ↦ by
    let c : ConcatenationEmptyStructure V :=
      { zero := s.func (Sum.inl Concatenation.Func.zero) ![]
        one := s.func (Sum.inl Concatenation.Func.one) ![]
        append a b := s.func (Sum.inl Concatenation.Func.concat) ![a, b]
        emptyCollection := s.func (Sum.inr <| Constant.Func.const ⟨⟩) ![] }
    have e : s = standardModelEmpty V :=
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
            (Tarski.Structure.eq_lang (L := ℒ⌢ₑ) (M := V) (v := v)).eq)
    rw [e] at hT ⊢
    exact H V

lemma weakerThan_of_models_empty (T S : Theory ℒ⌢ₑ) [𝗘𝗤 ℒ⌢ₑ ⪯ S]
    (H : ∀ (V : Type*) [ConcatenationEmptyStructure V] [V↓[ℒ⌢ₑ] ⊧* S], V↓[ℒ⌢ₑ] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ completeEmpty _ _ fun V _ _ ↦ Theory.Proof.sound h (H V)

section letters

open LetterStructure

variable {α : Type}

/-- The constant denoting the letter `a`. -/
def letterTerm {ξ : Type*} {n : ℕ} (a : α) : Semiterm ℒ⌢[α] ξ n := .func (.letter a) ![]

section semantics

variable (V : Type*) [LetterStructure α V]

instance lettersModel : Tarski.Structure ℒ⌢[α] V where
  func := fun _ f ↦
    match f with
    | .letter a => fun _ ↦ ofLetter a
    | .concat => fun v ↦ v 0 ++ v 1
  rel := fun _ r ↦
    match r with
    | .eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Eq ℒ⌢[α] V := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Tarski.Structure.Concat ℒ⌢[α] V := ⟨fun _ _ ↦ rfl⟩

variable {V}

@[simp]
lemma val_letterTerm {ξ : Type*} {n : ℕ} {e : Fin n → V} {ε : ξ → V} (a : α) :
    (letterTerm a : Semiterm ℒ⌢[α] ξ n).val e ε = ofLetter a := rfl

end semantics

lemma completeLetters (T : Theory ℒ⌢[α]) [𝗘𝗤 ℒ⌢[α] ⪯ T] (φ : Sentence ℒ⌢[α])
    (H : ∀ (V : Type*) [Nonempty V] [LetterStructure α V] [V↓[ℒ⌢[α]] ⊧* T], V↓[ℒ⌢[α]] ⊧ φ) :
    T ⊢ φ :=
  Theory.Proof.complete_on_eq_models φ fun V _ s _ hT ↦ by
    let c : LetterStructure α V :=
      { ofLetter a := s.func (.letter a) ![]
        append x y := s.func .concat ![x, y] }
    have e : s = lettersModel V :=
      Tarski.Structure.ext
        (funext₃ fun k f v ↦
          match k, f with
          | _, .letter a => congrArg _ <| Matrix.empty_eq v
          | _, .concat => congrArg _ <| Matrix.fun_eq_vec_two v)
        (funext₃ fun k r v ↦
          match k, r with
          | _, .eq => (Tarski.Structure.eq_lang (L := ℒ⌢[α]) (M := V) (v := v)).eq)
    rw [e] at hT ⊢
    exact H V

/-- The nonempty strings of the letters `α` under concatenation. -/
instance : LetterStructure α (FreeSemigroup α) where
  ofLetter := FreeSemigroup.of

end letters

end Concatenation

end FFL.FirstOrder

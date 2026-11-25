module

public import Concatenation.OpenProblems.BoundedQuantifiers
public import Mathlib.Computability.Language
public import Mathlib.Data.Set.Card
import Concatenation.OpenProblem

/-!
# Open problems on the subword ordering

The existential formulas over the words on an alphabet, ordered by the relation of being a
subword, with constants for words. The free variables of the formulas serve as the constants.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Subword

/--
The words over the alphabet `A`, ordered by the relation of being a subword.
- [HSZ17, §2]
-/
instance (A : Type*) : Tarski.Structure Language.prefixRel (List A) where
  func := fun _ f _ ↦ f.elim
  rel := fun _ r v ↦ match r with
    | .pref => (v 0).Sublist (v 1)

/--
The words consisting of `l` blocks $a_1^* \cdots a_n^*$.
- [HSZ17, §2]
-/
def alternationBounded (n l : ℕ) : _root_.Language (Fin n) :=
  {w | ∃ u : Fin l → List (Fin n), (∀ i, (u i).Pairwise (· ≤ ·)) ∧ w = (List.ofFn u).flatten}

/--
`K` is defined by a formula of the fragment $\Sigma_{1,j}$: an existential formula with constants
for all words, in which at most `j` variables, counting the free one, range over all words, while
each of the others is restricted to the words of a bounded number of blocks.
- [HSZ17, §2]
-/
def IsAlternationDefinable {n : ℕ} (j : ℕ) (K : _root_.Language (Fin n)) : Prop :=
  ∃ (k : ℕ) (φ : Semiformula Language.prefixRel (List (Fin n)) (k + 1))
    (b : Fin (k + 1) → Option ℕ),
    φ.Open ∧ {i | b i = none}.ncard ≤ j ∧
    ∀ x, x ∈ K ↔ ∃ v : Fin (k + 1) → List (Fin n), v 0 = x ∧
      (∀ i, ∀ l ∈ b i, v i ∈ alternationBounded n l) ∧ φ.Eval v id

/--
Do the fragments $\Sigma_{1,1}$ and $\Sigma_{1,2}$ of the logic of the subword ordering, with
constants for all words, define the same languages?
- [HSZ17, §6]
-/
open_problem isAlternationDefinable_one_iff_two :=
  ∀ (n : ℕ) (K : _root_.Language (Fin n)), IsAlternationDefinable 1 K ↔ IsAlternationDefinable 2 K

/--
For which words $W_0, W_1, \dots$ is the truth of the existential sentences on the subword
ordering with constants for these words decidable?
- [HSZ17, §3.1]
-/
open_problem existential_subword_decidable {n : ℕ} (W : ℕ → List (Fin n)) :=
  ComputablePred fun φ : Formula Language.prefixRel ℕ ↦ φ.Existential ∧ φ.Evalf W

/--
Is there an undecidable language definable by an existential formula, without constants, on the
subword ordering?
- [BGTZ23, §5]
-/
open_problem exists_undecidable_existential_subword :=
  ∃ (n : ℕ) (φ : Semisentence Language.prefixRel 1), φ.Existential ∧
    ¬ComputablePred fun w : List (Fin n) ↦ φ.Evalb ![w]

/--
`R` is definable on the words over `A` by an existential formula with constants for all words.
- [BGTZ23, §1]
-/
def IsExistentiallyDefinable {A : Type*} {k : ℕ} (R : (Fin k → List A) → Prop) : Prop :=
  ∃ φ : Semiformula Language.prefixRel (List A) k, φ.Existential ∧ ∀ w, R w ↔ φ.Eval w id

/--
Is every computably enumerable relation on the words over two letters definable by an existential
formula with constants for all words on the subword ordering?
- [BGTZ23, §6]
-/
open_problem isExistentiallyDefinable_of_re :=
  ∀ (k : ℕ) (R : (Fin k → List Bool) → Prop), REPred R → IsExistentiallyDefinable R

/--
Is the language of the words over $\{a, b\}$ that do not contain $aba$ as an infix definable by an
existential formula with constants for all words on the subword ordering?
- [BGTZ23, §1]
-/
open_problem isExistentiallyDefinable_not_infix :=
  IsExistentiallyDefinable fun w : Fin 1 → List Bool ↦ ¬[false, true, false] <:+: w 0

/--
Is the reversal relation on the words over two letters definable by an existential formula with
constants for all words on the subword ordering?
- [BGTZ23, §1]
-/
open_problem isExistentiallyDefinable_reverse :=
  IsExistentiallyDefinable fun w : Fin 2 → List Bool ↦ w 1 = (w 0).reverse

end Subword

end FFL.FirstOrder

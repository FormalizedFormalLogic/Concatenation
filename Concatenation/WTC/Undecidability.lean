module

public import Concatenation.Coding
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.Undecidability
public import Concatenation.WTC.Arithmetic
public import Concatenation.WTC.Embedding

/-!
# Essential undecidability of $\mathsf{WTC}$

$\mathsf{WTC}$, with two or more letters, is mutually interpretable with $\mathsf{R}_0$, and
essentially undecidable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
$\mathsf{WTC}$ and $\mathsf{R}_0$ are mutually interpretable.
- [Hor11, §3, Theorem 3.15]
- [Hor12, §4, Theorem 4.1]
-/
noncomputable instance : 𝗪𝗧𝗖 ⋈ 𝗥₀ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{WTC}$ is essentially undecidable.
- [Hor11, §3, Corollary 3.17]
- [Hor12, §4, Corollary 4.11]
-/
instance : (𝗪𝗧𝗖 : ConcatenationTheory).EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀)

instance {α : Type} [Nonempty α] : (FreeSemigroup α)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] :=
  IsInitialEmbedding.models_WTCLetters (c := id)
    { injective := Function.injective_id
      map_letter := fun _ ↦ rfl
      map_append := fun _ _ ↦ rfl
      exists_of_append_eq := fun {x y} _ _ ↦ ⟨x, y, rfl, rfl⟩ }

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := models_WTC_concatenationStructure Bool.false_ne_true

instance : Entailment.Consistent 𝗪𝗧𝗖 :=
  let : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

/--
$\mathsf{WTC}$ is undecidable.
- [Hor11, §3, Corollary 3.17]
-/
theorem WTC.undecidable : Entailment.Undecidable 𝗪𝗧𝗖 :=
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖

section letters

variable {α β : Type} [Primcodable α] [Nontrivial α] [Primcodable β] [Nontrivial β]

/--
The weak theory of concatenation with at least two letters and $\mathsf{R}_0$ are mutually
interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗥₀ where
  r := DirectInterpretation.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀) inferInstance
  l := inferInstance

/--
The weak theory of concatenation with at least two letters and $\mathsf{WTC}$ are mutually
interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖 where
  r := inferInstance
  l := DirectInterpretation.comp (inferInstance : 𝗥₀ ⊳ 𝗪𝗧𝗖[α]) inferInstance

/--
Any two weak theories of concatenation with at least two letters are mutually interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
noncomputable instance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖[β] :=
  MutualDirectInterpretation.trans (inferInstance : 𝗪𝗧𝗖[α] ⋈ 𝗪𝗧𝗖)
    (MutualDirectInterpretation.symm inferInstance)

/--
For all $m, n \ge 2$, $\mathsf{WTC}_m$ and $\mathsf{WTC}_n$ are mutually interpretable.
- [Hor11, §3, Theorem 3.18]
- [Hor12, §4, Theorem 4.13]
- [HH14, Theorem 10]
-/
noncomputable abbrev WTCLetters.mutualInterpretation {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    𝗪𝗧𝗖[Fin m] ⋈ 𝗪𝗧𝗖[Fin n] :=
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  inferInstance

instance {α : Type} [Nonempty α] : Entailment.Consistent 𝗪𝗧𝗖[α] :=
  let : (FreeSemigroup α)↓[ℒ⌢[α]] ⊧* 𝗪𝗧𝗖[α] := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

variable {n : ℕ}

/--
For every $n \ge 2$, $\mathsf{WTC}_n$ is essentially undecidable.
- [Hor11, §3, Corollary 3.17, Theorem 3.18]
- [Hor12, §4, Corollary 4.11, Theorem 4.13]
-/
theorem WTCLetters.essentiallyUndecidable (hn : 2 ≤ n) : 𝗪𝗧𝗖[Fin n].EssentiallyUndecidable :=
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗪𝗧𝗖[Fin n] ⋈ 𝗥₀).r

/--
For every $n \ge 2$, $\mathsf{WTC}_n$ is undecidable.
- [Hor11, §3, Corollary 3.17, Theorem 3.18]
- [Hor12, §4, Corollary 4.11, Theorem 4.13]
-/
theorem WTCLetters.undecidable (hn : 2 ≤ n) : Entailment.Undecidable 𝗪𝗧𝗖[Fin n] :=
  have := essentiallyUndecidable hn
  have : Nonempty (Fin n) := ⟨⟨0, by lia⟩⟩
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖[Fin n]

end letters

end FFL.FirstOrder.Concatenation

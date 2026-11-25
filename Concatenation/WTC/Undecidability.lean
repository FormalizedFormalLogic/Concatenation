module

public import Concatenation.Coding
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.Undecidability
public import Concatenation.WTC.Arithmetic
public import Concatenation.WTC.Embedding

/-!
# Essential undecidability of $\mathsf{WTC}$

$\mathsf{WTC}$ is mutually interpretable with $\mathsf{R}_0$, and essentially undecidable.
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

instance : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 :=
  IsInitialEmbedding.models_WTC (c := id)
    { injective := Function.injective_id
      map_zero := rfl
      map_one := rfl
      map_append := fun _ _ ↦ rfl
      exists_of_append_eq := fun {x y} _ _ ↦ ⟨x, y, rfl, rfl⟩ }

instance : Entailment.Consistent 𝗪𝗧𝗖 :=
  let : (FreeSemigroup Bool)↓[ℒ⌢] ⊧* 𝗪𝗧𝗖 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

/--
$\mathsf{WTC}$ is undecidable.
- [Hor11, §3, Corollary 3.17]
-/
theorem WTC.undecidable : Entailment.Undecidable 𝗪𝗧𝗖 :=
  Theory.EssentiallyUndecidable.undecidable 𝗪𝗧𝗖

end FFL.FirstOrder.Concatenation

module

public import Concatenation.TC.Arithmetic
public import Concatenation.TC.Matrix
public import Concatenation.ToFoundation.Arithmetic.PeanoMinusInterpretation

/-!
# Mutual interpretability of $\mathsf{Q}$ and $\mathsf{TC}$

$\mathsf{Q}$ and $\mathsf{TC}$ are mutually interpretable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
$\mathsf{Q}$ interprets $\mathsf{TC}$.
- [Gan09, §3, Theorem 5]
- [Mur24, §6]
-/
instance : 𝗤 ⊳ 𝗧𝗖 :=
  DirectInterpretation.comp (inferInstance : 𝗣𝗔⁻ ⊳ 𝗧𝗖) (inferInstance : 𝗤 ⊳ 𝗣𝗔⁻)

/--
$\mathsf{Q}$ and $\mathsf{TC}$ are mutually interpretable.
- [Gan09, §3, Theorem 5]
-/
instance : 𝗤 ⋈ 𝗧𝗖 := ⟨inferInstance, inferInstance⟩

end FFL.FirstOrder.Concatenation

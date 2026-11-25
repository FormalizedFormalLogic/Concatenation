module

public import Concatenation.Coding
public import Concatenation.Semantics.Standard
public import Concatenation.TC.Arithmetic
public import Concatenation.ToFoundation.Arithmetic.R0.Undecidability
public import Concatenation.ToFoundation.Interpretability.Undecidability

/-!
# Essential undecidability of $\mathsf{TC}$

$\mathsf{TC}$ inherits essential undecidability from $\mathsf{Q}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
$\mathsf{TC}$ is essentially undecidable.
- [GZ08, Theorem 16]
-/
instance : (𝗧𝗖 : ConcatenationTheory).EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗧𝗖 ⊳ 𝗤)

/--
$\mathsf{TC}$ is undecidable.
- [GZ08, Theorem 16]
-/
theorem undecidable : Entailment.Undecidable 𝗧𝗖 := Theory.EssentiallyUndecidable.undecidable 𝗧𝗖

end FFL.FirstOrder.Concatenation

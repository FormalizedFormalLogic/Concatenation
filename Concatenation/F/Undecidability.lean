module

public import Concatenation.F.Radical
public import Concatenation.F.Tame
public import Concatenation.TC.EmptyInterpretation
public import Concatenation.TC.Undecidability

/-!
# Essential undecidability of $\mathsf{F}$
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

/--
$\mathsf{F}$ interprets $\mathsf{TC}$.
- [Gan09, §4, Lemma 8]
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⊳ 𝗧𝗖 :=
  DirectInterpretation.comp (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖) (inferInstance : 𝗙 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{TC}$ interprets $\mathsf{F}$.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗧𝗖 ⊳ 𝗙 :=
  DirectInterpretation.comp (inferInstance : 𝗧𝗖ₑ ⊳ 𝗙) (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ)

/--
$\mathsf{F}$ and $\mathsf{TC}$ with the empty string are mutually interpretable.
- [Hor11, §2, Theorem 2.12]
-/
instance : 𝗙 ⋈ 𝗧𝗖ₑ := ⟨inferInstance, inferInstance⟩

/--
$\mathsf{F}$ and $\mathsf{TC}$ are mutually interpretable.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4, Theorem 6]
-/
instance : 𝗙 ⋈ 𝗧𝗖 := ⟨inferInstance, inferInstance⟩

instance : Entailment.Consistent 𝗧𝗖ₑ := DirectInterpretation.consistent (inferInstance : 𝗧𝗖 ⊳ 𝗧𝗖ₑ)

instance : Entailment.Consistent 𝗙 := DirectInterpretation.consistent (inferInstance : 𝗧𝗖 ⊳ 𝗙)

/--
$\mathsf{TC}$ with the empty string is essentially undecidable.
- [Hor11, §2]
-/
instance : 𝗧𝗖ₑ.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗧𝗖ₑ ⊳ 𝗧𝗖)

/--
$\mathsf{F}$ is essentially undecidable.
- [Hor11, §2, Theorem 2.12]
- [Gan09, §4]
-/
instance : 𝗙.EssentiallyUndecidable :=
  DirectInterpretation.essentiallyUndecidable (inferInstance : 𝗙 ⊳ 𝗧𝗖)

end FFL.FirstOrder.Concatenation

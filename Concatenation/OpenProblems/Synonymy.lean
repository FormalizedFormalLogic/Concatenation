module

public import Concatenation.F.Basic
public import Concatenation.TC.Basic
public import Concatenation.ToFoundation.Arithmetic.R
public import Concatenation.ToFoundation.Interpretability.BiInterpretation
public import Concatenation.ToFoundation.Interpretability.DefinitionalEquivalence
public import Concatenation.WTC.Basic
public import Foundation.FirstOrder.Arithmetic.Q.Basic
import Concatenation.OpenProblem

/-!
# Open problems on bi-interpretability and synonymy

Pairs of mutually interpretable theories of arithmetic and concatenation.
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Concatenation

/--
Are $\mathsf{R}$ and $\mathsf{WTC}$, which are mutually interpretable by the cited theorem,
bi-interpretable?
- [HH14, Theorem 1]
-/
open_problem R_biInterpretable_WTC := Nonempty (BiInterpretation 𝗥 𝗪𝗧𝗖)

/--
Are $\mathsf{R}$ and $\mathsf{WTC}$, which are mutually interpretable by the cited theorem,
synonymous?
- [HH14, Theorem 1]
-/
open_problem R_definitionallyEquivalent_WTC := Nonempty (DefinitionalEquivalence 𝗥 𝗪𝗧𝗖)

/--
Are $\mathsf{Q}$ and $\mathsf{TC}$, whose mutual interpretability is recalled in the cited section,
bi-interpretable?
- [HH14, §1]
-/
open_problem Q_biInterpretable_TC := Nonempty (BiInterpretation 𝗤 𝗧𝗖)

/--
Are $\mathsf{Q}$ and $\mathsf{TC}$, whose mutual interpretability is recalled in the cited section,
synonymous?
- [HH14, §1]
-/
open_problem Q_definitionallyEquivalent_TC := Nonempty (DefinitionalEquivalence 𝗤 𝗧𝗖)

/--
Are $\mathsf{F}$ and $\mathsf{TC}$, which are mutually interpretable by the cited theorem,
bi-interpretable?
- [Hor11, §2, Theorem 2.12]
-/
open_problem F_biInterpretable_TC := Nonempty (BiInterpretation 𝗙 𝗧𝗖)

/--
Are $\mathsf{F}$ and $\mathsf{TC}$, which are mutually interpretable by the cited theorem,
synonymous?
- [Hor11, §2, Theorem 2.12]
-/
open_problem F_definitionallyEquivalent_TC := Nonempty (DefinitionalEquivalence 𝗙 𝗧𝗖)

end Concatenation

end FFL.FirstOrder

module

public import Concatenation.Seq.Editor
public import Concatenation.SetTheory.Sequential
import Concatenation.OpenProblem

/-!
# An open problem on theories of sequences
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Sequence

/--
Is $\mathsf{Seq}^*$ sequential?
- [KM24, §4.2, Problem 10]
-/
open_problem SeqStar_sequential := Theory.Sequential 𝗦𝗲𝗾⋆

end Sequence

end FFL.FirstOrder

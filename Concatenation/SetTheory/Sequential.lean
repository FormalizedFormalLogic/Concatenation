module

public import Concatenation.SetTheory.Adjunctive
public import Concatenation.ToFoundation.Interpretability.Unrelativized

/-!
# Sequential theories
-/

@[expose] public section

namespace FFL.FirstOrder

/--
`T` is sequential: it interprets adjunctive set theory on its whole universe, preserving equality.
- [Mur23, Definition 198]
- [KM24, §1, §3]
-/
def Theory.Sequential {L : Language} [L.Eq] (T : Theory L) [𝗘𝗤 _ ⪯ T] : Prop :=
  UnrelativizedInterprets T 𝗔𝗦

end FFL.FirstOrder

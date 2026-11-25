module

public import Foundation.FirstOrder.LK.Basic
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding
public import Foundation.Logic.Decidability

/-!
# Essentially undecidable theories

First-order theories all of whose consistent extensions are undecidable.
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language} [L.Encodable] [L.Primcodable]

/--
Every consistent extension of `T` in its language is undecidable.
- [Sve08, §1]
-/
class Theory.EssentiallyUndecidable (T : Theory L) : Prop where
  undecidable_of_consistent : ∀ U : Theory L, T ⪯ U → Entailment.Consistent U →
    Entailment.Undecidable U

namespace Theory.EssentiallyUndecidable

theorem undecidable (T : Theory L) [T.EssentiallyUndecidable] [Entailment.Consistent T] :
    Entailment.Undecidable T :=
  undecidable_of_consistent (T := T) T (Entailment.WeakerThan.refl T) inferInstance

theorem of_weakerThan (T U : Theory L) [T.EssentiallyUndecidable] [T ⪯ U] :
    U.EssentiallyUndecidable where
  undecidable_of_consistent V hUV hV :=
    undecidable_of_consistent (T := T) V (Entailment.WeakerThan.trans inferInstance hUV) hV

instance (T : Theory L) [T.EssentiallyUndecidable] : Entailment.EssentiallyUndecidable T where
  essentially_undec U hTU hU := undecidable_of_consistent U hTU <|
    Entailment.consistent_of_incomplete (h := hU)

end Theory.EssentiallyUndecidable

end FFL.FirstOrder

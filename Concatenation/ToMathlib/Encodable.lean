module

public import Mathlib.Logic.Encodable.Basic

/-!
# Decoding of sums
-/

@[expose] public section

namespace Encodable

variable {α β : Type*} [Encodable α] [Encodable β] (n : ℕ)

lemma decode_sum_two_mul :
    (decode (2 * n) : Option (α ⊕ β)) = (decode n : Option α).map Sum.inl := by
  simp [decode_sum_val, decodeSum]

lemma decode_sum_two_mul_add_one :
    (decode (2 * n + 1) : Option (α ⊕ β)) = (decode n : Option β).map Sum.inr := by
  simp [decode_sum_val, decodeSum]

end Encodable

module

public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.R0.Cobham

/-!
# Cobham's order on models of $\mathsf{R}_0$

Definability of Cobham's order, and Cobham's order on `ℕ`.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open ORingStructure
open scoped FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V]

instance isRegular_definable : 𝚺ᴬ₀-Predicate[V] IsRegular := isRegular_defined.to_definable

instance cobhamLE_definable : 𝚺ᴬ₀-Relation[V] CobhamLE := cobhamLE_defined.to_definable

instance cobhamLT_definable : 𝚺ᴬ₀-Relation[V] CobhamLT := cobhamLT_defined.to_definable

@[simp, grind =]
lemma nat_cobhamLE_iff {m n : ℕ} : m ≤ᶜ n ↔ m ≤ n := by
  simpa using numeral_cobhamLE_numeral_iff (V := ℕ) (k := m) (n := n)

end FFL.FirstOrder.Arithmetic

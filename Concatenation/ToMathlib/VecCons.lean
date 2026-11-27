module

public import Mathlib.Data.Fin.VecNotation

/-!
# Composing with `Matrix.vecCons`

Precomposition with a vector built by `Matrix.vecCons`, in the lambda form `simp` meets.
-/

@[expose] public section

namespace Matrix

variable {α : Type*} {m n : ℕ}

lemma fun_vecCons_apply (w : Fin m → α) (a : Fin m) (f : Fin n → Fin m) :
    (fun i ↦ w (vecCons a f i)) = vecCons (w a) fun i ↦ w (f i) :=
  funext fun i ↦ by cases i using Fin.cases <;> simp

end Matrix

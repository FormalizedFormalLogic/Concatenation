module

public import Concatenation.ToFoundation.Arithmetic.R0.Visser
public import Concatenation.WTC.Arithmetic
public import Concatenation.WTC.LocallyFinitelySatisfiable

/-!
# Interpretability in $\mathsf{WTC}$

A recursively enumerable theory of a finite language is interpretable in $\mathsf{WTC}$ if and only
if it is locally finitely satisfiable.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

variable {L : Language} [L.Eq] [L.Finite] [L.Encodable] [L.Primcodable] {T : Theory L} [𝗘𝗤 L ⪯ T]

/--
A recursively enumerable theory of a finite language is interpretable in $\mathsf{WTC}$ if and only
if it is locally finitely satisfiable.
- [Hor11, §3, Corollary 3.16]
- [Hor12, §4, Corollary 4.12]
- [HH14, Theorem 2]
-/
theorem WTC.nonempty_interpretation_iff_locallyFinitelySatisfiable (hT : REPred (· ∈ T)) :
    Nonempty (𝗪𝗧𝗖 ⊳ T) ↔ T.LocallyFinitelySatisfiable :=
  ⟨fun ⟨π⟩ ↦ π.locallyFinitelySatisfiable locallyFinitelySatisfiable, fun h ↦
    let ⟨π⟩ := Arithmetic.R0.nonempty_interpretation_of_locallyFinitelySatisfiable hT h
    ⟨π.comp (inferInstance : 𝗪𝗧𝗖 ⊳ 𝗥₀)⟩⟩

end FFL.FirstOrder.Concatenation

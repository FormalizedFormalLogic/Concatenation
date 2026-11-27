module

public import Concatenation.TC.ISigma
public import Concatenation.ToFoundation.BoundingHierarchy

/-!
# $\mathsf{PA}$ interprets $\mathsf{TCI}$

The translation by the bijective binary numerals that interprets $\Sigma_n\text{-}\mathsf{TCI}$ in
$\mathsf{I}\Sigma_n$ does not depend on `n`, and every formula lies in some level of the bounded
hierarchy, so the same translation interprets $\mathsf{TCI}$ in $\mathsf{PA}$.
-/

@[expose] public section

namespace FFL.FirstOrder.Concatenation

open DirectTranslation Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/--
The bijective binary numerals of a model of $\mathsf{PA}$ form a model of $\mathsf{TCI}$.
- [Gan09, §1]
-/
instance {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    ((binaryTranslation 𝗣𝗔).Model V)↓[ℒ⌢ₑ] ⊧* 𝗧𝗖𝗜 := by
  rw [binaryTranslation.struc_eq]
  let := binaryTranslation.concatenationEmptyStructure 𝗣𝗔 V
  have append (x y : V) : binaryTranslation.equiv 𝗣𝗔 V (binaryAppend x y) =
      binaryTranslation.equiv 𝗣𝗔 V x ++ binaryTranslation.equiv 𝗣𝗔 V y := rfl
  constructor
  intro σ hσ
  cases hσ with
  | tcEmpty _ hσ =>
    exact (models_TCISigma (binaryTranslation.equiv 𝗣𝗔 V) rfl rfl rfl append 0).models_set
      (IsTCISigmaAxiom.tcEmpty _ hσ)
  | notationInduction φ =>
    obtain ⟨s, hφ⟩ := Bounding.Hierarchy.exists_level (substringBounding ℒ⌢ₑ) 𝚺 φ
    have : Nonempty ((binaryTranslation 𝗣𝗔).Model V) := ⟨∅⟩
    simpa [models_iff, Semiformula.eval_univCl] using fun ε ↦
      eval_notationInduction (binaryTranslation.equiv 𝗣𝗔 V) rfl rfl rfl append s hφ ε

/--
$\mathsf{PA}$ interprets $\mathsf{TCI}$ by the bijective binary numerals.
- [Gan09, §1]
-/
noncomputable instance binaryInterpretationPA : 𝗣𝗔 ⊳ 𝗧𝗖𝗜 where
  trln := binaryTranslation 𝗣𝗔
  interpret_theory _ hφ := Arithmetic.complete.{0} _ _ fun _ _ _ ↦
    DirectTranslation.models_translate_of_mem hφ

end FFL.FirstOrder.Concatenation

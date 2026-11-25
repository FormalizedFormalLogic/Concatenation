module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Mathlib.Tactic.Ring

/-!
# An injective pairing in $\mathsf{PA}^-$
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {M : Type*} [ORingStructure M] {x y x' y' z : M}

/-- The pair $(x + y)^2 + x$ of `x` and `y`. -/
def squarePair (x y : M) : M := (x + y) * (x + y) + x

/-- `z` is the pair $(x + y)^2 + x$ of `x` and `y`. -/
def isSquarePair : ArithmeticSemisentence 3 := “z x y. z = (x + y) * (x + y) + x”

@[simp]
lemma eval_isSquarePair : M ⊧/![z, x, y] isSquarePair ↔ z = squarePair x y := by
  simp [isSquarePair, squarePair]

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

private lemma squarePair_lt (h : x + y < x' + y') : squarePair x y < squarePair x' y' := by
  have h₁ : x + y + 1 ≤ x' + y' := by
    obtain ⟨z, hz, h₂⟩ := lt_iff_exists_add.mp h
    rw [h₂]
    gcongr
    exact one_le_of_zero_lt z hz
  calc
    squarePair x y ≤ (x + y) * (x + y) + (x + y) := by simp [squarePair]
    _ < (x + y + 1) * (x + y + 1) := by
      have : (x + y + 1) * (x + y + 1) = (x + y) * (x + y) + (x + y) + (x + y + 1) := by ring
      rw [this]
      exact lt_add_of_pos_right _ <| by simp
    _ ≤ (x' + y') * (x' + y') := by gcongr
    _ ≤ squarePair x' y' := by simp [squarePair]

@[simp]
lemma squarePair_inj : squarePair x y = squarePair x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    rcases lt_trichotomy (x + y) (x' + y') with h₁ | h₁ | h₁
    · exact absurd h (squarePair_lt h₁).ne
    · obtain rfl : x = x' := by simpa [squarePair, h₁] using h
      exact ⟨rfl, by simpa using h₁⟩
    · exact absurd h (squarePair_lt h₁).ne'
  · rintro ⟨rfl, rfl⟩
    rfl

end FFL.FirstOrder.Arithmetic

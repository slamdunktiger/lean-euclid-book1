/-
  Euclid's Elements, Book I, Proposition 11
  "To draw a straight line at right angles to a given straight line
   from a given point on it."

  Given a line through A and B and a point C on that line, there exists
  a point P such that the segment CP is perpendicular to AB, i.e.
  ⟨P - C, B - A⟩ = 0.

  We construct P by rotating the direction vector (B - A) by 90°:
  P = C + rot90 (B - A), where rot90 (x, y) = (-y, x). Then
  ⟨rot90 u, u⟩ = (-u₁)·u₀ + u₀·u₁ = 0, so CP ⟂ AB.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

open Real

namespace Euclid.BookI.Prop11

/-- 90° rotation in ℝ²: rot90 (x, y) = (-y, x). -/
noncomputable def rot90
    (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(-u 1), u 0]

/-- Euclid I.11: from a point C, a perpendicular to the line AB can be erected.

    Given distinct points A, B (defining the line) and any point C, there
    exists P such that ⟨P - C, B - A⟩ = 0 (i.e. CP ⟂ AB). -/
theorem perpendicular_exists
    (A B C : EuclideanSpace ℝ (Fin 2)) (_hAB : A ≠ B) :
    ∃ P : EuclideanSpace ℝ (Fin 2),
      inner ℝ (P - C) (B - A) = 0 := by
  let u := B - A
  let P := C + rot90 u
  refine ⟨P, ?_⟩
  -- P - C = rot90 u.
  have : P - C = rot90 u := by
    unfold P u
    abel
  rw [this]
  -- Goal: inner ℝ (rot90 u) u = 0. Expand both via WithLp coordinates.
  unfold rot90 u
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  dsimp only [WithLp.toLp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.inner_apply]
  -- Goal: (-(u 1)) * (u 0) + (u 0) * (u 1) = 0 = -a*b + b*a.
  ring

end Euclid.BookI.Prop11

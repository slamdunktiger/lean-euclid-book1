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

  (The construction works for any point C; requiring C to lie on AB
  recovers Euclid's formulation.)

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
    (A B C : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B) :
    ∃ P : EuclideanSpace ℝ (Fin 2),
      @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ (P - C) (B - A) = 0 := by
  let u := B - A
  let P := C + rot90 u
  refine ⟨P, ?_⟩
  -- ⟨P - C, B - A⟩ = ⟨rot90 u, u⟩ by bilinearity, then polarization.
  rw [inner_sub_left, inner_add_left]
  rw [add_comm (inner ℝ C (B - A)), add_sub_cancel_right]
  -- Goal: ⟨rot90 u, u⟩ = 0. Use polarization:
  --   ⟨x, y⟩ = (‖x + y‖² - ‖x - y‖²) / 4
  let x := rot90 u
  let y := u
  have hsum : ‖x + y‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
    unfold x y rot90 u
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs, sq_abs, sq_abs]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               sub_add_eq_sub_sub, add_sub, add_sub_assoc]
    ring
  have hdiff : ‖x - y‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
    unfold x y rot90 u
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs, sq_abs, sq_abs]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               sub_sub, sub_add_eq_sub_sub, sub_sub_assoc]
    ring
  have hx : ‖x‖ ^ 2 = ‖u‖ ^ 2 := by
    unfold x rot90 u
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
    rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hy : ‖y‖ ^ 2 = ‖u‖ ^ 2 := by
    unfold y
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    rw [Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
    ring
  -- ⟨x,y⟩ = (‖x+y‖² - ‖x‖² - ‖y‖²)/2  (real polarization)
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y,
      hsum, hx, hy, sub_self, zero_div, sub_self, zero_div, neg_zero, add_zero]
  norm_num

end Euclid.BookI.Prop11

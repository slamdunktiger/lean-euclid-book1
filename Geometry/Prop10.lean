/-
  Euclid's Elements, Book I, Proposition 10
  "To cut a given finite straight line in half."

  Given a segment AB, there exists a point M (the midpoint) such that
  |AM| = |MB|. (Each equals |AB| / 2.)

  We construct M = A + (1/2) • (B - A) and verify the distances by norm algebra.

  Author: Warren Wong
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.LinearCombination

open Real

namespace Euclid.BookI.Prop10

/-- Euclid I.10: A given segment can be bisected.

    Given distinct points A, B, there exists a point M such that
    dist A M = dist M B. -/
theorem segment_bisect_exists
    (A B : EuclideanSpace ℝ (Fin 2)) (h : A ≠ B) :
    ∃ M : EuclideanSpace ℝ (Fin 2),
      dist A M = dist M B := by
  -- M = (1/2) • (A + B)  (the midpoint)
  let M := (2⁻¹ : ℝ) • (A + B)
  refine ⟨M, ?_⟩
  -- |AM| = |A - ½(A+B)| = |½(A-B)| = |AB|/2
  -- |MB| = |½(A+B) - B| = |½(A-B)| = |AB|/2
  -- so |AM| = |MB| by identical expression.
  rw [dist_eq_norm, dist_eq_norm]
  -- goal: ‖A - M‖ = ‖M - B‖
  have hL : ‖A - M‖ = (2⁻¹ : ℝ) * ‖A - B‖ := by
    have hLvec : A - M = (2⁻¹ : ℝ) • (A - B) := by
      unfold M
      ext
      simp
      ring
    rw [hLvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  have hR : ‖M - B‖ = (2⁻¹ : ℝ) * ‖A - B‖ := by
    rw [norm_sub_rev]
    have hRvec : B - M = (2⁻¹ : ℝ) • (B - A) := by
      unfold M
      ext
      simp
      ring
    rw [hRvec, norm_smul, norm_sub_rev, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  rw [hL, hR]

end Euclid.BookI.Prop10

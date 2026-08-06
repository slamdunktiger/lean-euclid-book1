import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
  Euclid's Elements, Book I, Proposition 13
  "If a straight line set up on a straight line make angles, it will make
   either two right angles or angles equal to two right angles."

  Given collinear points A, C, B with C between A and B, and any point D,
  the adjacent angles ∠ACD and ∠DCB sum to π (two right angles).

  In ℝ²: the direction vectors (A−C) and (B−C) are antiparallel, so for any
  w = D−C we have angle(w, A−C) + angle(w, B−C) = π, because
  arccos(−x) = π − arccos(x).
-/

open Real

namespace Euclid.BookI.Prop13

/-- The angle between two nonzero vectors, in [0, π]. -/
noncomputable def angleOf (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.arccos (inner ℝ u v / (‖u‖ * ‖v‖))

/-- Adjacent angles on a straight line sum to π. -/
theorem straight_line_angles_sum_pi
    (A B C D : EuclideanSpace ℝ (Fin 2))
    (hAC : A ≠ C) (hBC : B ≠ C) (hDC : D ≠ C)
    (hCollinear : ∃ (t : ℝ), t > 0 ∧ B - C = -t • (A - C)) :
    angleOf (D - C) (A - C) + angleOf (D - C) (B - C) = π := by
  obtain ⟨t, ht_pos, hAnti⟩ := hCollinear
  -- ‖B - C‖ = ‖-t•(A-C)‖ = ‖t•(A-C)‖ = t * ‖A-C‖ (since t > 0)
  have hScale : ‖B - C‖ = t * ‖A - C‖ := by
    rw [hAnti] ; simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht_pos]
  -- inner(w, B-C) = inner(w, -t•(A-C)) = -t * inner(w, A-C)
  have hInNeg : inner ℝ (D - C) (B - C) = -t * inner ℝ (D - C) (A - C) := by
    rw [hAnti, inner_smul_right]
  -- cosine at (D-C, B-C) = -cosine at (D-C, A-C), so the two angles sum to π.
  have hCosB : angleOf (D - C) (A - C) + angleOf (D - C) (B - C) = π := by
    rw [angleOf, angleOf]
    rw [hInNeg, hScale]
    field_simp [hDC, hAC, hBC, ht_pos.ne']
    rw [Real.arccos_neg]
    ring
  exact hCosB

end Euclid.BookI.Prop13

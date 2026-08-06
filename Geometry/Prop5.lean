import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
  Euclid's Elements, Book I, Proposition 5
  "In isosceles triangles the angles at the base are equal to one another."

  Given triangle ABC with |AB| = |AC| (the equal sides meeting at A),
  the base angles at B and C are equal: ∠ABC = ∠ACB.

  Proved directly in ℝ² via the law of cosines (inner products), avoiding
  congruence axioms. The cosines of the two base angles are computed and
  shown equal; both angles lie in [0, π], so arccos is injective.
-/

open Real

namespace Euclid.BookI.Prop5

/-- The angle between two nonzero vectors, in [0, π]. -/
noncomputable def angleOf (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.arccos (inner ℝ u v / (‖u‖ * ‖v‖))

/-- The base angles of an isosceles triangle are equal. -/
theorem base_angles_eq
    (A B C : EuclideanSpace ℝ (Fin 2))
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hIsos : ‖A - B‖ = ‖A - C‖) :
    angleOf (A - B) (C - B) = angleOf (A - C) (B - C) := by
  -- Symmetry of the real inner product via the polarization identity,
  -- which uses only norm_add_sq_real (no inner_comm needed).
  have inner_symm (x y : EuclideanSpace ℝ (Fin 2)) : inner ℝ x y = inner ℝ y x := by
    have h1 : inner ℝ x y = (‖x + y‖ ^ 2 - ‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
      rw [norm_add_sq_real x y] ; ring
    have h2 : inner ℝ y x = (‖y + x‖ ^ 2 - ‖y‖ ^ 2 - ‖x‖ ^ 2) / 2 := by
      rw [norm_add_sq_real y x] ; ring
    rw [h1, h2] ; abel
  -- Expand the two numerators using inner_sub_left/right.
  have h1 : inner ℝ (A - B) (C - B) =
      inner ℝ A C - inner ℝ A B - inner ℝ B C + inner ℝ B B := by
    simp only [inner_sub_left, inner_sub_right] ; ring
  have h2 : inner ℝ (A - C) (B - C) =
      inner ℝ A B - inner ℝ A C - inner ℝ C B + inner ℝ C C := by
    simp only [inner_sub_left, inner_sub_right] ; ring
  -- Flip inner B C = inner C B so h1 and h2 line up.
  rw [inner_symm B C] at h1
  -- From hIsos: ‖A-B‖ = ‖A-C‖ ⇒ ‖A-B‖² = ‖A-C‖².
  have hExp1 : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 - 2 * inner ℝ A B + ‖B‖ ^ 2 := by
    rw [sub_eq_add_neg (A) (B), norm_add_sq_real A (-B)]
    simp only [inner_neg_right, norm_neg] ; ring
  have hExp2 : ‖A - C‖ ^ 2 = ‖A‖ ^ 2 - 2 * inner ℝ A C + ‖C‖ ^ 2 := by
    rw [sub_eq_add_neg (A) (C), norm_add_sq_real A (-C)]
    simp only [inner_neg_right, norm_neg] ; ring
  -- From hIsos: ‖A-B‖² = ‖A-C‖².
  have hSqu : ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 := by rw [hIsos]
  -- Relate ⟨B,B⟩ and ⟨C,C⟩ to the squared side lengths.
  have hExp1' : inner ℝ B B = ‖A - B‖ ^ 2 - ‖A‖ ^ 2 + 2 * inner ℝ A B := by
    rw [hExp1] ; ring ; rw [inner_self_eq_norm_sq_to_K B] ; norm_cast
  have hExp2' : inner ℝ C C = ‖A - C‖ ^ 2 - ‖A‖ ^ 2 + 2 * inner ℝ A C := by
    rw [hExp2] ; ring ; rw [inner_self_eq_norm_sq_to_K C] ; norm_cast
  -- Numerators equal: ⟨A-B, C-B⟩ = ⟨A-C, B-C⟩.
  have hEq : inner ℝ (A - B) (C - B) = inner ℝ (A - C) (B - C) := by
    rw [h1, h2, ← inner_symm B C]
    rw [hExp1', hExp2']
    rw [hSqu] ; ring
  -- Denominators equal (‖A-B‖=‖A-C‖ and ‖C-B‖=‖B-C‖).
  have hDenEq : ‖A - B‖ * ‖C - B‖ = ‖A - C‖ * ‖B - C‖ := by
    rw [hIsos, norm_sub_rev C B]
  unfold angleOf
  rw [hEq, hDenEq]

end Euclid.BookI.Prop5

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
  Euclid's Elements, Book I, Proposition 15
  "If two straight lines cut one another, they make the vertical angles
   equal to one another."

  Given four rays from a point O: OA, OB, OC, OD where OA and OC are
  opposite and OB and OD are opposite, then ∠AOB = ∠COD.

  In ℝ² this follows immediately: the angle between u and v equals the
  angle between -u and -v, since the inner-product sign cancels.
-/

open Real

namespace Euclid.BookI.Prop15

/-- The angle between two nonzero vectors, in [0, π]. -/
noncomputable def angleOf (u v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.arccos (inner ℝ u v / (‖u‖ * ‖v‖))

/-- Vertical angles are equal: angle(u, v) = angle(-u, -v). -/
theorem vertical_angles_eq
    (u v : EuclideanSpace ℝ (Fin 2)) (hu : u ≠ 0) (hv : v ≠ 0) :
    angleOf u v = angleOf (-u) (-v) := by
  unfold angleOf
  simp [inner_neg_left, inner_neg_right, norm_neg]

end Euclid.BookI.Prop15

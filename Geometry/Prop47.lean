import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
  Euclid's Elements, Book I, Proposition 47
  "In right-angled triangles the square on the side subtending the right
   angle is equal to the squares on the sides containing the right angle."

  The Pythagorean theorem. In ℝ²: if two vectors u, v are perpendicular
  (⟨u, v⟩ = 0), then for the hypotenuse h = u + v we have
  ‖h‖² = ‖u‖² + ‖v‖².

  Immediate from the inner-product expansion
  ‖u + v‖² = ‖u‖² + ‖v‖² + 2⟨u, v⟩, since the cross term vanishes.
-/

open Real

namespace Euclid.BookI.Prop47

/-- Pythagorean theorem in ℝ²: for perpendicular legs u, v and hypotenuse u+v,
    ‖u + v‖² = ‖u‖² + ‖v‖². -/
theorem pythagoras
    (u v : EuclideanSpace ℝ (Fin 2)) (hPerp : inner ℝ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  -- ‖u + v‖² = ‖u‖² + ‖v‖² + 2⟨u, v⟩ ; perpendicularity kills the cross term.
  rw [norm_add_sq_real u v, hPerp]
  ring

end Euclid.BookI.Prop47

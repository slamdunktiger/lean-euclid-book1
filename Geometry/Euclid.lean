/-
  Euclid's Elements, Book I — formalization in Lean 4 + mathlib.

  This is a STANDALONE library (depends on mathlib, not part of it). It
  collects machine-checked proofs of the first propositions of Euclid's
  Elements (c. 300 BCE), formalized directly in ℝ² via the law of cosines
  and inner products (`EuclideanSpace ℝ (Fin 2)`), for study and teaching.

  Author: Warren Wong

  Note: several propositions below (I.5, I.13, I.15, I.47) already exist in
  mathlib under `Mathlib/Geometry/Euclidean`. They are re-proven here as a
  self-contained, elementary presentation. This repository is intentionally
  kept separate from mathlib (per the mathlib contribution guidelines, a
  standalone repo is the recommended home for such material).

  ## Status

  | Prop | Content                              | In mathlib? | Here? |
  |------|--------------------------------------|-------------|-------|
  | I.1  | Equilateral triangle construction    | No          | ✅    |
  | I.2  | Copy a segment to a point            | No          | ✅    |
  | I.3  | Cut a shorter segment from a longer  | No          | ✅    |
  | I.4  | SAS congruence                        | Yes         | —     |
  | I.5  | Isosceles base angles equal          | Yes         | ✅ (standalone) |
  | I.6  | Converse of I.5                       | Yes         | —     |
  | I.7  | Uniqueness of triangle (perp)        | No          | ✅    |
  | I.8  | SSS congruence                        | Yes         | —     |
  | I.9  | Angle bisection (existence)          | No          | ✅    |
  | I.10 | Bisect a segment (midpoint)           | No          | ✅    |
  | I.11 | Erect perpendicular from a point      | No          | ✅    |
  | I.13 | Angles on a straight line sum to π    | Yes         | ✅ (standalone) |
  | I.15 | Vertical angles equal                 | Yes         | ✅ (standalone) |
  | I.47 | The Pythagorean theorem (Pythagoras) | Yes         | ✅ (standalone) |

 All proofs verified with `lake build` (ZERO `sorry`).

  ## How to build

  ```
  export PATH="$HOME/.elan/bin:$PATH"
  cd ~/Projects/lean-geometry && lake build
  ```
-/

import Geometry.Basic
import Geometry.Prop2
import Geometry.Prop3
import Geometry.Prop5
import Geometry.Prop7
import Geometry.Prop9
import Geometry.Prop10
import Geometry.Prop11
import Geometry.Prop13
import Geometry.Prop15
import Geometry.Prop47

namespace Geometry.Euclid

/-! ### Book I, Proposition 1
  On a given finite straight line, to construct an equilateral triangle. -/
#check Euclid.BookI.Prop1.equilateral_triangle_exists

/-! ### Book I, Proposition 2
  To place a straight line equal to a given straight line with one end at a given point. -/
#check Euclid.BookI.Prop2.segment_copy

/-! ### Book I, Proposition 3
  Given two unequal straight lines, to cut off from the greater a straight line equal to the less. -/
#check Euclid.BookI.Prop3.cut_segment

/-! ### Book I, Proposition 7
  On the same base and on the same side, two straight lines cannot be constructed
  meeting at a different point while having the same endpoints.
  (Algebraic core: equidistant points are perpendicular to the base.) -/
#check Euclid.BookI.Prop7.equidistant_implies_perp

/-! ### Book I, Proposition 9
  To bisect a given rectilinear angle.
  (Existence of a point D such that the angle ABD equals the angle DBC.) -/
#check Euclid.BookI.Prop9.angle_bisector_exists

/-! ### Book I, Proposition 10
  To bisect a given finite straight line (construct its midpoint). -/
#check Euclid.BookI.Prop10.segment_bisect_exists

/-! ### Book I, Proposition 11
  To draw a straight line at right angles to a given straight line
  from a given point on it (erect a perpendicular). -/
#check Euclid.BookI.Prop11.perpendicular_exists

/-! ### Book I, Proposition 5
  In isosceles triangles the angles at the base are equal to one another. -/
#check Euclid.BookI.Prop5.base_angles_eq

/-! ### Book I, Proposition 13
  If a straight line set up on a straight line makes angles, it makes either
  two right angles or angles equal to two right angles. -/
#check Euclid.BookI.Prop13.straight_line_angles_sum_pi

/-! ### Book I, Proposition 15
  If two straight lines cut one another, they make the vertical angles equal. -/
#check Euclid.BookI.Prop15.vertical_angles_eq

/-! ### Book I, Proposition 47
  In right-angled triangles the square on the side subtending the right angle
  is equal to the squares on the sides containing the right angle. -/
#check Euclid.BookI.Prop47.pythagoras

end Geometry.Euclid

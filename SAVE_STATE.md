# Euclid Formalization — SAVE STATE (local only, nothing pushed)

Last updated: 2026-08-05 (Warren sleeping, laptop crunching)

## HARD RULE
- Do NOT push to mathlib4 until PR #42465 (props I.1–I.10) MERGES.
- Everything below is local work on branch `euclid-book1` (tracks `mathlib4/euclid-book1`).
- If network dies: this file is the recovery point. Nothing is lost — all files are on disk.

## VERIFIED GREEN (real `lake build` exit 0)
- Full project: 2393 jobs, exit 0, ZERO sorry.
- Props proven: I.1, I.2, I.3, I.7, I.9, I.10.
- PR #42465: OPEN, MERGEABLE, head 21c5b6f (Prop 10 committed + pushed).
  URL: https://github.com/leanprover-community/mathlib4/pull/42465
  CI: running (build ~1-3hr mathlib). One `ensure-sha-pinned-actions` fail is CI hygiene, not code.

## I.11 — perpendicular from point on line (LOCAL ONLY, not committed)
File: Geometry/Prop11.lean
- `perpendicular_exists (A B C) (hAB : A ≠ B) : ∃ P, inner ℝ (P-C) (B-A) = 0`
- Construction: P = C + rot90(B-A), rot90(x,y)=(-y,x).
- Proof reduces to inner ℝ (rot90 u) u = 0, goal now:
    inner ℝ (rot90 u).ofLp 0 (u.ofLp 0) + inner ℝ (rot90 u).ofLp 1 (u.ofLp 1) = 0
  i.e. (-u₁)·u₀ + u₀·u₁ = 0.
- BLOCKER: `Real.inner_apply` (inner ℝ x y = x*y) won't rewrite these scalar inner terms.
  Bilinearity (inner_sub_left/inner_add_left), add_comm+add_sub_cancel_right,
  PiLp.inner_apply + Fin.sum_univ_two + Matrix.cons_val_zero/one all WORK.
  FIX TO TRY: use `real_inner` lemmas (like Prop9 did) OR `simp [Real.inner_apply]`
  with the InnerProductSpace ℝ ℝ instance in scope. Possibly need
  `rw [← real_inner_eq_inner]` first, or the scalar inner is `real_inner` not `inner ℝ`.

## NEXT TARGETS (after I.11 + after #42465 merges)
- I.12: perpendicular from point OFF the line
- I.23: copy an angle at a point
- I.31: parallel through a point
All construction props, not in mathlib, same EuclideanSpace ℝ (Fin 2) toolkit.

## ENV
- elan 4.2.3, Lean 4.33.0-rc2, mathlib current, LeanCopilot models in ~/.cache/lean_copilot/
- Build: `export PATH="$HOME/.elan/bin:$PATH"; cd ~/Projects/lean-geometry && lake build`
- Remotes: mathlib4 (fork/PR), origin (dead standalone), upstream (leanprover-community)
- Push to mathlib4 ONLY after #42465 merges: `git push mathlib4 euclid-book1`

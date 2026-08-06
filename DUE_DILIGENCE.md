# DUE-DILIGENCE RULE (global, all projects) — time > tokens
# Installed 2026-08-06 after the Euclid/mathlib redundant-PR token-burn.

Before building / formalizing / contributing ANYTHING, verify it does not
already exist and is actually in scope. Concrete gates:

1. LIB/CODE CONTRIB: grep the target codebase / upstream for the symbol,
   theorem, or function BEFORE writing it.
     git ls-tree -r <upstream>/master | grep -i <topic>
     # or: git grep <name> upstream/master -- 'Mathlib/**/*.lean'
   If it already exists -> DO NOT re-implement. State that, propose the GAP.

2. UPSTREAM PR: confirm the work is NOT redundant AND structurally valid
   (correct lakefile / dependency direction — never make a lib depend on
   itself) BEFORE opening the PR.

3. SCOPING: name the deliverable + its consumer up front
   (personal study repo / mathlib target / signed open-source donation)
   so effort is not misdirected.

4. TOKEN-BURN GUARD: if >3 tactic/iteration attempts fail on the SAME
   sub-step, STOP and re-derive the approach (scratch `#check`, read the
   ACTUAL error, verify lemma names) instead of guessing lemma names.

Warren has free tokens but finite time. Optimize for cycles saved, not
calls made. This rule applies to EVERY project, not just lean-geometry.

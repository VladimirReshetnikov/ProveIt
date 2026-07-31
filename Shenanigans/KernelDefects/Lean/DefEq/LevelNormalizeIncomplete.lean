/-
UNIVERSE-LEVEL NORMALIZATION IS INCOMPLETE — `imax` that collapses to `max`.

`Level.normalize` does not produce a canonical form when an `imax` simplifies to
a `max`: outer `succ`s are not distributed into the `max` arguments, and the C++
kernel does not re-sort/flatten the result.  `Level.isEquiv` and the kernel's
`is_equivalent` therefore answer `false` for denotationally equal levels.

This is an INCOMPLETENESS, not unsoundness: the kernel rejects statements that
are true.  Nothing here proves `False`, and nothing here is harmful — it is
recorded because a complete catalog of kernel defects includes the ones that
cost expressiveness rather than soundness, and because an independent Lean
kernel (`lean4lean`) had a *soundness* hole in this same area
(lean-kernel-arena PR #17).

Upstream: lean4#12747 (OPEN, P-low, filed 2026-03-01, found by Opus 4.6).

The two levels below are equal under every valuation:
  imax u (imax v w)  vs  imax v (imax u w)
    * if w = 0, both inner imax are 0, so both outer imax are 0;
    * if w > 0, both reduce to max u (max v w) = max v (max u w).

Verified rejected with `elan run leanprover/lean4:<v> lean --trust=0` on this
file (exit 1, "Type mismatch ... Sort (imax u v w) ... Sort (imax v u w)"):
`v4.32.0`, `v4.32.2`, `v4.33.0-rc1`.

CONTROL: the same declaration with the levels written in the order the
elaborator itself produces is accepted, showing that the term is fine and only
the level comparison fails.

Related: `../../../Audits/Lean/Fuzz/LevelFuzzer.lean` samples 880 random levels over 774,400 pairs
and reports 0 unsound / 162 incompleteness cases.  Those 162 are very likely
instances of this defect; confirming that case-by-case is open work
(see ../../../CATALOG.md section 5).
-/

-- CONTROL: accepted — this is the level the elaborator infers for `A → B → C`.
example (A : Sort u) (B : Sort v) (C : Sort w) : Sort (imax u (imax v w)) := A → B → C

-- THE DEFECT: denotationally the same level, rejected.
-- Uncomment to observe the failure (kept commented so the file itself compiles):
-- example (A : Sort u) (B : Sort v) (C : Sort w) : Sort (imax v (imax u w)) := A → B → C

/-
Observed on all three toolchains for the commented line:

  error: Type mismatch
    A → B → C
  has type
    Sort (imax u v w)
  of sort `Type (imax u v w)` but is expected to have type
    Sort (imax v u w)
  of sort `Type (imax v u w)`
-/

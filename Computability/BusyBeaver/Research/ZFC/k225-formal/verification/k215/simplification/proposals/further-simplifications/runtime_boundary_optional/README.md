# Optional boundary-only return shortcut

This narrow addendum leaves the frozen `runtime_contexts` primary artifacts unchanged. It reuses the same already-required `Boundary` lemma:

    zl 2 [] (true :: R)  →  zc 84 [true] R

for arbitrary right frame R, in exactly 18 physical transitions. An arbitrary all-blank left list is equivalent to the empty left list by `zl_padl`, so the symbolic guard permits only false bits/runs on the left, including runs of arbitrary natural-dependent length. The right head must be a literal true, and the state/orientation must be exactly q2/on-left. The remaining right frame is untouched.

The two previously conservative rejections both satisfy this guard:
- `11011`, brk 1, no branch assumption.
- `1111110`, decnz-zero, physical register 8.

For each, the old symbolic engine takes 27 dispatches, not 18: its left moves include orientation/bookkeeping operations. Replacing each block by one macro saves 26 dispatches, hence **52 additional dispatches**, rather than the initially guessed 34.

Actual macro-output-resuming replay of all 6,176 branch runs passes:
- 910,624 ordinary symbolic steps.
- 15,673 main home macros and 2 boundary macros.
- **926,299 total dispatches**, versus 926,351 for the frozen primary shortcut and 2,442,801 for the original executor.
- Total reduction: 1,516,502 dispatches, or 62.0805%.

The independent absolute-coordinate checker verifies complete finite-support tape equality and the exact 18-step clock on 2,555 exhaustive right-word/padding cases plus 60 symbolic-padding instantiations. Five invalid guards are rejected. These remain ordinary executable checks, not kernel proof or performance measurements.

No additional mathematical theorem is needed beyond the Boundary lemma already explicit in `HomeReturn.uncompiled.lean`; the small symbolic bridge uses the same blank-padding equality. This addendum does not claim that Boundary has been compiled or that the two macro families' checker implementation is already integrated into Lean.

Replay from anywhere, keeping this directory beside `runtime_contexts`:

    python -I -B runtime_boundary_optional/check_boundary_optional.py

Owned entry point: `check_boundary_optional.py`. It imports only the owned sibling helpers `symbolic_owned.py`, `profile_home.py`, and `verify_home.py`; no incoming executable is imported. The primary helper checks the exact bundled source/data hashes. Optimized Python is rejected. Output: `boundary_optional_result.json`.

# Independent review: optional boundary-only shortcut

**Verdict:** mathematically valid as a narrow application of the existing boundary obligation. Suitable to include as a separately labeled addendum. No frozen primary artifact was changed; no Lean theorem was compiled.

## Guard and semantic contract

The guard accepts only state 2, left-facing orientation, a left list consisting solely of false bits or false runs, and a literal true bit as the right list's first segment. In the intended Lean segment type the run coefficient and constant are naturals. Consequently, for every natural gap parameter and every register list, the entire left list denotes finite blank padding and the right marker definitely exists. Boxes on the left, a nonblank left segment, a nonliteral or false right head, the wrong state, and the wrong orientation are rejected.

For every right frame R, blank-padding equality reduces the accepted input to

    zl 2 [] (true :: R).

The already-required Boundary premise gives

    zc 84 [true] R.

This is exactly the implementation's output: remove the literal right-head marker from the old right list, put it in the singleton left list, and face right at state 84. The right continuation, including any opaque register box, is untouched. No source-path, branch, register-validity, or stronger scanner-word hypothesis is added or weakened. The symbolic guard bridge must still be implemented/proved when integrating into Lean, but requires only the existing blank-padding identity and Boundary obligation.

Boundary in `HomeReturn.uncompiled.lean` asserts positive reachability, not an exact clock. For the fixed 18 checked table rows, the separate ordinary argument gives exactly 18 physical steps: eight leftward zeros, nine rightward zeros, then the marker step. With the old right-head marker at absolute coordinate 0, the initial head is -1 and the final head is +1; all tape cells are unchanged.

## Evidence review

The optional entry point was inspected, including its actual macro-output-resuming runner. Its recorded counts reconcile exactly:

- 6,176 completed branch runs.
- 15,673 original home macros and 2 boundary macros.
- 910,624 ordinary symbolic dispatches.
- 926,299 total enhanced dispatches.
- Each new block replaces 27 old abstract dispatches with one, saving 26 each and 52 total relative to 926,351.

The old engine's 27 abstract dispatches are not the 18 physical transitions. Total abstract reduction from the original 2,442,801 is 1,516,502 (62.080456%). This is not elapsed-time, kernel-reduction, or concrete-machine-runtime improvement.

The supplied finite receipt records 2,555 complete-tape cases, 60 affine-padding cases, and five negative guards. In addition, this reviewer independently parsed only the literal table and executed an absolute-coordinate interpreter on all 1,023 binary right continuations of lengths 0 through 9. Each preserved the entire finite tape, first reached state 84 exactly at step 18, and matched the translated output tape and head. This independent test did not use the optional macro or sibling symbolic interpreter.

The full 6,176-case replay was source-audited and its receipt checked here, not independently rerun a second time by this reviewer. A release replay should execute the owned optional entry point as already planned. It imports only the three named owned sibling helpers; their incoming source inputs are read as data, not executed. Its natural-segment invariant should remain explicit if a future implementation accepts untrusted serialized segments.

Reviewed source SHA-256:

    e9f170540f8c0fd8034fc576ac2b2ea4435eeda4337d7ff47281050ce396d374

Reviewed `boundary_optional_result.json` SHA-256:

    0c92478093b4c96f8bbdde5414de788be7045829bd8a7969c374e6d7e3d5162c

This addendum establishes no new kernel checking, completed Boundary proof, or production integration.

# Independent ordinary review: synchronized signed projections

**Accepted.** I read `PROOF.md`, the complete independent checker and its
authenticated `verify_projection.py` replayer, then replayed the checker
in normal and optimized Python. No candidate source was changed and no
Lean process was run.

For a current row `v-f(z)=0` or its negative, monicity and independence
of v give a unique integral restoration `v=f(z)`. Negative coefficients
of f are allowed because the projection domain is the unrestricted
integers. The replayer substitutes into every other row and checks all
resulting residual degrees. It drops a row only when substitution makes
it identically zero. These identities prove both directions for all
integer assignments, independently of finite controls or the optimizer's
heuristic choice.

The reverse order of restorations is correct: each saved polynomial uses
only coordinates alive at that step, excluding itself. All later-deleted
coordinates have already been recovered when that step is reversed.
Every run requires `unconstrained_removed=[]`, so the projection really
is a bijection between the child and full integer-parent zero sets.
Without that condition only existence equivalence would be justified.

Most importantly, the original seed guards are not omitted by a special
path. They undergo the same substitution as every row; a deleted guard
must either be an exact zero identity or an actual monic defining row
whose truth follows by restoration. The signed child need not satisfy
the parent's sign assertions coordinatewise before restoration. Restore
the full integer parent first, then its actual guard equations prove
the seed signs, and the ordered nonnegative-RHS row certificate proves
all original natural coordinates nonnegative. This closes the sign chain
without assuming a negative-coefficient restoring polynomial preserves
natural numbers.

The independent checks authenticate the frozen parent packets, replay all
row substitutions, retain every sign guard algebraically, reconstruct all
seven complete SOS polynomials and their exact quartic coefficients, and
test three signed off-source restorations against every original row.
Both normal and optimized replays passed, including 14 corrupted
certificate/row rejections. The fewest-variable point is **1,190
unrestricted integers, degree four, 600 rows, 26,411 terms, height
83,900,628**. The additional materialized points retain their stated
term/height tradeoffs.

The ordinary source/refutation calibration is unchanged. This accepts
the exact integral transformation, not a proof of no zeros, consistency,
global minimality, a new Lean theorem or an encoded object-ZFC derivation.

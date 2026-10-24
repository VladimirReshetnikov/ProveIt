# Attribution and scope

This is an AI-assisted mathematical research contribution prepared for
Vladimir Reshetnikov's ProveIt repository. Newly written proofs, builders,
audit scripts, and report text are provided under the included MIT No
Attribution license for incorporation in the repository.

The comparison snapshot is
`cf4a5218a5a4e4358d3f5314151b6b05d4aa384e` of
<https://github.com/VladimirReshetnikov/ProveIt>.

The integer construction adapts packages 64, 68, 70 and 71. The fixed
native tuple and its finite builder come from package 34; the signed Pell
and strong-rank interfaces, source compiler and K215 calibration remain
inherited mathematical inputs. `integer/polynomial.py` is adapted from
package 71's exact sparse-polynomial engine, with a performance correction
that avoids the unused final squaring in binary exponentiation.

The determinant sign guard is credited to package 71, affine residue
orientation to package 70, and the shared nearest-square positivity lemma
to package 68. The new CRT application, compatible combination, exact
transport elimination, retained-rank choice, and resulting literal
equations are explained in the report. No priority claim is made for CRT,
Pell identities, sums of squares, or other standard ingredients.

See `positive/NOTICE.md` and `nine_full_radical/NOTICE.md` for the companion
constructions and their inherited packages. Existing MIT/MIT-0 licenses,
Andrew James Wade's license, and the K215 and normalized-source notices
are preserved in the relevant component directories and `licenses/`.

No prior theorem-prover receipt is presented as a certificate for these
new equations. Independent audits here are internal checks by separate
reasoning/code paths; they are not external peer review.

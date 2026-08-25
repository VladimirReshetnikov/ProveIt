import FabiusFunction.ThueMorseApproximation
import FabiusFunction.ThueMorseExponential
import FabiusFunction.ThueMorseBinomialLog
import FabiusFunction.DraftCounterexamples
import FabiusFunction.StirlingAsymptotics
import FabiusFunction.LowerLambertW
import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusFlatness
import FabiusFunction.FabiusDecayComparison

set_option autoImplicit false

/-!
# Claim-level audit of the local K-fold Thue--Morse draft

The TeX source in
`Papers/K-fold summation over the signed Thue-Morse sequence/` contains no
`theorem`, `lemma`, `proposition`, or `corollary` environments.  This public
aggregate tracks its numbered equations and substantive prose claims.

The Thue--Morse identities, sharp affine Prouhet formula, iterated-prefix
convolution, exact zero runs, ordinary and exponential formal generating
series, and a corrected pointwise approximation theorem are proved.  The
aggregate also exposes the zero-one Thue--Morse sequence and the exact
binomial-parity/`Log2` formula for it.  The literal normalization
printed in equation (1), its local
and global error claims, the maximum in equation (7), and the missing linear
term in the equation-(10) proxy are refuted by machine-checked theorems.

After making the draft's integer-to-real switch and omitted branch domain
explicit, the lower Lambert-W branch, its equation-(9) solution, and its
standard two-term expansion are proved.  They do not repair the preceding
false maximum or the equation-(10) proxy.  The rigorous Fabius asymptotic
headline is the coarse `O(t * log t)` log-squared estimate.  The
two qualitative comparisons—faster decay than every power and slower decay
than `exp (-c/x)` for `c > 0`—are also proved precisely.  See
`PAPER_COVERAGE.md` for the exact claim matrix.
-/

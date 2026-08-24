import FabiusFunction.ThueMorseApproximation
import FabiusFunction.DraftCounterexamples
import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusFlatness
import FabiusFunction.FabiusDecayComparison

/-!
# Claim-level audit of the local K-fold Thue--Morse draft

The TeX source in
`Papers/K-fold summation over the signed Thue-Morse sequence/` contains no
`theorem`, `lemma`, `proposition`, or `corollary` environments.  This public
aggregate tracks its numbered equations and substantive prose claims.

The Thue--Morse identities, iterated-prefix convolution, exact zero runs,
formal generating series, and a corrected pointwise approximation theorem
are proved.  The literal normalization printed in equation (1), its local
and global error claims, the maximum in equation (7), and the missing linear
term in the equation-(10) proxy are refuted by machine-checked theorems.

The Lambert-W heuristic is not advertised as formalized: the draft silently
changes an integer index to a real optimization variable and the project has
not introduced a Lambert-W branch.  The proved asymptotic headline is the
coarse `O(t * log t)` log-squared estimate, not the invalid proxy chain.  The
two qualitative comparisons—faster decay than every power and slower decay
than `exp (-c/x)` for `c > 0`—are also proved precisely.  See
`PAPER_COVERAGE.md` for the exact claim matrix.
-/

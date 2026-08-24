import FabiusFunction.FabiusLogScale
import FabiusFunction.FabiusLogMainDefect
import FabiusFunction.FabiusDyadicLogBounds
import FabiusFunction.FabiusLogSquaredAsymptotic
import FabiusFunction.FabiusFlatness
import FabiusFunction.FabiusSharpAsymptotic
import FabiusFunction.FabiusRecurrenceSequence

/-!
# Claim-level audit of the local *Fabius Asymptotic* draft

The TeX source in `Papers/Fabius Asymptotic/` contains no `theorem`, `lemma`,
`proposition`, or `corollary` environments.  This public aggregate therefore
tracks its numbered equations and substantive prose claims rather than a list
of formally named source results.

The exact logarithmic delay identity, the elementary logarithm expansions,
and the coarse log-squared asymptotic are proved.  The explicit sharp main
term proposed by the draft is also substituted into the delay equation and
its residual is determined: it has a nonzero multiple of
`(log t / t)^2` as its leading term.  In particular, the draft's later
replacement of this residual by `O(t^-2)` is formally disproved.

No theorem in this development asserts the draft's unsupported periodic-in-`t`
remainder or derives a sharp expansion from that invalid argument.  A separate
Laplace-product, Mellin, and quantitative saddle analysis does prove the
correct sharp formula: its genuine nonconstant periodic correction is sampled
at the lower-Lambert phase, and the literal elementary expression printed in
the linked Math Stack Exchange discussion is proved to be missing that term.
The related Mathematica Stack Exchange quotient is also proved not to be an
endpoint asymptotic equivalent.  See `PAPER_COVERAGE.md` for the exact claim
matrix.
-/

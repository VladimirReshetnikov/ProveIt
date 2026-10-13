# Separate review of the gap-contraction patch, 12 October 2026

Intake preserved the package without testing. This later goal review checks
only `integration/orbit-contraction.patch`; the other three patches and
finite exceptional-row algorithms are not validated by this record.

The patch applies cleanly to an isolated copy of its pinned baseline,
`c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`. All six delivered gap-prefix tests
pass in 0.106 seconds. At that review checkpoint the four target runtime modules matched that
baseline byte for byte. Native integration followed in a separate change.

The proposed verifier helper replaces repeated sums over every static gap
at each pairing endpoint with one prefix table and binary searches. It
uses the already authenticated, increasing, disjoint inclusive gaps and
the fact that pairing endpoints lie outside them. The three verifier
callers remain independent of the producer. This reduces the endpoint
mapping stage from O(PG) to O(G + P log(G+2)) arithmetic operations, where
P counts pairing rows and G gaps. The producer patch separately streamlines
its occupied-interval scan. Neither stage bounds total orbit-trace length.

Native integration should preserve every old certificate, explicitly test
malformed-gap rejection before the helper is reached, compare exact bit
and weighted-transversal behavior, and measure complete queries and replay.
The isolated test result is not a whole-native-suite or performance claim.
See `synthesis/data/deferred-forest-report106-gap-*` for this review's
source pins and test log. The originals remain unchanged.

## Native gap-prefix integration

The maintained four runtime modules now use the gap patch. Eight focused
tests pass, including two added native tests for hostile nested weighted
proofs and weighted original-label replay with 16,384-bit endpoints. The
independent checker helper is used only after exact gap authentication.
Old certificate formats and the inverse representative map are unchanged.
The detailed proof and evolving validation record are in
`synthesis/gap_prefix_replay.tex` and `synthesis/data/gap-prefix-*`.
Four retained baseline modules support separate-interpreter paired complete
queries and corpus certificate comparisons. The complete 120-source audit preserves all 111 positive certificates and
nine inconclusive outcomes. Eleven paired complete-query measurements are
recorded, including tiny-input regressions. All 1,737 maintained methods
are covered across the broad run (1,723 passes, one missing-Regina error,
thirteen dependency skips) and the exact fourteen-method Regina 7.4 rerun,
which passes without skips. Both logs are retained; this is not a clean
single-run claim.
The original delivered package files remain unchanged.

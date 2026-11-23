# Almost-everywhere globe flattening

This project contains the delivered report
[Flattening a Sphere Almost Everywhere](globe_flattening_verification.pdf)
and its [LaTeX source](globe_flattening_verification.tex). It concerns a
homeomorphism from a cut sphere to a planar domain whose classical
differential is an isometry almost everywhere. The report's claims are
presented as delivered and have not been independently verified here.

The Lean development begins with the single-interval refinement, the eventual
good set, the classical derivative of the limit under the tile estimates, and
the inverse derivative on that set. The global refinement and its estimates,
and the spherical theorem and area conclusions, still need to be assembled.
Build the current Lean modules from the repository root with
`lake build GlobeFlattening`.

The delivered [README](README.txt),
[original claim](original_claim.md), and figures are retained alongside the
report. The incoming archive was recorded in commit `e270ff954f`.

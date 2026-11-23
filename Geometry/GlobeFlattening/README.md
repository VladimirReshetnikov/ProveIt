# Almost-everywhere globe flattening

This project contains the delivered report
[Flattening a Sphere Almost Everywhere](globe_flattening_verification.pdf)
and its [LaTeX source](globe_flattening_verification.tex). It concerns a
homeomorphism from a cut sphere to a planar domain whose classical
differential is an isometry almost everywhere. The report's claims are
presented as delivered and have not been independently verified here.

The Lean development proves the rectangular refinement estimates, including
the local error inside an old affine tile and the bound on the area discarded
by trimming. The scalar limit theorem gives a classical derivative on a
measurable co-null set once a sequence of these refinements is supplied.
The choice and iteration of the spherical meshes and the final spherical
theorem remain to be assembled.
Build the current Lean modules from the repository root with
`lake build GlobeFlattening`.

The delivered [README](README.txt),
[original claim](original_claim.md), and figures are retained alongside the
report. The incoming archive was recorded in commit `e270ff954f`.

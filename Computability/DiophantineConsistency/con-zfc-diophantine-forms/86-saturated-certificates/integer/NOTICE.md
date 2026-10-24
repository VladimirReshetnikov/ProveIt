# Attribution and scope

This AI-assisted research contribution was prepared for Vladimir Reshetnikov's
ProveIt project on 23 October 2026. New reductions and their proofs are in
`PROOF.md` and `section.tex`; the complete literal equations and executable
finite checks are supplied alongside them.

Inherited contributions include the source34 native coefficient recipe and
K215 encoding, source64 signed arithmetic, source70 residue orientation,
source71 calibrated determinant, source68 joint positivity, source69 rational
Pell descent, and the incoming paired-root translations and transport pivot.
The repository already exposes the strong-quotient identity; the new step
uses it to delete a coordinate from the completed signed consistency equation.
The new rational-norm composition and its polynomial majorant are separately
proved. The positive unit-product finalizer is elementary integer arithmetic.

`polynomial.py` is derived from source71's small exact sparse ring engine.
Its only modification skips constructing an unused final square in binary
exponentiation. Its byte-exact original is retained under `upstream/`.

New text and code are offered under MIT No Attribution terms. This does not
relicense inherited third-party contributions: preserve the original notices
and licenses under `licenses/`, including the Wade and K215 lineage notices.
Complete source and incoming-archive hashes are in `SOURCE_PINS.json`.

Independent review means separate work inside the AI collaboration; it is not
external human peer review. Finite algebra/data verification is not an
end-to-end proof-assistant or encoded internal-ZFC certificate. No global
optimality, external historical priority, or consistency decision is asserted.

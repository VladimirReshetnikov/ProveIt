# Exact Rvachev up-function polynomial synthesis

This directory is the canonical representation volume for exact polynomial
synthesis, Lagrange cardinal loops, Legendre spectral closure, operator
transmutation, and finite self-reconstruction by Rvachev up-atoms.

The report consolidates thirteen earlier packages:

- three exact-polynomial synthesis packages already absorbed into the original
  volume;
- six Lagrange--Rvachev reports;
- four Legendre--Rvachev reports.

Repeated background and equivalent matrix notations are stated once. Distinct
theorems are grouped by mathematical dependency, every theorem-like
environment has a proof, conjectures are explicitly labeled, and vague
normalization claims have been demoted to problems.

## Canonical artifacts

- Up_Polynomial_Synthesis.tex — report driver.
- chapters/Lagrange_Cardinal_Loops.tex — exact cardinal synthesis, right
  inverses, projectors, ghosts, nested details, conditioning, q-binomial rows,
  Appell--Vandermonde growth, and denominator support.
- chapters/Legendre_Spectral_Closure.tex — literal mode synthesis, blockwise
  self-reconstruction, energy, translated analysis, biorthogonality, reverse
  closure, Gram frames, refinement, and flatness.
- chapters/Legendre_Transmutation_Arithmetic.tex — pullback geometries,
  conjugated operators, Gauss/Christoffel--Darboux synthesis, smoothed
  Legendre--Appell connections, parity, central q-determinants, asymptotics,
  exact Sturm evidence, and consolidated conjectures.
- Up_Polynomial_Synthesis.pdf — rendered report.
- assets/provenance/THEOREM_CROSSWALK.md — one-to-one provenance and evidence
  ledger for all 80 theorem-like assertions.
- assets/provenance/ — source snapshots, migration map, and asset policy.
- assets/evidence/legendre/root-geometry/ — exact Q12 Sturm certificate,
  complete counts through degree twenty, and a focused verifier.

## Notation contract

- Q_n^- = M_u(D)^(-1) P_n is the deconvolved Legendre family used for
  synthesis samples.
- R_n = M_u(D) P_n is the distinct moment-smoothed Legendre family.
- A_n = M_u(D)^(-1) x^n is the Rvachev--Appell family.
- X_- = x - K'(D) and X_+ = x + K'(D), with K = log M_u.
- a_n is the coefficient of P_(2n) in the even Fourier--Legendre expansion of
  u.

These names are deliberately not interchangeable.

## Build and verification

From this directory, run three direct passes:

    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex
    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex
    pdflatex -interaction=nonstopmode -halt-on-error Up_Polynomial_Synthesis.tex

Then inspect the log for undefined references, missing files, overfull boxes,
and font substitution. Render all pages to images and inspect the full contact
sheet plus representative pages at original resolution. The committed PDF
must be A4, have embedded/subset fonts, and contain no Type 3 fonts.

The focused exact Sturm verifier requires SymPy:

    python assets/evidence/legendre/root-geometry/verify_sturm.py

Lean is verified separately from the repository root with one serialized
umbrella build:

    LEAN_NUM_THREADS=0 LAKE_JOBS=1 lake build +FabiusFunction

On PowerShell, set the two environment variables before invoking Lake.

## Evidence discipline

Human-readable proof, exact symbolic certificate, focused Lean build,
repository-wide Lean build, and remote CI are distinct evidence levels. This
package does not equate them.

Several analytical and finite-dimensional results in the new Lagrange and
Legendre chapters remain human proofs backed by exact scripts rather than Lean
theorems. The report says so explicitly. Existing compiled Lean declarations
are named where they discharge a claim; no source-only statement is presented
as kernel verified.

The Q12 root transition is exact computer-assisted mathematics: rational
polynomials and rational Sturm chains decide root counts. Approximate complex
root locations are diagnostics only.

## Asset and retirement policy

No two companion files among the ten later reports are byte-identical, even
after line-ending normalization. Similar filenames often use different ranges,
normalizations, or operators. Therefore report prose may be deduplicated, but
scripts and data are not discarded merely because their names look similar.

Historical checksum ledgers are provenance. They are preserved without
rewriting old hashes to fit new paths. A future live SHA256SUMS must hash the
canonical Git-tree bytes and must not target removed arrival files.

The ten source directories are intentionally retained until all 113 selected
payloads have canonical destinations and live hashes, every theorem label has
an auditable crosswalk, the PDF and exact verifier are green, and a fresh
checkout validates the new live ledger. The exact removal gate is documented
in assets/provenance/ASSET_INVENTORY.md.

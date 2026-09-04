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

- Up_Polynomial_Synthesis.tex — 2,324-line, 95,757-byte report driver;
  SHA-256
  `15f7c593895ed4a06b7f9d90c72d55078a193cd01f0818cb3b3cfa4f4d585a52`.
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
- The driver plus its three chapter sources total 5,279 lines and 202,019
  bytes.
- Up_Polynomial_Synthesis.pdf — synchronized 60-page, 1,056,613-byte report;
  SHA-256
  `0b7fc962bcb4509affc322571100cc4f27252b1ec113ca8116b05c59d23ffd35`.
- assets/provenance/THEOREM_CROSSWALK.md — one-to-one provenance and evidence
  ledger for all 80 theorem-like assertions.
- assets/provenance/ — source snapshots, migration map, and asset policy.
- assets/provenance/COMPANION_PAYLOADS.csv — one-to-one old-to-new map for all
  113 selected companion payloads.
- assets/companion-evidence/ — 104 migrated scripts, exact tables, captured
  outputs, requirements, and useful PNG diagnostics, grouped by source slug;
  the provenance map also covers two already-canonical root-geometry files and
  seven retired checksum-ledger rows without live destinations.
- assets/evidence/legendre/root-geometry/ — exact Q12 Sturm certificate,
  complete counts through degree twenty, and a focused verifier.
- Package checksum manifests are retired; scoped hashes remain in the
  provenance CSVs and historical artifact receipts.

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

The current publication was rebuilt from absent auxiliaries on 2026-09-04 by
the exact procedure above. The three successful halt-on-error passes produced
59 pages/1,030,964 bytes, 60 pages/1,056,607 bytes, and finally 60
pages/1,056,613 bytes. The final log has no TeX error, unresolved reference or
citation, or rerun request; title, author, subject, and keywords metadata are
present. Every page is A4 at rotation zero, rendered, and contains extractable
text. All 27 font rows are embedded and subset, four are Libertinus, and none
is Type 3. Representative title, chapter-opening, theorem, table, figure, and
final pages passed visual inspection. Generated sidecars were removed, and no
package-local checksum ledger is a live publication gate.

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

## Asset and retirement record

No two companion files among the ten later reports were byte-identical, even
after line-ending normalization. Similar filenames often use different ranges,
normalizations, or operators. The report prose and PDFs were therefore retired
after consolidation. Of 113 disposition rows, 106 retained evidence payloads
received canonical destinations; seven checksum-ledger rows were retired.

Historical checksum ledgers are provenance recoverable from Git history; they
are not retained or rewritten to fit new paths. Canonical Git-tree bytes are
tracked directly rather than through live package-local ledgers.

The ten source directories were retired on 31 August 2026 after 106 retained
payloads received canonical destinations, seven checksum-ledger rows were
retired, every theorem label received an auditable crosswalk, the PDF and exact
verifier passed, and a fresh checkout validated the then-recorded root checkpoint. Their exact
pre-retirement bytes
remain recoverable at commit
`443793e846934e7363e314ea01129b9f50197a58`; the completed gate is documented
in `assets/provenance/ASSET_INVENTORY.md`.

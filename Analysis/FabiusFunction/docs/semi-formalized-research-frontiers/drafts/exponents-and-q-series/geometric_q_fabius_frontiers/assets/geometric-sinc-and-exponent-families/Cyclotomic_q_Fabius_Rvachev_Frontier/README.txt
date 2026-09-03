> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part IX** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

Cyclotomic q-Fabius--Rvachev Frontier Report
============================================

Contents
--------
- cyclotomic_q_fabius_frontier.tex : LaTeX manuscript
- cyclotomic_q_fabius_frontier.pdf : compiled PDF
- numerical_experiments.py        : deterministic high-precision experiments
- data/                            : CSV output and generated LaTeX table
- figures/                         : PDF and PNG figures
- corpus_audit_note.txt            : source-audit method and novelty boundary
- corpus_inventory_2026-08-27.txt : preserved recursive 57-TeX-path ledger
- requirements.txt                 : Python dependencies

Reproduce numerical results
---------------------------
From this directory, run:

    python numerical_experiments.py --dps 80

The script writes all CSV tables, summary text, and figures in place.  It uses
mpmath's arbitrary-precision arithmetic and Matplotlib.  No random sampling is
used.

Build the report
----------------
With a standard TeX installation, run three strict serial passes:

    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error cyclotomic_q_fabius_frontier.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error cyclotomic_q_fabius_frontier.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error cyclotomic_q_fabius_frontier.tex

The source expects figures/ and data/ to remain beside it.

Current publication artifact
----------------------------
The 31 August 2026 rebuild matches the current 1,873-line source and is a
705,892-byte, 28-page A4 PDF with extractable text and no encryption.  All 31
font rows are embedded and subset; four are Libertinus rows and nine are
Type-3 rows inherited from the four included Matplotlib vector figures.  The
standalone figure PDFs contain the same nine Type-3 rows, so figure-font
normalization remains outstanding.  The active 22-entry checksum ledger
verifies the current package in full.

Result status and inventory
---------------------------

Lean-verified
- The global spectral q-Pochhammer factorization is machine-checked as
  `Fabius.geometricSincProduct_eq_tprod_complexQPochhammerInf`; the dyadic
  Rvachev factorization is its direct specialization.  The report records the
  exact normalization relating Phi(q,z) to Lean's geometric sinc product.

Manuscript-proved, not yet formalized in Lean
- Holomorphy and normalization, the master logarithm, the uniform two-term
  radial root-of-unity expansion, spectral-dilogarithm and cyclic descriptions
  of the action, the action sign theorem, and the resulting natural boundary
  for every fixed real 0<|z|<pi/2.
- The shrinking-frequency cyclotomic blow-up, its finite and all-order
  correction algebra, the universal entire-kernel scaling principle,
  reciprocal-zero and Bernoulli-cumulant condensation, sparse Bell moments,
  the Gould--Hopper/Appell limit, and the polyharmonic semigroup interpretation.

Formal only
- The inverse-frequency and inverse-q formulas are coefficientwise formal
  series.  No convergent boundary germ, sectorial realization, or inverse
  monodromy theorem is claimed.

Conjectural and open
- The proposed all-orders fixed-frequency radial expansion, Diophantine phase
  transition, and two-nome Newton-polygon principle remain conjectural.
- Sectorial inverse theory and the explicitly labeled Stokes, Thue--Morse
  coupling, generic natural-boundary, cyclic-dilogarithm, small-divisor,
  Galois, large-order, and inverse-monodromy problems remain open.
- The downstream cyclotomic asymptotics, condensation, Appell results, and
  natural-boundary proof remain to be formalized in Lean.

The numerical files test constants and asymptotic orders only; they are not
proofs and do not change any status above.  "New" in the manuscript means
apparently new relative to the audited ProveIt repository corpus, not a claim
of worldwide priority.

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
With a standard TeX installation:

    latexmk -pdf -interaction=nonstopmode cyclotomic_q_fabius_frontier.tex

or use pdflatex three times so the contents and cross-references stabilize.
The source expects figures/ and data/ to remain beside it.

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

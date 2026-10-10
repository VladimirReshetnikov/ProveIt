# Finite Golden Seeds and Uniform Analytic Transitions

A research continuation for Vladimir Reshetnikov's ProveIt polylogarithm
manuscript, prepared 10 October 2026 with OpenAI assistance.

## Read the article

- **article/polylogarithms_uniform_continuation.pdf** — complete compiled article.
- **article/polylogarithms_uniform_continuation.tex** — LaTeX entry point.
- The other files in **article/** are the included mathematical sections and references.

The baseline is ProveIt commit
**28357e8ca63dd78327db91d9be239d75e4462879**, dated
2026-10-10 03:57:30 UTC:
[pinned manuscript](https://github.com/VladimirReshetnikov/ProveIt/tree/28357e8ca63dd78327db91d9be239d75e4462879/Analysis/Polylogarithms/docs/manuscript).
The package proposes additions and corrections; it does not modify the remote repository.

## Main mathematical contributions

1. **Complete golden multiplicative seeds.** An infinite-support theorem
   reduces quadratic-unit seeds to indices at most 12 or 24. The full
   golden integral relation lattice has six generators; its even part
   has four. Restrictions to powers of the base have ranks 6, 4, 1, 1,
   and then zero. The all-weight exterior-symbol kernel is determined.
   The historically known even argument list is attributed explicitly.
2. **Sharp real-order signed-measure classification.** The coefficients
   H_(n−1)^(b)/n^a admit a finite signed Hausdorff measure precisely when
   a+b ≥ 1. Above the boundary the density crosses once; at the boundary
   it is negative and there is a positive atom at one.
3. **Angular geometry and complete monotonicity.** Every radius in the
   unit disk has a unique simple angular zero, with a precise enclosure.
   Its Cartesian abscissa is increasing. A critical Hurwitz-zeta deficit
   satisfies strict complete-monotonicity inequalities.
4. **Two scales of endpoint concentration.** The density crossing has
   an explicit power asymptotic and first correction. Typical positive
   mass lies on an exponential scale; its rescaled distribution converges
   in total variation to a unit exponential law.
5. **A uniform reflected log-gamma transition.** At n/(m+1)−log m → s,
   the normalized moments tend to exp(c exp(−s)), where
   c = ζ(2)/(2γ)−γ. There is an explicit first correction, an all-fixed-orders
   construction, and exact identities for diagonal residue polynomials.
6. **A sharp formal depth obstruction.** At weight six the binary
   shuffle indecomposable quotient has dimension nine; depth-two words
   under all six standard argument changes span dimension eight.
   An explicit Lie covariant and a determinant-one minor certify this,
   and two constructive triple congruences follow.

The article also gives the source's still-conjectural weight-seven S6
identity, proposed radial-angle and correction-polynomial conjectures,
and further questions. It **does not** claim numerical period independence,
a maximal golden ladder weight, or a proof of S6.

## Contents

| Directory | Purpose |
|---|---|
| article/ | Complete LaTeX article, included sections, references, and PDF |
| code/ | Exact verification, symbolic derivation, numerical replay, and figure generation |
| data/ | Recorded exact certificates and numerical diagnostics |
| figures/ | Vector PDF figures and PNG previews |
| integration/ | Source correction patch, explanation, and insertion guidance |
| verification/ | Independent proof audits, additional receipts, and final QA record |
| provenance.json | Pinned source, inspected-file hashes, dependencies, and scope |
| SHA256SUMS.txt | SHA-256 checksums for package contents |

No external article PDFs or copies of the complete ProveIt source are
redistributed in this package. The required mathematical statements
are quoted or described with references, and the new proofs are given
in full.

## Build the PDF

From the package root:

~~~sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error polylogarithms_uniform_continuation.tex
~~~

Alternatively run pdfLaTeX on the entry point three times. The figures
are already included, so building the article does not require Python.
The source uses standard TeX Live packages, Latin Modern fonts,
amsmath/amsthm, booktabs, graphics, and hyperref.
No shell escape, remote fetch, or bibliography service is required.

## Replay the mathematics

The exact golden and depth scripts use only the Python standard library.
From the package root:

~~~sh
python3 code/verify_all.py
~~~

This regenerates the two exact finite certificates and writes
verification/replay_summary.json. It does not try to computationally
reprove the external primitive-divisor theorem or the analytic estimates.

For symbolic coefficient checks and all numerical diagnostics:

~~~sh
python3 -m pip install -r requirements.txt
python3 code/verify_all.py --numerical
~~~

The full numerical replay includes independent direct and transformed
moment quadratures, and can take several minutes. It overwrites only
the generated reports in this package. The canonical notation repair
uses exact rational transformations followed by numerical checks;
it does not run PSLQ.

Individual commands are also available:

~~~sh
python3 code/golden_seed_certificate.py > data/golden_seed_certificate.json
python3 code/depth_s3_verify.py
python3 code/moment_asymptotics.py --dps 60
python3 code/geometry_diagnostics.py
python3 code/geometry_boundary_diagnostics.py
python3 code/canonical_reconstruction_check.py --dps 160 --terms 600
python3 code/make_figures.py
~~~

For a faster exploratory moment check, use the --quick flag; it
regenerates the moment report with two cases rather than the eight
bundled here. Rerun the full command before comparing the complete
article table or regenerating all figure data.

## Verification status and limits

- The six golden generators, eighteen finite prime-ideal witnesses,
  restriction ranks, and two own-base identities are checked exactly.
  A separate audit checks all smaller exponents for each witness.
- The depth verifier checks all 320 nonempty weight-six binary
  shuffle products, the determinant-one minor, and both congruences.
- Symbolic algebra verifies the first two moment corrections and the
  gamma moments about the mode.
- The geometric replay records 9 independent kernel comparisons,
  4 density crossings, 15 critical-density values, 16 angular zeros,
  and 12 complete-monotonicity samples.
- The boundary replay records 21 crossings and 84 distribution-function
  comparisons at 90 decimal digits of working precision.
- The canonical-notation replay compares mpmath polylogarithms with
  a separate defining series at 160 digits and certifies the rational
  changes of coordinates exactly.

All numerical checks passed in the recorded run. Floating-point
agreement and analytic series-tail estimates are **not** outward-rounded
interval certificates and do not prove period equalities.
The analytic theorems rest on the proofs in the article.
Independent reviews were conducted within the same research workflow;
the article has not been checked by a proof assistant or externally
peer-reviewed.

## Integration

See **integration/README.md** for the section map, label conventions,
bibliography reconciliation, and figure paths.
**integration/corrections.patch** is a concrete proposed patch against
the pinned source. **integration/EDITORIAL_NOTES.md** explains each
correction, including the published 1987 plastic-base sequel and the
missing canonical L12 definition.

The original source files were left unchanged. Mathematical theorem
status, formal quotient status, numerical diagnostics, and conjectures
should remain distinct when integrating the material.

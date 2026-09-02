# q-Series and inverse q-analogs

This directory contains the one canonical document for forward q-series and
branch-aware inverse q-analog theory:
`q_pochhammer_q_binomial_monograph.tex`. Files under `chapters/` are implementation
units included by that master; they are not independent manuscripts.
The reader-facing structure has 28 numbered forward chapters, eight numbered
inverse chapters, and five appendices. The source-only validator's count of 13
chapter files refers to implementation inputs, not to the printed chapter
count.

The consolidation uses the former q-Pochhammer/q-binomial monograph as its
forward backbone and incorporates the former inverse-q synthesis as a
specialist part. The three general q-series guides were donor manuscripts:
their repeated results map to one strongest canonical statement, while only
genuinely stronger or independent material was transplanted. The completed
`source_concordance.csv` assigns every one of the 547 source result
environments a reviewed disposition. All five source-publication trees are
therefore historical inputs preserved by the pinned revision and repository
history, not parallel live packages.

The editorial contract is mathematical rather than mechanical:

- a repeated result is stated once, with the strongest proved hypotheses and
  one complete human-readable proof;
- an erroneous or overbroad assertion is corrected, split, or removed;
- an unproved assertion survives only when it is interesting, precise, and
  plausible, and then only in an explicitly labelled `Conjecture`
  environment;
- numerical and symbolic checks are evidence or regression tests, not
  substitutes for an infinite proof;
- exact Lean counterparts, partial Lean infrastructure, complete human proofs,
  source records, and conjectures are reported as distinct statuses.

## Provenance and reproducibility

`theorem_concordance.csv` and `audit/SOURCE_REVISION` retain the already
reviewed 260-row history of the six precursor inverse-q packages at commit
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`. Those historical source paths
are immutable. `source_concordance.csv` is the completed 547-row disposition
ledger for the five-publication merge surface pinned by
`audit/MERGE_SOURCE_REVISION` at commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`. The ledgers remain separate so
the earlier six-package inverse provenance is not silently reinterpreted.

The migrated `assets/` tree preserves six experiment programs, nineteen
CSV/TXT outputs, and fourteen vector figures selected by the historical
77-row `assets/ASSET_DISPOSITION.csv`. That disposition ledger remains the
authoritative inventory of the 39 retained historical payloads.

## Validation state

The source-structure gate is:

```text
python audit/validate_canonical.py
```

It checks the complete input graph, balanced environments, unique labels,
resolved references, immediate one-to-one ownership of a nonempty proof by
every proved result, both concordances---the 260-row inverse ledger and the
completed 547-row five-publication ledger---and reproduction of both pinned
source inventories.  Canonical status describes the destination, not the
donor's editorial disposition: a proved row with a live result destination
may never be marked `not applicable`, even when the donor copy was retired.
The larger ledger is reproduced, including all editorial columns, with

```text
python audit/extract_merge_sources.py
```

and may be regenerated explicitly with `--write-reviewed-csv`.  That write is
atomic, is tied to `audit/MERGE_SOURCE_REVISION`, and fails if any editorial
override does not match its pinned source exactly once.

The fifteen status-labelled archival identity records have a separate exact
finite check:

```text
python audit/verify_archival_identity_records.py
```

It compares all coefficients through degree 100 using integer arithmetic:
1,515 equalities in total. This is a transcription-quality gate, explicitly
not an infinite proof of any recorded identity.

Repository policy no longer retains package-level or nested `SHA256SUMS`
manifests. They are not validation gates and must not be recreated. Historical
SHA-256 values recorded directly in this README and in `PROVENANCE.md` remain
provenance receipts for the named artifacts.

The retained `q_pochhammer_q_binomial_monograph.pdf` is a historical 354-page
A4 build of its recorded source checkpoint (14,381 lines, 675,239 bytes,
SHA-256 `240bff72fb47562e9a8fd87085b5a3a96d738189714518db17988f7c4ac15d31`).
The PDF is 3,030,302 bytes with SHA-256
`1050a9a3b0b7a8df8e7de0870946ae64940d7d7839a2f20427be0ebe14b0ba8c`.
It was built by exactly three serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes, which produced 343,
354, and 354 pages, with `makeindex` run on the `.idx` file after each pass.
The final log scan found three overfull boxes, all in the single paragraph of
the `QPochhammerEntire` crosswalk, whose long declaration names lack break
points. All pages are A4. `pdffonts` reports 42 font rows, all embedded and
subsetted, including five Libertinus rows, with no Type-3
fonts. The files under `assets/experiments/**/figures/` remain research
figures, not publication manuscripts.

The current live master is a source-only successor to that checkpoint: it has
14,530 lines, 683,858 bytes, and SHA-256
`b77e9ab54d9437485bab9ee36783cc1f1d5c36c347e67a5242953af8319650fc`.
It adds the explicit document-local `\BellBlockMultiplicity{r}` and
`\MacMahonQCatalanPolynomial{n}{q}` families and normalizes the newly merged
Jackson, Gaussian-binomial, q-integer, and q-Pochhammer status formulas, while
retaining the newest feature, crosswalk, and provenance expansion catalogued
below. No PDF was regenerated after those changes. The historical source
identity above must not be reused for the live source: the PDF and its recorded
14,381-line build source form the retained synchronized checkpoint, while the
current master and retained PDF are distinct artifacts and do not claim render
parity.

The current source includes exhaustive crosswalks for `QPochhammerEntire`
(zero definitions
and five legacy compatibility theorems), `QPochhammerInfinite` (one definition
and twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), `QBinomialTheoremInfinite` (one definition and twenty-two
theorems), `GaussianBinomialPalindromic` (zero definitions and fourteen
theorems), `GaussianBinomialPolynomialStructure` (zero definitions and five
theorems), `GaussianBinomialBounds` (zero definitions and six theorems), and
`GeometricPochhammerNormalConvergence` (zero
definitions and three theorems). The wider inventory also includes
`QMultinomial` (one definition and nine theorems),
`QuantumMultinomial` (zero definitions and five theorems),
`QPochhammerInfiniteBounds` (zero definitions and five theorems),
`QPochhammerComplexOrder` (one definition and four theorems),
`BasicHypergeometricSeries` (two definitions and five theorems),
`HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems). Recent exact surfaces
add `QExponential` (three definitions and eight theorems), `JacksonIntegral`
(one definition and seven theorems), `ThetaQuasiPeriodicity` (one definition
and six theorems), `QPochhammerLogDerivative` (zero definitions and ten
theorems), `QPochhammerOrderDerivative` (zero definitions and three theorems),
`JacobiCubic` (zero definitions and two theorems),
`CentralQBinomialReduction` (zero definitions and six theorems), and
`CyclotomicFactorization` (zero definitions and seven theorems).  The newest
cyclotomic tail consists exhaustively of `CyclotomicDivisibility` (zero
definitions and three theorems), `PrimitiveRootBlock` (zero definitions and
three theorems), `QCatalan` (one definition and eleven theorems), and `QLucas`
(zero definitions and eight theorems).  The latest analytic and interpolation
tail adds `QBetaIntegral` (one definition and eight theorems) and
`NewtonInterpolation` (two definitions and thirteen theorems).  The newest
tail adds `GaussianBinomialInteger` (one definition and ten theorems),
`GaussianBinomialComplexOrder` (one definition and five theorems), and
`QPfaffSaalschutz` (zero definitions and three theorems), together with
expanded Euler, Jacobi, and Rogers--Szegő material.

The two newest generic theorems are
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, which gives a nonzero
derivative at every raw factor zero `a*q^j = 1` including `q = 0`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`, which gives analytic order
exactly one at every zero. The `QPochhammerEntire` wrappers retain the older
`complexQPochhammerInf` names by transferring the generic local-uniformity,
entireness, zero-locus, reciprocal-power, and analytic-order results rather
than duplicating their analytic proofs. In `QBinomialTheoremInfinite`,
`finiteQPochhammerIn_zero_left` remains the unique declaration owned by
`GaussianBinomialAtOne` and is imported rather than redeclared. The forward
status ledger is 90 Exact, 84 Partial, 100 None, and 8 interface rows; the
191-result pre-Fabius core is 36/29/123/3. The compound outer spectral-product
theorem remains Partial even though the three-theorem outer-product leaf proves
local-uniform (normal) convergence for every complex strict contraction, its
nome-`1/4` Rvachev specialization, and the bounded-Fabius Fourier
specialization. Its named centered/MGF packaging and exterior reciprocal
formula, pole divisor, and zero--pole exchange remain outside Lean.

The new status changes record the exact q-exponential eigenfunction and
Jackson integration-by-parts subclaims, and Partial formalizations of the
q-exponential factorization, Jackson fundamental theorem, and theta
quasi-periodicity; the remaining clauses named in their rows stay explicit.
The incoming tail further makes the full elementary Gaussian-polynomial
structure and Jacobi's cubic identity Exact, while adding Partial order
derivative and Gaussian-moment rows; the Lambert logarithm row remains
Partial with both displayed derivative formulas now formalized.
The central-reduction row is now Exact through a division-free commutative-ring
identity and its field quotient wrapper; the cyclotomic-factorization row is
Exact over every commutative ring for the factorial form and every integral
domain for the Gaussian form, with the exponent bounds stated explicitly. The
half-base Gaussian valuation row remains Partial: Lean proves the reciprocal
identity and symmetry used in the argument, while the concluding odd-integer
valuation statement is still outside the formal surface.
The Jackson q-beta evaluation and both recurrences are Exact over the stated
real domain `0 < q < 1`, `0 < x`, `0 < y`.  The geometric Newton formula and
its triangular-coefficient corollary are Exact via the generic field-valued
interpolation API and its geometric-grid specialization.
The terminating q-Pfaff--Saalschütz row is Exact under its explicit field and
nonvanishing hypotheses.  The integer-index Gaussian definition, reflection,
two Pascal laws, and reciprocal series are Exact; so are the upper-parameter
and generalized complex-order series on their stated norm domains.  The
separate complex-parameter property and classical-specialization rows remain
None and are not inferred from those series identities.
The quantum-multinomial row is Exact over every semiring under the stated
pairwise q-commutation laws and commutation of q with each variable; neither
centrality of q nor commutativity of the ambient semiring is claimed.
`GaussianBinomialBounds` owns six theorems. Its finite-product positivity
input `finiteQPochhammerIn_self_pos` is the pre-existing generic declaration
from `GeneralQConditionNumber`, reused through an import and therefore not
counted as a seventh theorem of the bounds leaf.

The complete root block, evaluated q-Lucas theorem, square-free cyclotomic
criterion, and q-Catalan row are Exact. The primitive-root value in the
Babbage corollary is formalized over every integral domain, while its
derivative clause keeps that compound row Partial.

The geometric Newton interpolation and divided-difference rows are Exact. The
Jackson q-beta product/q-gamma evaluation and its two recurrence formulas are
also Exact. The terminating q-Pfaff--Saalschütz sum and quantum multinomial
are Exact, as are the integer-index Gaussian definition and Pascal laws, both
reciprocal-product expansions, the complex upper-parameter series, and the
generalized q-binomial theorem. The remaining complex-Gaussian property and
classical-limit rows stay unformalized.

No PDF was generated locally while resolving this merge. The retained
354-page artifact remains the validated historical checkpoint described
above. No deleted checksum manifest was recreated.

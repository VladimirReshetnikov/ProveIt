# Exact reproducibility checks for report120

Python 3.10 or newer, standard library only. The reader package needs no network,
third-party package, source PDF, research directory, or private file.

From the package root:

    python3 -B checks/run_checks.py
    python3 -B -O checks/run_checks.py
    python3 -B checks/mutation_tests.py --output /tmp/report120-check-results.json

The first two commands print an exact-arithmetic JSON certificate. The aggregate
last command compares normal and optimized baselines, repeats both in a fresh
directory, and runs all fixture-leaf plus named schema, mathematics, and file
mutations. Each negative test must fail with its expected diagnostic in both
modes. Input files must remain byte-for-byte unchanged. Output must be outside
this checks directory. A nonzero exit status is failure.

`MANIFEST.json` seals every other supplied file and admits no additional file,
subdirectory, symlink, or special file. The manifest is an integrity inventory,
not a signature: mathematical/schema mutations are resealed deliberately, so
successful rejection cannot rely only on changed hashes. All guards use explicit
conditionals and remain active under `-O`. Bytecode creation is disabled.

## Independent reconstruction and exact scope

- `exact_math.py` independently enumerates symmetric alternating-sign matrices
  from their original row/column partial-sum definition for n=1,...,5. It also
  enumerates all internal-edge orientations of the triangular graph for
  n=1,...,4. These agree on the full joint diagonal-nonzero mask polynomial,
  which is stronger than merely matching its univariate specialization
- The original unweighted Pfaffian independently reproduces all 20 published
  A005163 terms n=1,...,20. Recursive Pfaffian expansion checks n<=8, and its
  square equals the exact determinant throughout. Direct bivariate kernel
  expansion agrees with the original coefficient sum on a 21-by-21 grid
- The degree-at-most-n adjacent determinant polynomial D_n(t) is reconstructed
  at n+1 exact rational interpolation nodes for n=1,...,10. Independent banded
  determinants agree at all nodes. Original bordered coefficient determinants
  and both Pascal/Toeplitz forms are checked for n<=8. Adjacent division yields
  P_n for n<=11, agreeing with the independent matrix enumeration where available
- Finite Pascal factorization, inverse/congruence, every monomial case of the
  binomial/Toeplitz conjugacy, and the hockey-stick identity are checked through
  matrix size 10. The shifted Andrews determinant, double product, ASM factorial
  product, and the n+1 indexing are checked through size 16
- Sparse rational-polynomial cross multiplication verifies the exact kernel
  decomposition, Mobius transformation, specialization at t=3, and Jensen's
  fugacity parameter/inverse identities. The Stirling inverse-N contributions
  sum exactly to -5/36; the even calibration logarithm is -5/72. Odd-parity
  coefficient algebra and the formal inverse residual are checked exactly,
  including its nonzero constant term. Finite rational rounding tests distinguish
  the >= threshold from > and verify the width-less-than-one ceiling lemma
- `interval_math.py` is an independent rational interval implementation. It uses
  range-reduced logarithm series, range-reduced exponential series, rigorous tail
  bounds, and outward rational-grid rounding. No binary floating-point number
  enters its certificates. It checks every supplied p/q/width decimal endpoint,
  the strict fixed-point signs, map endpoint gaps, contraction, and inverse
  limiting width below one. The JSON output includes exact fractions and
  outward decimal views of all intermediate parameter intervals
- `fixtures.json` contains only public source provenance and expected exact
  results. All external sequence terms are distinguished from internally
  reconstructed diagonal polynomials; the OEIS b-file was not used

## What finite computation does not establish

Real-rootedness is an analytic stability theorem proved in the report. Neither
finite enumeration nor numerical root calculations prove it; no numerical root
finder is used here. The published graph-to-DSASM correspondence, closure of
stability, classical Andrews determinant theorem, controlled Stirling remainder,
projected-contraction argument and asymptotic inverse estimates are analytic
proof inputs, not consequences of testing finitely many cases.

An independent-Bernoulli representation of the total diagonal count does not
assert independence of actual diagonal entries. These checks do not establish
a limiting linear coefficient, the full DSASM asymptotic equivalent, the true
logarithmic power, a multiplicative amplitude, root simplicity, interlacing, or
general r-weighted stability. No common calibration amplitude is assumed.

The final envelopes have bounded logarithmic remainders after retaining
-(5/72) log n. Their constants and the eventual onset of the two-ceiling inverse
bracket remain existential. The inverse error must stay inside its rounding
bracket. No bibliographic novelty claim is made.

## Public source provenance

Roger E. Behrend, Ilse Fischer and Christoph Koutschan, *Diagonally symmetric
alternating sign matrices*, arXiv:2309.08446v3 (1 October 2026), equation (4.11),
section 5.1, and Proposition 5.1 equation (5.10):
https://arxiv.org/html/2309.08446v3

OEIS A005163, published 20-term prefix n=1,...,20 previously transcribed in the
source verification and independently recomputed in this offline package:
https://oeis.org/A005163

Christian Krattenthaler, *Advanced Determinant Calculus*, Theorem 34,
equation (3.24), specialized at q=1 with shift/index as stated in the report:
https://www.mat.univie.ac.at/~kratt/akkomb/detsurv.pdf

Inventory/schema/mutation infrastructure follows report119 conventions; the
mathematical algorithms and interval implementation have been reconstructed for
this report and do not import its mathematics or any research certificate.

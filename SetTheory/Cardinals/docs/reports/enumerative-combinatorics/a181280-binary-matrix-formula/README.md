# A twelve-value proof of the A181280 formula

This package contains a detailed article and exact reproducible arithmetic for
the binary-matrix formula recorded as Conjecture 20 by Kauers and Koutschan
(2023) and still marked conjectural in OEIS A181280 when retrieved on
19 September 2026.

**Read `STATUS.md` before making a novelty or priority claim.** General
C-finiteness was already proved in Kauers's December 2025 lecture slides. The
present report provides an explicit spectral recurrence bound, a finite
certificate of the formula, and further consequences. No independent peer
review or Lean formalization is claimed.

## Contents

- `article.pdf`: the compiled comprehensive article.
- `article.tex`: the complete LaTeX source (uses the small Python file below
  as a typeset code listing).
- `verify.py`: full exact verifier, written using the Python standard library.
- `minimal_certificate.py`: a separate tuple-state implementation of the twelve
  decisive counts, also printed in the article.
- `results/certificate.json`: machine-readable initial values, Gram acceptance
  masks, recurrence coefficients, generating-function coefficients, and audit
  details.
- `results/counts.csv`: definition-based counts through n = 100, including
  zero-Gram counts and the exceptional n = 0,1,2,3 formula evaluations.
- `results/verification.txt`: output of the executed full verification run.
- `results/minimal_verification.txt`: output of the separate small verifier.
- `STATUS.md`: source provenance and the exact limits of the status/novelty check.
- `build.sh`: PDF rebuild script.

## Reproduce the arithmetic

Python 3.10 or later is required. No third-party Python packages, network
connection, external data, or symbolic algebra system are needed.

```sh
python3 minimal_certificate.py
python3 verify.py --out results
```

The default full run checks exact counts through n = 100, exhaustively checks all
1024 weighted 8-by-8 matrix annihilator identities, compares Fourier inversion
with direct Gram-state dynamic programming, and independently brute-forces all
four-element row sets through n = 6. It also checks the general recurrence for
every Gram target for m = 1,2,3 through n = 20. The initial recorded run used
Python 3.13.5 and took about 4.15 seconds; timing depends on the machine.

`verify.py` accepts `--limit` (16 through 10000) and `--brute-max` (0 through 6).
The upper length limit is an input guard, not a practical resource guarantee:
very large limits can use substantial memory because the audit retains history.
The reusable enumerator supports 1 <= m <= 5 as a resource guard; the theorem
in the article holds for every positive m.

## Rebuild the PDF

A reasonably complete TeX Live installation is required. The build uses
pdfLaTeX and standard packages including newtx, amsmath, amsthm, mathtools,
booktabs, microtype, tcolorbox, listings, hyperref, and cleveref.

```sh
sh build.sh
```

Run this command from the package root. The TeX source imports
`minimal_certificate.py`; keep these two files together. No font files are
included or need to be obtained from this package.

## What is proved

The article proves the universal recurrence *from the combinatorial definition*,
using a row-prefix automaton, Fourier characters of symmetric binary matrices,
a quadratic Walsh-sum lemma, and a level filtration. For four rows it has order
12 and holds on the tail starting at n = 4. The conjectured expression satisfies
the same recurrence. Twelve exact counts for n = 4,...,15 therefore prove the
identity for all n >= 4, by ordinary induction. The additional tests through
n = 100 are validation, not the basis of an extrapolation.

For an arbitrary fixed row count m and any allowed Gram set, the derived
universal eventual recurrence has order m + 2 floor(m^2/4). The report also proves
that the four-row order 12 is sharp across all Gram acceptance conditions,
whereas the selected A181280 sequence has minimal eventual order 11.

All polynomial coefficient arrays in the JSON certificate use **ascending
powers**. The OEIS sequence is indexed from n = 1; the package explicitly extends
it with a(0) = 0. The exponential-polynomial formula must **not** be applied to
a(0), a(1), a(2), or a(3).

## Related reports

*Added 3 October 2026 (batch 85).* Other conjectures and questions of the
Kauers–Koutschan (2023) paper whose Conjecture 20 this report proves are
treated in the collection:

- `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/a195806-hexagonal-lattice`
  (Conjecture 11) and Part IV of
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a215561-fixed-composition-excursions`
  (Conjecture 15).
- `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a047874-long-increasing-subsequences`
  (batch 85). The paper's Conjecture 17, the A269021 recurrence, was proved
  by Kauers and Wang (arXiv:2609.02220, 2026); that report answers the
  sector question their paper raises (D-finiteness of the LIS array in every
  sector `N ≤ rk`) and gives five correction terms for A269021. Its
  package's source audit names the present report as the reason A181280 was
  not chosen as its target.
- `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles`
  (batch 85): the shifted rectangles A181198/A181199 of the paper's
  Section 6.4. The A181199 leading asymptotic and all-order expansions are
  proved there; the guessed recurrences are not.
  [Added 5 October 2026, batch 98: Part II of that report proves that the
  generating function of every fixed-height row of A181196 (A181198 and
  A181199 included) is the diagonal of a rational power series, hence
  D-finite (its Theorem 14.1, via Bostan–Lairez–Salvy's multiple binomial
  sums), so the Section 6.4 sequences are now proved D-finite; the
  particular guessed recurrences and finite sums of Section 6.4
  (Conjectures 18–19) remain unproved.]
  [Added 7 October 2026, batch-101 reciprocal note: "the guessed recurrences
  are not" and "remain unproved" above are out of date. Parts III and IV of
  that report (Research Reports 231 and 233, batch 101) prove, from the
  array definition, the order-two, degree-nine A181198 recurrence and the
  order-three, degree-24 A181199 recurrence for every n ≥ 1, and the paper's
  Conjectures 18 (for n > 1) and 19, the printed finite sums (Theorems 26.1,
  30.1, 30.2, 34.1, 34.2 there); its Proposition 33.2 shows that order two is
  minimal for A181198. So the Section 6.4 conjectures, like this report's
  Conjecture 20, are now proved in the collection; unrefereed, not
  formalized.]

None of these reports uses this one's theorems. All are unrefereed and none
is formalized.

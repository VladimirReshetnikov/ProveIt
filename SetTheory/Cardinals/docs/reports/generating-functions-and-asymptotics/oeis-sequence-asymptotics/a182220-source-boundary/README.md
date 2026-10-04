# The source boundary of extensional acyclic digraphs

**An OEIS conjecture, finite-defect enumeration, and dyadic non-holonomicity**

Research prepared for Vladimir Reshetnikov, October 3, 2026.

## Read first

`article.pdf` is the typeset article; `article.tex` is its complete source.
The main theorems are conventional mathematical proofs, not Lean/Rocq
certificates. Historical priority for the boundary refinements is not
established. The source upper bound and general source sieve have explicit
prior art, which the article credits.

For n >= 1 let q = ceil(log2(n)), let u_m = OEIS A001192(m), and let
b_n^(d) count isomorphism classes of extensional acyclic digraphs on n
vertices with exactly n-q-d sources. Out-of-range source counts are zero.

The article proves:

- A182220(n) = n-q, together with the full feasible source-count interval.
- b_n^(0) = u_q * binomial(2^q-q, n-q), via an exact core classification.
- A (d+1)-term exact formula for each fixed-defect boundary diagonal.
- A uniform covering estimate and entropy law for every fixed d.
- Every b^(d), and its labeled counterpart n! b^(d), is not P-recursive.
- The full interval of subsequential nth-root growth rates; for d=0 it is [1,4].
- An all-orders expansion of the Boolean-subset factor, with u_m retained exactly.
- A quantitative binomial approximation for arc deficits near n=2^m.

The current OEIS entry still labels the maximum formula conjectural, but
Tomescu's 2011 thesis already states its upper-bound half. An OEIS label
is not a certification that the problem remained open in the literature.

## Contents

- `article.tex`, `article.pdf`: manuscript and compiled PDF.
- `verify.py`: standard-library exact checks and independent brute-force enumeration.
- `check_asymptotics.py`: standard-library Decimal numerical diagnostics.
- `data/verification.json`: structured exact verification report.
- `data/verification-output.txt`: human-readable output of the exact run.
- `data/source_triangle.csv`: exact labeled and unlabeled source counts to n=64.
- `data/boundary_counts.csv`: boundary counts for d=0,1,2 to n=64.
- `data/asymptotic_checks.csv`, `data/asymptotic-output.txt`: prefactor diagnostics.
- `SOURCES.md`: provenance, access limitations, and prior-art distinctions.
- `STATUS.md`: theorem and verification status.
- `manifest-entry.tex`: a suggested repository bibliography/manifest paragraph.
- `SHA256SUMS`: hashes of the package files other than the checksum file itself.

## Reproduce the computations

Python 3.10 or later; no third-party Python packages are required.

```sh
python verify.py --max-n 64 --brute-n 7
python check_asymptotics.py
```

The recorded exact run checks 2,080 source-count cells with two independent
recurrences, 2,080 covering inequalities, 64 extremizer counts, and 354
finite-defect entries. It matches 17 displayed terms of A001192 and 25
flattened displayed terms of A182162. Brute-force enumeration through
n=7 includes 75,598 isomorphism classes at n=7 and independently verifies
source and extremal arc distributions.

`check_asymptotics.py` checks the first correction at n=192,768,3072,12288
and d=0,1,2 using 70-digit Decimal arithmetic. All 12 tests show an
improvement. These numerical diagnostics are not interval-certified bounds.

Brute-force checking is deliberately capped at seven vertices. For a faster
run without enumeration, use `--brute-n 0`. The exact triangle can be
computed to larger n using `--max-n`, with increasing integer sizes.

## Build the article

A normal TeX Live installation with pdfLaTeX and the packages listed in the
preamble is sufficient. Bibliography entries are embedded; no BibTeX step
is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article.tex` three times to resolve contents,
references, and page numbers. No custom font files are included or required.

## Repository placement

The inspected repository snapshot was:

`6bf7f30d0352f7596e70928b3d4f304914075907`

Suggested new directory, subject to the user's preferred organization:

`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a182220-source-boundary/`

No files were committed to GitHub and no OEIS submission was made.

# Signed Quadratic-Feedback Inversion
## A finite-core resolution and sharp entire Borel growth

Research draft prepared for Vladimir Reshetnikov, 29 September 2026.

This package contains a 21-page article (20 pages as delivered; see
"Editorial amendments"), its self-contained LaTeX source,
exact-arithmetic verification programs, and recorded diagnostic data.

## Main result

Let U(q) be the unique formal solution of

    U(q) = sum_(j>=1) w_j q^j exp(lambda_j U(q)),

where w_1 = 1 and, after finitely many arbitrary real exceptions,
w_j = 1 and lambda_j = a j^2, with a > 0. Write V = U^(-1) for its
compositional inverse, v_n = [t^n] V(t), and b = (lambda_1 + w_2)/a.
Define r_n by

    r_n (1 + r_n) exp(2 r_n) = a n,

and

    S_n = exp(n r_n (1 + 2 r_n)/(1 + r_n)) / sqrt(2 r_n^2 + 4 r_n + 1).

The article proves

    v_n ~ - S_n exp(-b r_n).

For the pure model this is the explicitly conjectural quadratic inverse
equivalent in ProveIt's finite-core universality article. The proof first
resums a finite analytic inverse core, then controls all multiple-tail
contributions using a quadratic merger defect. A large auxiliary core
provides arbitrary algebraic accuracy; the leading equivalent itself needs
only the first two actions. The one-action core suffices exactly when w_2=0.

A second saddle calculation proves an explicit equivalent for the entire
ordinary Borel transform B(z) = sum v_n z^n/n!. For s(s+1)=aR,

    -B(R) ~ max_(|z|=R) |B(z)|
          ~ exp(s exp(2s)/a - b s) / sqrt(2s+1).

Thus its positive-direction ordinary Laplace integral diverges because of
growth at infinity, despite the absence of finite Borel singularities.

## Contents

- `article.pdf`: the article, rebuilt with editorial notes (21 pages).
- `article.tex`: complete source, including bibliography and numerical table.
- `code/verify.py`: integer-normalized recurrence, independent finite
  composition checks, and numerical comparison values.
- `code/symbolic_checks.py`: six exact symbolic identities.
- `data/exact_coefficients.json`: coefficients in four models through degree 220.
- `data/diagnostics.csv`: signed ratios to the asymptotic equivalent and,
  in the pure cases, to the exact two-action one-tail response.
- `data/verification.json`, `data/symbolic_checks.json`: check results.
- `data/run.log`: recorded standard output of `code/verify.py --order 220`
  (a rerun differs only in its timing lines).
- `PROOF_STATUS.md`: theorem scope, dependencies, and limitations.
- `SOURCES.md`, `PROVENANCE.json`: source attribution and repository snapshot.
- `BUILD_REPORT.json`: software versions and build/check summary.
- `requirements.txt`, `build.sh`: reproduction aids.
- The delivered checksum ledger `SHA256SUMS` was verified in full on
  filing (batch 49) and not kept; the delivered archive remains in the
  repository history (see `docs/incoming/README.md`, batch 49 row).

## Reproduction

Use Python 3.10 or later, with the dependencies in `requirements.txt`.
The algebraic recurrence itself uses only the standard library; the driver
also imports mpmath for the diagnostic comparisons. SymPy is used only by
the symbolic script.

```sh
python -m pip install -r requirements.txt
python code/verify.py --order 220
python code/symbolic_checks.py
```

The coefficient driver accepts orders at least 20, so that all independent
low-order checks are included. Its full table costs cubic arithmetic work
and quadratic storage; integer bit costs grow as the order increases.
Larger runs can therefore be much slower than the supplied run.

To rebuild the PDF, use a TeX installation containing the ordinary packages
listed in `article.tex` (Latin Modern, AMS mathematics, microtype, geometry,
booktabs, enumitem, xcolor, fancyhdr, titlesec, xurl, hyperref, and bookmark):

```sh
sh build.sh
```

The article is self-contained and does not require Python output files,
a network connection, external figures, or a separate bibliography database
to compile. No font files are distributed in this package.

## Recorded checks and their limits

The four degree-220 models are the pure cases a=1 and a=2, one signed
finite perturbation, and one cancellation of the leading core penalty.
There are 24 independent ordered-composition assertions, two independent
forward/inverse composition block assertions through degree 11, and six
symbolic identities: all 32 recorded assertions pass.

Stored coefficients are **n! times** the ordinary coefficients. Element 0
is the zero constant term. Divide element n by n! to recover v_n. Do not
use the stored integers directly as ordinary or Borel coefficients.

Floating-point ratios are diagnostics, not interval certificates. For example,
at n=220 the pure a=1 ratio to the main equivalent is approximately 0.8448;
the signed perturbation ratio is approximately 2.693. The article explicitly
discusses these substantial finite-order corrections and makes no uniform
onset claim. Finite tests are not substitutes for the asymptotic proofs.

## Proof and priority status

This is an AI-assisted conventional research draft, not an independently
refereed or Lean-verified paper. It identifies and proves a specific
repository-local conjecture and additional model-specific results. Worldwide
novelty or publication priority has not been certified. The pure forward/
inverse ratio corollary explicitly depends on a forward theorem from the
repository; the inverse and Borel theorems have their own proofs here.

The article ends with twelve research questions, including sharp two-core
remainders, full higher-order expansions, effective onset bounds,
subquadratic feedback, complex Borel growth, acceleration, and Lean
formalization. No ProveIt file, branch, issue, or pull request was modified.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 49 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: two visible "Editorial note (ProveIt, 2026-09-29)"
  paragraphs (an unnumbered environment, so the article's own numbering is
  unchanged), each preceded by a `% ed. (2026-09-29)` comment. At the end
  of Section 1.1: the proof is claimed and unreviewed; it answers, for the
  inverse series, the negative-ray article's question "Signed coefficient
  asymptotics and actual least error"
  (`../Negative_Ray_Summation_Exponential_Feedback/article.tex`, lines
  1372-1381); its Borel theorem parallels the regularity article's
  `thm:borelintro` (`../Exponential_Feedback_Regularity_Classification/article.tex`,
  lines 288-303), neither of which it cites; and `cor:gevrey` and
  `eq:Bgrowth` upgrade to limits the two limsups of the later weighted-type
  package `../Sharp_Weighted_Type_Formal_Reversion/`. After Theorem
  `thm:main`: a second, independent claimed proof of the same conjecture is
  `../Quadratic_Exponential_Feedback_After_Reversion/` (nonnegative
  exceptions, affine and borderline slope tails); neither set of
  hypotheses contains the other, and the two packages' exact inverse
  coefficients agree at every common degree (through 220 for `a = 1`, 180
  for `a = 2`; rechecked on filing). In Section 1.1 the sentence "The
  inspected repository tree was ..." now says "commit": the identifier is a
  commit, not a Git tree. Four bibliography entries `ed:qef`, `ed:nrs`,
  `ed:reg`, `ed:swt` were added. No existing label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `build.sh`'s three
  pdflatex passes (21 pages; the delivered PDF had 20). Line numbers of
  `article.tex` after the first insertion point differ from those of the
  delivered file. `BUILD_REPORT.json` describes the delivered 20-page build
  and was left unchanged.
- `SOURCES.md`: "Observed root tree/commit identifier" corrected to
  "Observed commit identifier", with a note. `PROVENANCE.json` keeps its
  delivered key `observed_root_tree`; its value is that same commit.
- `code/verify.py`, `code/symbolic_checks.py`: the CSV writer passes
  `lineterminator='\n'` and the JSON writers `newline='\n'`, so reruns emit
  LF on every platform (the JSON files still end without a final newline,
  as delivered). Rerun on a copy (`--order 220`, Windows, mpmath 1.3.0,
  sympy 1.14.0): `exact_coefficients.json`, `diagnostics.csv` and
  `symbolic_checks.json` were byte-identical to the filed files;
  `verification.json` differed only in `elapsed_seconds`, and the standard
  output only in the four timing lines of `data/run.log`. The default
  output directory `data/` and default order 220 are those of the recorded
  run, so a default rerun reproduces it.
- `README.md`: the page count, the `data/run.log` and ledger bullets under
  "Contents", and this section.

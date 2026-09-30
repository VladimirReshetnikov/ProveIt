# Algebraic Convergence Loci for Nonlinear Hahn–Fuchsian Systems

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `article.pdf` — the complete 23-page A4 article (22 pages as delivered).
- `article.tex` — standalone LaTeX source with an embedded bibliography.
- `verification/verify.py` — exact finite symbolic checks.
- `verification/results.json` — output of the successful verification run.
- `notes/proof_audit.md` — mathematical assumptions and validation boundaries.
- `notes/source_audit.md` — repository and literature comparison.
- `notes/build_report.json` — recorded PDF and verification checks.

## Main results

The setting is `D y = A y + F(x,y)`, with `D = x d/dx`, an arbitrary fixed
complex matrix `A`, and positive, logarithm-free Hahn solutions on a fixed
well-ordered additive monoid of nonnegative real exponents. Finite accumulation
of exponents is allowed. The nonlinear input has no constant term or linear
term at x-exponent zero and satisfies an explicit joint absolute-convergence
majorant.

**Theorem 5.1:** the resonant parameters producing absolutely convergent
solutions form an affine algebraic set, even at zero spectral gap. Its proof
first confines divergence to the bounded exponent window below the largest
positive real eigenvalue, then applies finite-dimensional linear algebra to
polynomial coefficient families modulo the summable subspace. The equations
have a sharp weighted-degree bound. Theorem 5.4 gives a common convergence
radius on compact parameter sets.

**Theorem 7.1:** after normalizing auxiliary free resonant coefficients, every
affine algebraic set occurs as such a convergence locus, even when every
parameter is formally compatible. Without the normalization, an explicitly
stated affine factor remains. Singular, reducible, and disconnected examples
are included.

Other results include finite polynomial formal-compatibility certificates,
finite exact additive ancestry, the sharp total degree bound
`2 floor(resonance / least positive exponent) - 1`, a necessary-and-sufficient
universal spectral-gap criterion, and an explicit nonlinear example in which
well-separated forcing generates a sharp small-divisor threshold.

For the scalar family in Section 8, all formal branches exist, and convergence
is equivalent to `p > 2 or a*b = 0`, independently of the top resonant parameter.
The article also proves that no general finite set of input coefficients can
determine the analytic convergence locus.

Section 10 develops ten further research questions, including effective
summability quotients, moving eigenvalues, logarithmic solutions, higher-rank
supports, irregular equations, and a complete Lean model case.

## Build the PDF

Run from this directory:

```sh
sh build.sh
```

The build uses three `pdflatex` passes and writes `article.pdf`. A standard
TeX Live installation providing the packages in the preamble is sufficient.
No bibliography processor, repository checkout, private font files, or network
access is needed for the TeX build. Intermediate files are kept in a temporary
directory and removed on exit.

## Reproduce the exact checks

Python 3.10 or later is required. Install the recorded dependency and run:

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

The delivered run used Python 3.13.5 and SymPy 1.14.0, with seed 20260929.
It checked 21 finite systems and 670 exact scalar equalities in total,
including 24 independent Riccati recurrence identities. All passed.
The script writes `build/results.json` (relative to this directory; as
delivered it overwrote `verification/results.json`, which now requires
`--overwrite-recorded`) and raises an exception on any failed check. The checks are not disabled by Python's optimization flag.

The program enumerates only finitely generated rational monoids below finite
cutoffs. It checks exact recurrences, residuals, resonance projections,
polynomial identities, and displayed finite coefficients. It does NOT prove
infinite-support convergence by truncation.

## Scope and status

The article supplies conventional mathematical proofs, not a Lean
formalization. The finite checks support the formulas but do not machine-verify
the general theorems. The selected repository support module was read, not
recompiled here. No repository files were changed.

The proposed contribution is the algebraicity and universality of the
parameter-dependent absolute-convergence locus at zero spectral gap. Classical
support lemmas, generalized-series fixed-point theory, convergence results in
other settings, and the repository's earlier linear normalization theorem are
acknowledged. The comparison was targeted rather than exhaustive; historical
priority and independent peer review are not claimed.

Finite polynomial conditions do not imply finite-input decidability. The
analytic conditions can depend on infinite summability relations. Failure of
absolute convergence does not mean that a weaker renormalized analytic
realization is impossible. Failure of compatibility refers to the positive,
logarithm-free solution class, not to all possible transseries extensions.

Repository snapshot inspected:
`3d5973524506411392a911470b5ddc35521568ea`.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 52 (see `docs/incoming/README.md`). The
following changes were made on 2026-09-29; everything else is as delivered.

- `article.tex`: an unnumbered `ednote` environment (the article's remarks
  share the theorem counter, so its numbering is unchanged) and one visible
  "Editorial note (ProveIt, 2026-09-29)" paragraph at the end of the
  introduction of Section 1, preceded by a `% ed. (2026-09-29)` comment:
  the universal criterion of Theorem 6.1 (`thm:gap`) is proved
  independently, for real spectrum with resonant constants and logarithms,
  as `thm:universal` of `../Nonlinear_Hahn_Dulac_Finite_Resonance_Control/`
  (batch 52; one criterion, two independent proofs, agreeing where both
  apply), whose accumulation example (`thm:sharp-family`, `p > 2`) has
  accumulating forcing, unlike Theorem 8.1 (`thm:hidden`); the linear
  counterpart of `thm:hidden` is `ex:hidden` of
  `../Path_Sensitive_Small_Divisors_Hahn_Fuchsian/`; and the Hahn–Fuchsian
  article's further direction closest to this question is "Geometry of the
  logarithmic strata", of which the convergence loci are a nonlinear
  counterpart, not an answer (the article's own summary of those directions
  mentions "exceptional parameter sets").
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`
  (23 pages; the delivered PDF had 22; no errors, undefined references,
  multiply defined labels, duplicate destinations or overfull boxes).
  Line numbers of `article.tex` after line 22 differ from the delivered
  file.
- `verification/verify.py`: writes LF on every platform (as delivered, its
  `write_text` produced CRLF on Windows) and has `--output`, defaulting to
  `build/results.json`; writing the recorded `verification/results.json`
  requires `--overwrite-recorded`. Rerun on a copy (Windows, Python 3.13.5,
  SymPy 1.14.0, default output): 670 equalities passed and the output is
  byte-identical to `verification/results.json`.
- `notes/build_report.json`: `pdf_pages` and the four `sha256` entries
  recomputed for the filed files (`verification/results.json` is
  unchanged); an `editorial_rebuild` field says so; its other fields,
  including the per-page checks, describe the delivered build.

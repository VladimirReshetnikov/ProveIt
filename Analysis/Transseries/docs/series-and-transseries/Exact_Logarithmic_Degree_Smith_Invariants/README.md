# The Exact Logarithmic Degree of Hahn-Transseries Solutions

**Finite jets, Smith invariants, and cancellation-sensitive resonance**  
Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `exact_logarithmic_degree.pdf`: the 29-page article.
- `exact_logarithmic_degree.tex`: standalone editable LaTeX source, including bibliography.

The article addresses the exact minimum promoted-logarithm degree and
cancellation-sensitive resonance questions explicitly posed in ProveIt's
*Finite Residue Obstructions and Logarithmic-Depth Promotion in Hahn Transseries*.

## Main results

For outer-small linear Euler perturbations over the specified real Hahn field
of logarithmic depth n >= 1, the article constructs a finite formal matrix series
M(z), with z acting as differentiation in the newly added logarithm T.
Its Smith exponents nu_i satisfy

    sum(nu_i) = r,       0 <= nu_i <= s,

where r is the sum of real-root multiplicities and s is the number of distinct
real indicial roots. They give the complete homogeneous degree filtration and
the minimum degree of every T-independent forcing. Finite block Toeplitz rank
tests give exact positive and negative certificates. Classification requires
only coefficients M_0 through M_(s-1), with explicit finite word-depth bounds.

A residue-weighted scalar subclass has the exact pencil M(z) = D_P(z I + B).
Every strictly upper triangular rational matrix B, hence every partition of the
operator order as a logarithmic-index profile, has an explicit finite rational
scalar realization. A fourth-order family distinguishes the correct weighted
cancellation data from both the unweighted graph and the nilpotency of M_0.

See Theorem 6.2 (classification), Theorem 7.1 (finite certificates), Theorem 8.1
(exact pencil), Theorem 9.1 (scalar realization), and Section 10 (cancellation).
Nine further research directions are developed in Section 13.

## Scope and status

These are conventional mathematical proofs, not a Lean formalization or an
independently refereed publication. Smith, Toeplitz, and Jordan-chain methods
are classical and are credited. Global priority is not established.

The theorem concerns solutions in H_n[T], with polynomial dependence on T.
Coefficients lower the outer x exponent by a uniform positive amount.
It does not assert analytic summability, classify arbitrary dependence on T,
or cover merely logarithmically small perturbations. Effective computation on
arbitrary Hahn data needs explicit coefficient-operation oracles; the finite
rational scalar realization with residue forcing does not have that obstacle.

## Exact verification

Python 3.10 or newer and SymPy are required. The recorded environment is
Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
python verification/operator_check.py
```

The recorded runs passed:

- 1,383 exact assertions in the primary algebraic suite.
- 192 exact projected-column checks in an independent noncommutative scalar
  differential-operator calculation, through jet degree 3 and word length 6.

The actual outputs are `verification/results.json` and
`verification/operator_results.json`. (Editorial, 2026-09-29: both programs
now write into `rerun/` in the package root by default; writing the recorded
files in `verification/` requires `--overwrite-recorded`. On Windows use `py`
instead of `python`, or `uv run --no-project --with sympy==1.14.0 python
verification/verify.py`.) The primary suite includes rational
left-nullspace certificates for rejected degrees in the fourth-order example.
The arithmetic is exact; these are finite regression checks, not a verification
of all infinite Hahn-support arguments. No floating-point tests are used.

## Rebuild the document

With a standard TeX installation containing the packages in the preamble:

```sh
sh build.sh
```

The script runs pdfLaTeX three times and stops on an error. It needs no external
figures, bibliography processor, network access, or repository checkout.

## Additional files

`notes/proof_audit.md` records assumptions, key proof dependencies, and boundaries.
`notes/repository_provenance.json` records the inspected snapshot and source paths.
`notes/validation.json` records the PDF/build and verification checks; its
page count, sizes and the two SHA-256 digests of the article PDF and source
were recomputed for the editorial rebuild of 2026-09-29 (see below).
The delivered checksum ledger `SHA256SUMS.txt` was verified in full on filing
(12/12, batch 50) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 50 row).

The repository snapshot is `76b8ea50cc67f2255c11b27e0edc9ed0fca3b5cd`.
No repository files were changed or uploaded.

## Editorial amendments (ProveIt, 2026-09-29)

Filed on 2026-09-29 (batch 50 of `docs/incoming/`; see `docs/incoming/README.md`).
The following changes were made; every change to the article source is
preceded by a `% ed. (2026-09-29)` comment, the visible additions are labelled
"Editorial note (ProveIt, 2026-09-29)" or "Editorial addition", and no label
was renamed.

- `exact_logarithmic_degree.tex`:
  - an unnumbered `ednote` environment (no numbering shifts);
  - end of Section 1.1: the Hahn–Fuchsian package
    `../Hahn_Fuchsian_Resonance_Analytic_Normalization/`, filed after this
    article's snapshot, answers the homogeneous half of the first question at
    depth 0 for first-order real-spectrum systems (`dim ker B^{d+1}`, its
    `thm:logs`; `thm:ancestry`); this article is scalar, depth `n >= 1`, with
    forcing; no overlap in hypotheses;
  - Section 1.3: Lemmas `lem:primitive`, `lem:moments`, `lem:functional`,
    Proposition `prop:split`, `eq:old-reduction` and `eq:M0-finite` restate
    the predecessor's `thm:residue`, `thm:moments`, `lem:functional`,
    `thm:euler-split`, `thm:fredholm` and `thm:cutoff`; `Res∘δ = 0` is the
    lower-block form of the canonical volume's `plt:thm:ext-tower-strict`;
  - after the proof of `thm:realization`: the predecessor's Jordan-shift
    family (`thm:sharp-matrix`) is the case `q_1 = 1` of `thm:pencil` (single
    Jordan block, Smith exponents `(0,…,0,s)`), whose coefficients `c_k` and
    `C_s` are reproduced exactly (checked for `s <= 6` on filing);
  - Section 12.2: by the predecessor's `thm:promotion`, for `T`-independent
    forcing `thm:smith-degree` classifies all solutions in `H_{n+1}`, not only
    those in `H_n[T]`;
  - Section 13 (further questions): six of its questions are the predecessor's
    Section 11 questions, named; the matrix-systems one is partly answered at
    depth 0 by the Hahn–Fuchsian package;
  - a bibliography entry `ed:hfr`, after the delivered ones.
- `exact_logarithmic_degree.pdf`: rebuilt with three pdfLaTeX passes (30
  pages, was 29; no errors, undefined references, LaTeX warnings, multiply
  defined labels, duplicate destinations, overfull or underfull boxes; every
  font Type 1).
- `notes/validation.json`: `pdf_pages`, `pdf_bytes`, `tex_bytes`,
  `tex_source_whitespace_words`, `checksums.pdf_sha256` and
  `checksums.tex_sha256` recomputed for the filed source and PDF (they match
  them), and an `editorial_rebuild` field added recording the delivered
  values; the other fields describe the delivered build. Any later rebuild
  makes the PDF digest stale, since pdfTeX embeds the build date.
- `verification/verify.py`, `verification/operator_check.py`: `--output-dir`
  (default `rerun/`) and `--overwrite-recorded`; JSON written with LF on every
  platform (the delivered programs always rewrote `verification/` and wrote
  CRLF on Windows). A rerun on a copy reproduced both recorded JSON files byte
  for byte (1,383 assertions; 192 column checks); `verification/` is
  unchanged.
- `notes/repository_provenance.json` is kept as delivered. Its
  `target_source_lines` `[1026, 1041]` are lines of the pinned snapshot of
  `../Residue_Obstructions_Logarithmic_Depth_Promotion/residue_fredholm.tex`;
  after the editorial passes of 2026-09-29 they are lines 1035–1063 (the
  first question at 1039–1042, the second at 1052–1055, each followed by an
  editorial note that now records this package).
- `README.md`: this section, the ledger and `notes/validation.json`
  sentences, and the note under "Exact verification". (`build.sh` leaves
  `build-pass-*.log` files in the package root; they are ignored.)

# All Fixed Order Asymptotics for Total Kostka Sums (OEIS A104779, A321652, A068313)

**The sum of all entries of the Kostka matrix: a shifted-involution
expansion `a_n = C Σ_{s≤S} H_s I_{n−s} + O(I_n n^{−(S+1)/2})` with
`C = Π_{j≥2}(1 − 1/j!)^{−1}`, rationally certified 40-digit constants, a
controlled Lambert-W/Newton inverse with two-ceiling thresholds, the full
nonunit margin profile in total variation, factorial-scale expansions for the
rectangular companions A321652 and A068313, and an exact dominant/alternating
sector decomposition.**

A single-source report: bundle Report 237 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The title page and the
PDF author field read "Report 237"; the manuscript names no person, tool or
addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *All Fixed Order Asymptotics for Total Kostka Sums* ("Report 237", 5 October 2026) | `Report237.zip` (633,646 bytes, 33 files, wrapper `Report237/`; `article.tex`, 55 lines, with thirteen `\input` files in `sections/`, 25 pp.) | `a4186a946` | `article.tex` and `sections/*.tex` |

The package records no ProveIt commit, so no pin is recorded. It is a
separate report, not a Part of `a138178-symmetric-packed-matrices`
(different transform and constants, two rectangular sequences outside that
report's scope; see the relation section).

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. **Trust boundary:** the exact
identities (2.2) and (9.1) are imported from Schwob's arXiv version 1
(not read by the write; checked by the write's own finite computations for
`n ≤ 11`); every asymptotic statement has a conventional proof in the text.

## What the report proves

`a_n` (A104779) is the total of the Kostka matrix, equivalently the number of
symmetric nonnegative integer matrices without zero rows whose row sums are
weakly decreasing (A178718 is its OEIS duplicate); `b_n` (A321652) and `c_n`
(A068313) are the rectangular nonnegative and binary analogues; `I_n` are the
involution numbers, `t = n^{−1/2}`.

- **Theorem 1.1:** for every fixed `S`, `a_n = C Σ_{s≤S} H_s I_{n−s} +
  O_S(I_n n^{−(S+1)/2})` with nonnegative computable `H_s`, `H_0 = 1`,
  `H_1 = H_2 = 0`; `a_n/(C I_n) = 1 + H_3 n^{−3/2} + (H_4 − 3H_3/2) n^{−2} +
  …`, `a_n ~ (C/√2)(n/e)^{n/2} e^{√n − 1/4}`. The proof: a positive global
  support majorant (3.3), (3.6) and analytic stabilization (Lemma 3.2).
- Proposition 4.1 and Section 4.3: proved tail bounds and 40-digit rational
  interval certificates for `C, H_3, …, H_6`; closed forms (4.5)–(4.8).
- Proposition 5.1 and (5.6)–(5.12): the involution saddle at every fixed
  order with rational coefficients; Section 6: `a_n` through `n^{−3}` in three
  normalizations.
- Proposition 7.1 and **Theorem 7.2:** a Lambert-W seed, Newton iterates,
  explicit inverse terms (7.8)–(7.10), and two-ceiling threshold enclosures.
- **Theorem 8.1:** the nonunit margin profile converges in total variation to
  independent geometric multiplicities, `d_TV = (2H_3/C) n^{−3/2} + O(n^{−2})`.
- **Theorem 9.1:** `b_n, c_n = C² Σ J_s^± (n−s)! + O(n! n^{−S−1})`, opposite
  first corrections `±2η_2² n^{−2}`, and a matrix counted by `b_n` is binary
  with probability `1 − 4η_2² n^{−2} + O(n^{−3})`.
- **Theorem A.1:** an exact half-axis split `a_n = 𝒜_n^+ + (−1)^n 𝒜_n^−` with
  separate fixed-order expansions; `𝒜_n^−/𝒜_n^+ = e^{−2√n}(1 − 7/(12√n) +
  49/(288n) + …)`.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

Schwob's identities, the involution saddle (Moser–Wyman; Bornemann's
display), and the parabolic-cylinder sectors (DLMF, Olver) are prior. No
global novelty; Schwob's journal version was not compared. Not claimed:
convergence of the series, uniformity in the order, optimal truncation,
complete exponential asymptotics, Stokes data or resurgence; numerical
constants or onsets in the remainders; a certified finite-input inverse;
isolation of the recessive sector by subtraction; moment convergence of the
dimension deficit; the official offset of A068313 at `n = 0`.

## The write's findings

- **The OEIS entries** (Remark 10.1): A104779 (#14, 4 September 2025, Alford
  Arnold; matrix interpretation and b-file `n = 0..39` by Ludovic Schwob),
  A178718 (#60, "Duplicate of A104779.", Wouter Meeussen; b-file `1..39`,
  equal to A104779), A321652 (#18, Gus Wiseman) and A068313 (#25, Axel
  Kohnert), offsets as the source says; no asymptotic formula and no
  conjecture in any of them. No OEIS edit.
- **Recomputed with the write's own code:** all Kostka numbers for `n ≤ 14`
  by horizontal-strip branching, hence `a_n`, and `b_n`, `c_n` through RSK and
  dual RSK (equal to the b-files); symmetric sorted-margin matrices directly
  for `n ≤ 7` and (10.1) for `n ≤ 8`; **Schwob's identities (2.2) and (9.1)
  for `n ≤ 11` by its own cycle-index code**; the square-root formula (2.4)
  against brute force for all types of size ≤ 7; **`C`, `H_3, …, H_6` twice**
  (own extraction from the product at `J = 60` and the closed forms, agreeing
  to 50 digits; all inside the printed intervals); the saddle coefficients
  (5.5), `α_j` (5.8), (5.9), (5.11), (6.1), (6.2), (6.5) symbolically and
  against exact `I_n` up to `n = 20000`; the inverse formulas (7.8)–(7.10),
  (9.16) and the Newton orders; (A.2), (A.7) by quadrature, (A.6).
- **The alternating sector is visible** (dated note at the end of Appendix
  A): for `15 ≤ n ≤ 39` the remainder of the dominant expansion alternates
  with the parity of `n`; adding `(−1)^n C B_−(n) 𝒦(−t)` removes the
  alternation.
- **Remark 7.3 (transseries volume):** growth outside `p0:def:model`; the
  seeds (7.5) and (9.15) exact instances of `p0:thm:lambert-core` (in
  `log x_0 − 1`); `ρ_K`, the Newton iterates and the explicit inverse terms
  not shown to be instances of `plt:thm:lw-template`; Theorem 7.2 and the
  exact-term recovery analogues of `p0:thm:staircase`(2) and (3).
- **Reciprocal notes** for `a138178-symmetric-packed-matrices` (its
  "Other matrix conventions" paragraph) and `a260700-parabolic-double-cosets`
  (which names A321652 and A178718) are proposed in the intake record, not
  applied.

## Further questions, and the standing rule

Section 11 (the source's five directions: effective remainders, beyond fixed
algebraic order, higher profile corrections, the cost of high order, other
matrix conventions), with a dated note under Vladimir's standing rule of
4 October 2026; added from the non-claims: a comparison with Schwob's journal
version and an independent proof of the imported identities. No claim of the
source was found false; nothing is refuted.

## Relation to the repository

Before batch 113 the repository named A321652 and A178718 only in
`a260700-parabolic-double-cosets`, which cites Schwob's paper and draws no
asymptotic for them. `a138178-symmetric-packed-matrices` works on the same
involution scale for symmetric matrices without margin order and names
decreasing-margin variants as further questions; the present aggregate needs
Schwob's cycle index instead of a geometric transform. No shared result. No
Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `tks:`: the 123 delivered labels, prefixed
before anything cited them (82 references updated: 64 `\eqref`, 18 `\ref`),
and the write's three (`tks:sec:provenance`, `tks:rem:transseries`,
`tks:rem:oeis`); 126 in all. The write's remarks are the last statements of
their sections and its additions contain no numbered display, so every
number is delivered (checked against the `.aux` of a build of the delivered
text: 123 labels, 0 differences). Section 1.2 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.2 with the false readings: `A` (threshold) and `𝒜_n^σ`; `B` (`B(n)` versus
the envelope constant of (7.11)); `C`; `F`, `G`; `H`, `h`; `J`, `K`; `L`,
`ℓ`; `M`, `P`; `q` (`q_ρ` versus `q_n = I_{n−3}/I_n`), `r`, `R`; `ρ` (cycle
type versus the model root `ρ_K`), `s`, `σ`; `t`, `T`; `α` (`α_ν` versus
`α_j`), `γ`, `δ`; `D`, `W`, `N`.

## The write's additions

The status note after the abstract, Section 1.2 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 7.3 and
10.1, the dated notes in Sections 4.3, 10 and 11 and at the end of Appendix A,
the label prefixes, the bibliography entry `TSvol`, the `\file` macro and
`writenote` environment, and one preamble line (`etoolbox`, a ragged-right
bibliography, which removes the delivered build's one underfull line).
Everything else is delivered text.

## Files

```text
README.md                        this guide (replaces the delivered README.md)
COMPUTATION.md                   the source's account of its finite computations and reproduction
SOURCES.md                       the source's public sources and attribution boundary
article.tex                      the report's main file (delivered, written)
article.pdf                      compiled report, 29 pages
code/build.py                    delivered root builder: manifest, receipts, pdfLaTeX, deterministic ZIP
code/certify_constants.py        rational interval certificates for C and H_3..H_6 (J = 70)
code/common.py                   shared bounded helpers
code/diagnostics.py              floating diagnostics against exact counts
code/exact_counts.py             exact a_n, b_n, c_n (n <= 20) by the cycle index and an independent matrix recursion
code/guard_tests.py              input, path and manifest guard tests
code/reproduce_zip.py            verifier that rebuilds the delivered ZIP
code/sector_diagnostics.py       floating diagnostics of the two sectors
code/symbolic_coefficients.py    SymPy checks of the saddle, conversion, shift and inverse formulas
data/constant_receipt.json       frozen receipt of certify_constants.py (delivered code/)
data/count_receipt.json          frozen receipt of exact_counts.py (delivered code/)
data/guard_receipt.json          frozen receipt of guard_tests.py (delivered code/)
data/requirements.txt            mpmath 1.3.0 and SymPy 1.14.0
data/symbolic_receipt.json       frozen receipt of symbolic_coefficients.py (delivered code/)
sections/01_results.tex          Section 1 (written)
sections/02_identity.tex         Section 2 (labels prefixed)
sections/03_support.tex          Section 3 (labels prefixed)
sections/04_constants.tex        Section 4 (written)
sections/05_involutions.tex      Section 5 (labels prefixed)
sections/06_expansions.tex       Section 6 (labels prefixed)
sections/07_inverse.tex          Section 7 (written)
sections/08_margins.tex          Section 8 (labels prefixed)
sections/09_companions.tex       Section 9 (labels prefixed)
sections/10_computation.tex      Section 10 (written)
sections/11_outlook.tex          Section 11 (written)
sections/12_references.tex       bibliography (written)
sections/12_sectors.tex          Appendix A (written)
```

Every file except `README.md`, `article.tex`, `article.pdf` and
`sections/*.tex` is byte-identical to its delivery (the root `build.py` moved
to `code/`, the receipts and requirements to `data/`). Not shipped
(retrievable from `60f54ea06`): the delivered `Report237.pdf` (25 pages),
`MANIFEST.sha256` (32 entries, all verified at the write) and the delivered
`README.md` (replaced by this guide).

```sh
git show 60f54ea06:docs/incoming/Report237.zip > <scratch>/r237.zip
```

**Delivered text that names the delivery layout.** `COMPUTATION.md`,
`SOURCES.md` and Section 10 describe the delivered archive (root `build.py`,
receipts under `code/`, the manifest; a dated note at the end of Section 10
says what is shipped). `code/build.py` and `code/reproduce_zip.py` expect that
layout and the manifest, so they run only in a re-extracted archive.

**Third-party data.** `data/count_receipt.json` and the programs contain OEIS
terms of A104779, A321652 and A068313 (CC BY-SA 4.0,
https://oeis.org/LICENSE). No third-party paper is shipped.

## Rerunning the checks (on scratch copies)

The checkers write their receipts to standard output. From this directory
(Git Bash):

```sh
T=$(mktemp -d); cp -r code data "$T/"; D=$(cygpath -m "$PWD/data"); cd "$T"
for f in exact_counts:count certify_constants:constant symbolic_coefficients:symbolic; do
  py -B code/${f%%:*}.py > ${f##*:}.json        # repeat with py -B -O; SymPy 1.14.0, mpmath 1.3.0
done
py -c "import json,sys; D=sys.argv[1]
for k in ['count','constant','symbolic']: print(k, json.load(open(k+'.json'))==json.load(open(D+'/'+k+'_receipt.json')))" "$D"
```

At the write (7 October 2026, Windows, Python 3.14.4) all three receipts, in
both modes, equalled the shipped ones as JSON (Windows writes CRLF line ends,
so the bytes differ). `code/guard_tests.py` stops on Windows with "backslash
output components are forbidden", a path test, not a mathematical failure.
`diagnostics.py` and `sector_diagnostics.py` ran. The builder and the ZIP
verifier were not run.

## Build

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr, hyperref,
etoolbox). In a scratch copy:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from these files with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 29 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no
overfull or underfull boxes. The delivered text gives 25 pages and one
underfull line in the bibliography.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 237 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A104779, A178718, A321652, A068313;
  Schwob (arXiv:2506.04007v1; Adv. Appl. Math. 173, 2026); Moser–Wyman (1955,
  1956); Bornemann (arXiv:2306.03798v5); DLMF §12.5, §12.10(v); Olver (1959);
  and the repository's transseries volume (added by the write).

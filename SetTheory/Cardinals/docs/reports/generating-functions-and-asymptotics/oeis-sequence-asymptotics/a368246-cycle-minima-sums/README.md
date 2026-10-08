# Record Sum Diagonal Expansions and Integer Inverses (OEIS A368246)

**Permutations whose cycle minima (equivalently, record positions) sum to
`n`: a fixed-order expansion of `b_n = a_n/(n−1)!` with constant `e^{−γ}`, no
`n^{−1}` term and every algebraic correction oscillatory with mean zero (via
the rooted-tree identity `T(s e^{−s}) = s`), explicit terms through `n^{−3}`,
the delayed singularities at `±i`, the natural boundary, and a two-ceiling
integer inverse with finite Newton centres. Kotěšovec's conjecture in A368246
is proved as posted.**

A single-source report: bundle Report 234 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The title page and the
PDF author field read "Report 234"; the manuscript names no person, tool or
addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Record Sum Diagonal Expansions and Integer Inverses* ("Report 234", 5 October 2026) | `Report234.zip` (648,517 bytes, 24 files (the write said 25; corrected by the independent check), wrapper `Report234/`; `article.tex`, 67 lines, with eleven `\input` files in `sections/`, 29 pp.) | `a4186a946` | `article.tex` and `sections/*.tex` |

The package records no ProveIt commit, so no pin is recorded (its
`SOURCES.md` names five reports of this collection and four blob hashes, all
in the repository's history).

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. Every theorem has a conventional proof in
the text.

## What the report proves

`a_n` (A368246) counts permutations of `[n]` whose cycle minima sum to `n`
(equally, whose record positions sum to `n`); `b_n = a_n/(n−1)! =
[z^{n−1}] Π_{j≥1}(1 + z^{j+1}/j)`, `A = e^{−γ}`, `ω = e^{2πi/3}`.

- Proposition 2.1: the counting polynomial `Π (k−1+z^k)` for both statistics,
  the exact shift `m = n−1`, and the global bound (2.4); Section 2.3: the
  leading constant already follows from the local limit theorem of Giuliano,
  Szewczak and Weber (2013).
- **Theorem 1.1:** for every fixed `K`, `b_n = A + Σ_{j=2}^{K} P_j(n, log n)/n^j
  + O((1+log n)^{K−1}/n^{K+1})`, each `P_j` a polynomial of degree at most
  `j−2` in `log n` with coefficients periodic of period dividing
  `lcm(2,…,j)` and mean zero: no `n^{−1}` term and no smooth correction at
  any order. The reason is (4.5), `Σ r^{r−1}s^{r−1}e^{−rs}/r! = 1`.
- **Theorem 1.2:** `b_n = A + (−1)^n/n² + [(−1)^n(8 − 2γ − 2 log n) +
  6 Re(C_ω ω^{1−n})]/n³ + O((1+log n)²/n⁴)` with the Gamma product `C_ω`
  (1.3).
- Sections 3–7: a uniformly differentiated tail, Gamma products at the roots
  (Proposition 5.1), the natural boundary (Corollary 5.2), the delayed zeros at
  `±i` (first contribution `256 Re(Q_i i^{−m}) m^{−5}`), a global Fourier
  remainder (Lemma 6.1) and exact coefficient transfer.
- **Theorems 9.1 and 9.2:** for the explicit real model `A_K = Γ·B_K`, a
  two-ceiling envelope `⌈r_K − δ_K⌉ ≤ ν(y) ≤ ⌈r_K + δ_K⌉`, a Lambert coordinate
  `X(log X − 1) = log y + γ − ½ log 2π`, `r_K = X + ½ + O(1/(X log X))`, and
  `⌈log₂(K+2)⌉` Newton steps reaching every fixed order.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The counting polynomial (Louchard), the shifted product, the constant
`e^{−γ}` (Giuliano–Szewczak–Weber), Gamma grouping and the hybrid method
(Flajolet–Fusy–Gourdon–Panario–Pouyanne) are prior; the refinements were not
found in the inspected sources, a bounded observation. Not claimed:
convergence of the root-of-unity transseries or uniformity in `K`; effective
constants or onsets; a threshold certificate from rounding a model root;
interval certification of the Gamma amplitudes; an implementation of every
higher `P_j`; formal verification, peer review, worldwide priority.

## The write's findings

- **The OEIS entry** (Remark 11.1): the source could not fetch A368246 (HTTP
  403); the write read revision #22 (4 January 2024, Alois P. Heinz; b-file by
  Heinz, n = 0..451). Its formula "a(n) ~ c * (n-1)!, where c = 0.561459...,
  conjecture: c = exp(-gamma) …", by **Václav Kotěšovec (29 December 2023),
  is still posted as a conjecture and is proved as posted**: Theorem 1.1 gives
  `b_n = A + O(n^{−2})`, and it already followed from Theorem 2.1 of
  Giuliano–Szewczak–Weber (arXiv:1309.1578v1, 2013, read by the write: its
  model is that of Section 2). A143946 (#38, Emeric Deutsch) has the row
  polynomial as stated. All 452 b-file terms equal the write's computation.
  No OEIS edit.
- **Recomputed with the write's own code:** `a_n` for `n ≤ 451`; the shifted
  product exactly for `n ≤ 61`; both statistics on every permutation for
  `n ≤ 8` (equal distributions); `b_n` for `n ≤ 4001` in 80-digit fixed point:
  the remainder of Theorem 1.2 times `n⁴/(1+log n)²` is at most 5.52 in
  absolute value for `200 ≤ n ≤ 4001`; `C_ω` and `Q_i` by the Gamma products
  and by extrapolated partial products; `F(−1) = 1`, the slope `S`, the sum
  `½`; the tree cancellation to degree 40 and the leading filtered terms for
  `q ≤ 14`; the jet (8.5), the transfer identities (8.6), (8.7), the shift to
  (8.8), the constants 3 and 256; (9.14)–(9.16) and the Newton convergence for
  `K = 3`; the constant-shift remark of Section 12 (numerically).
- **The printed decimal** (dated note after Theorem 1.2): the imaginary part
  of `C_ω` is printed rounded (`…33151`; truncation `…33150`).
- **Remark 9.3 (transseries volume):** growth outside `p0:def:model`; the
  Lambert coordinate `X` is an exact instance of `p0:thm:lambert-core` (in
  `log X − 1`); the model root and the Newton iterates are not shown to be
  instances of `plt:thm:lw-template`; `A_K` is not an admissible
  interpolation, so Theorems 9.1 and 9.2 are analogues of
  `p0:thm:staircase`(2), not instances.

## Further questions, and the standing rule

Section 12 (the source's four questions: effective constants and onset,
certified higher amplitudes, general exponent patterns, large order), with a
dated note under Vladimir's standing rule of 4 October 2026; added from the
non-claims: interval enclosures of the Gamma amplitudes and an implementation
of the higher `P_j`. No claim of the source was found false; Kotěšovec's
conjecture is proved. (The independent check qualified the note's word
"proved" for the constant-shift observation: see below.)

## Independent check of the write (7 October 2026)

An independent adversarial check of the batch-113 write (`f24d4b02b`) used
its own code. It read A368246 (#22), A143946 (#38) and A080130 again; the
quotations of Remark 11.1 are verbatim.

- **Checked hardest: Kotěšovec's conjecture, as posted, is proved.**
  - GSW's Theorem 2.1 was read in arXiv:1309.1578v1 (fetched again, same
    SHA-256). It holds for every integer `κ_n` with `κ_n/n → x > 0`, with
    the model of Section 2.3.
  - The identity `n P(T_n = n) = b_n` was verified exactly for `n ≤ 30`.
    With `κ_n = n` and `ρ(1) = 1` it gives `a_n ~ e^{−γ}(n−1)!`, as does
    Theorem 1.1.
  - One exact integer evaluation of (2.1) to `N = 2000` reproduces all 452
    b-file terms.
  - Brute force over all permutations with `n ≤ 8` confirms both statistics
    and the equality of their distributions.
  - With exact `b_n`, the Theorem 1.2 remainder times `n⁴/(1+log n)²` is
    0.650, −5.517, −3.998, 0.295, −2.616 at n = 100, 200, 500, 1000, 2000.
    It is at most 5.5171 in absolute value for 200 ≤ n ≤ 2000, as the
    write found.
- **Also confirmed.**
  - `C_ω` (Gamma product, 50 digits) and the dated note on its printed digits.
  - `Q_i` against partial products, and `S = 2 log 2 + 1 − ζ(2)`.
  - Remark 9.3 against the volume.
  - The four `SOURCES.md` blobs (two current; the other two in `3412ae074`
    and `a4198a037`).
  - The byte identity of the staged files and the README listing.
  - The numbering: 104 delivered labels, 0 differences against the `.aux` of
    a build of the placed text.
- **Corrected by a bracketed dated note:** the archive has 24 files, not 25.
  This is fixed in Section 1.4 and in the table above.
- **Qualified by a bracketed dated note (Section 12):** the constant-shift
  observation is derived, not proved.
  - The text computes the positive sector for every `d`.
  - The transfer of Sections 3–7 is written only for `d = 1`. For other `d`
    the factor `1 + z^{1+d}` vanishes at the `(d+1)`-th roots of −1, so the
    adaptation looks routine but has not been carried out.
  - The check's own numbers agree: `m(b^{(d)}_m − A)/(A(1−d))` at m = 3000
    is 0.99705 (d = 0), 1.00176 (d = 2) and 1.0044 (d = 3).

The check is recorded at the end of Section 1.4.

## Relation to the repository

No other file of the repository names A368246 or A143946. The five reports
that `SOURCES.md` inspected as possible duplicates
(`a039831-two-fourier-peaks`, `a372395-acyclic-orientation-partitions`,
`a279619-level-seven-gamma-constant`,
`a238016-restricted-partitions-cubic-boundary`,
`a189281-path-forest-expansions`) treat other models. No shared result, so no
reciprocal note. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `cms:`: the 104 delivered labels, prefixed before
anything cited them (102 references updated: 75 `\eqref`, 27 `\ref`), and
the write's three (`cms:sec:provenance`, `cms:rem:transseries`,
`cms:rem:oeis`); 107 in all. The write's remarks are the last statements of
their sections and its additions contain no numbered display, so every number
is delivered (checked against the `.aux` of a build of the delivered text: 104
labels, 0 differences). Section 1.4 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.4 with the false readings: `A`/`A_K`; `B` (the tree series `B_q(s)` and the
real model `B_K(x)`: `B_2(s)` and `B_2(x)` are unrelated); `C`, `D`; `d`, `s`;
`F`, `f_{K,y}`; `G`, `G_n`; `H`; `L`, `𝓛`, `M`, `m`; `P`, `Q`; `r`, `q`, `h`;
`T` (tree function, random sum, Taylor polynomial); `t`, `ν`, `X`.

## The write's additions

The status note after the abstract, the dated note after Theorem 1.2, Section
1.4 (provenance, sources read, checks, relation, collected non-claims, reading
conventions), Remarks 9.3 and 11.1, the dated notes at the ends of Sections 10
and 12, the label prefixes, the bibliography entry `TSvol`, and the `\file`
macro and `writenote` environment. Everything else is delivered text.

## Files

```text
README.md                    this guide (replaces the delivered README.md)
SOURCES.md                   the source's ledger: sources, retrieval limits, bounded duplicate checks
article.tex                  the report's main file (delivered, written)
article.pdf                  compiled report, 33 pages
code/build.py                delivered root builder: manifest check, receipts, pdfLaTeX, deterministic ZIP
code/checks.py               the 175-check arithmetic receipt (exact, symbolic, 80-110-digit numerics)
code/guard_tests.py          64 input, path and manifest guard tests
code/record_sum.py           CLI: exact diagonal, brute force, root amplitudes, Newton models, Decimal bounds
code/reproduce_zip.py        verifier that rebuilds the delivered ZIP twice
data/guard_receipt.json      frozen guard-test receipt (delivered code/guard_receipt.json)
data/receipt.json            frozen arithmetic receipt (delivered code/receipt.json)
data/requirements.txt        mpmath 1.3.0 and SymPy 1.14.0
sections/01_results.tex      Section 1 (written)
sections/02_counting.tex     Section 2 (labels prefixed)
sections/03_tail.tex         Section 3 (labels prefixed)
sections/04_positive.tex     Section 4 (labels prefixed)
sections/05_roots.tex        Section 5 (labels prefixed)
sections/06_global.tex       Section 6 (labels prefixed)
sections/07_transfer.tex     Section 7 (labels prefixed)
sections/08_explicit.tex     Section 8 (labels prefixed)
sections/09_inverse.tex      Section 9 (written)
sections/10_reproduction.tex Section 10 (written)
sections/11_sources.tex      Sections 11-12 and the bibliography (written)
```

Every file except `README.md`, `article.tex`, `article.pdf` and
`sections/*.tex` is byte-identical to its delivery (the root `build.py` moved
to `code/`, the receipts and requirements to `data/`). Not shipped
(retrievable from `60f54ea06`): the delivered `Report234.pdf` (29 pages),
`MANIFEST.sha256` (23 entries, all verified at the write) and the delivered
`README.md` (replaced by this guide).

```sh
git show 60f54ea06:docs/incoming/Report234.zip > <scratch>/r234.zip
```

**Delivered text that names the delivery layout.** Section 10 and
`SOURCES.md` describe the delivered archive (root `build.py`, receipts under
`code/`, the manifest; a dated note at the end of Section 10 says what is
shipped). `code/build.py` and `code/reproduce_zip.py` expect that layout and
the manifest, so they run only in a re-extracted archive.

**Third-party data.** `data/receipt.json` and `code/checks.py` contain OEIS
terms of A368246 (CC BY-SA 4.0, https://oeis.org/LICENSE). No third-party
paper is shipped.

## Rerunning the checks (on scratch copies)

`code/checks.py` writes its receipt to standard output. From this directory
(Git Bash):

```sh
T=$(mktemp -d); cp -r code data "$T/"; D=$(cygpath -m "$PWD/data"); cd "$T"
py -B code/checks.py > receipt_normal.json && py -B -O code/checks.py > receipt_optimized.json   # about 1 min
py -c "import json,sys; D=sys.argv[1]; r=json.load(open(D+'/receipt.json')); s=lambda d:{k:v for k,v in d.items() if k!='toolchain'}
for f in ['receipt_normal.json','receipt_optimized.json']: print(f, s(json.load(open(f)))==s(r))" "$D"
py -B code/record_sum.py inverse --log-y 1000 --order 3
```

At the write (7 October 2026, Windows, Python 3.14.4, SymPy 1.14.0, mpmath
1.3.0) both receipts equalled `data/receipt.json` apart from the recorded
toolchain (Python 3.14.4 against 3.12.14). `code/guard_tests.py` stops on
Windows at "file path guard 5" (a path with forward slashes and a `..`
component), not a mathematical failure. The builder and the ZIP verifier
were not run.

## Build

pdfLaTeX (fontenc, lmodern, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, microtype, xcolor, hyperref, enumitem, fancyhdr).
In a scratch copy:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from these files with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 33 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no
overfull or underfull boxes. The delivered text gives 29 pages, equally clean.
(MiKTeX prints 684 pdfTeX notices of duplicate font-map entries, both in the
delivered and in the written build. These are not LaTeX warnings.) The
independent check rebuilt the PDF on 7 October 2026, three passes: 33 pages,
equally clean, label numbers unchanged.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 234 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A368246, A143946; Kortchemski (JCTA
  2009); Louchard (OJAC 2014); Giuliano–Szewczak–Weber (arXiv:1309.1578, read
  by the write); de la Bretèche–Tenenbaum (arXiv:2012.00528v4);
  Flajolet–Fusy–Gourdon–Panario–Pouyanne (EJC 2006); and the repository's
  transseries volume (added by the write).

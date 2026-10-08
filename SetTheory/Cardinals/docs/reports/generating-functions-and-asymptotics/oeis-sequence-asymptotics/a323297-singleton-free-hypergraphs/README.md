# All Order Asymptotics for Hypergraphs without Singleton Intersections (OEIS A323297, A323296)

**Labelled 3-uniform hypergraphs in which no two edges meet in exactly one
vertex: an explicit exact-saddle expansion to every fixed order, a reversed
logarithmic inverse with a fine exact-saddle refinement and two-ceiling
brackets, a sharp product-Poisson total-variation constant for the isolates
and the two tetrahedral component types, rare-deletion probabilities by saddle
shift, and two independent Gaussian scales (component count `√n/r`, edge
defect `r²/√3`).**

A single-source report: bundle Report 240 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. The title page and the
PDF author field read "Report 240"; the manuscript names no person, tool or
addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *All Order Asymptotics for Hypergraphs without Singleton Intersections* ("Report 240", 5 October 2026) | `Report240.zip` (601,277 bytes, 30 files, wrapper `Report240/`; `article.tex`, 52 lines, with twelve `\input` files in `sections/`, 21 pp.) | `a4186a946` | `article.tex` and `sections/*.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. Every theorem has a conventional proof in
the text; the component classification and the generating functions agree
with Howroyd's OEIS formulas (2019).

## What the report proves

`A_n` (A323297) counts admissible hypergraphs on `[n]`, `B_n` (A323296) those
without isolated vertices; components are single edges, pair-stars and two
tetrahedral types, `C(z) = z − z²/2 − z³/3 + 5z⁴/24 + z²e^z/2`, `r` the exact
saddle `DC(r) = n` (`r ~ log n`), `b = D²C(r) ~ nr`.

- Proposition 1.1 and (1.4): the component classification
  (`c_4 = 11`, `c_m = C(m,2)` for `m ≥ 5`) and the exact defect identity
  `E + 2K − n = S + T_3 + 2T_4`.
- Lemma 2.2: full-arc Fourier domination. **Theorem 3.1:** an explicit finite
  rule (3.1) for every fixed saddle correction, relative remainder
  `O_J((r/n)^{J+1})`, with `E_1`, `E_2` displayed.
- **Theorems 4.1 and 4.2:** rounding-safe inverse brackets at the exact-saddle
  scale and the reversed logarithmic expansion
  `x = (y/L){1 + (2ℓ+1)/L + …}` through three corrections, with a recursion
  for every order and a Newton refinement.
- **Theorem 5.1:** a globally summable likelihood expansion for
  `X = (S, T_3, T_4)` and `d_TV ~ (10/3) φ(1) r³/n`.
- **Theorem 6.1:** fixed-polynomial deletion by saddle shift, e.g.
  `B_n/A_n ~ e^{−r}` with two correction terms (6.7) and the
  no-tetrahedron probability (6.5)–(6.6).
- **Theorems 7.1 and 8.1:** a projected Gaussian characteristic law on two
  scales and a mixed Gaussian–Poisson test bound `O(r³/√n)`; Corollary 8.2:
  defect moments. **Theorem 9.1:** everything transfers to `B_n` at its own
  saddle.

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The classification and the generating functions are Howroyd's (2019), the
connected formula Wiseman's; Hayman's method with Harris–Schoenfeld and
Odlyzko–Richmond and the conditioning tools of Arratia–Tavaré are prior; the
extremal question of Keevash–Mubayi–Wilson is different. No priority claim.
Not claimed: convergence as `J → ∞`; numerical `K_J` or onsets; a threshold
certificate from rounding; a canonical smooth interpolation; relative
accuracy from the coarse inverse; total-variation convergence of a discrete
count to a continuous law; growing deletions; certified diagnostics.

## The write's findings

- **The OEIS entries** (Remark 10.1): A323297 (#14, Gus Wiseman; e.g.f. by
  Andrew Howroyd, 18 August 2019; b-file `n = 0..200`), A323296 (#15,
  Wiseman; Howroyd's component comment and e.g.f.; b-file `0..200`) and
  A323294 (#34, Wiseman; `a(n) = C(n,2)` for `n ≥ 5` by Wiseman; b-file
  `0..1000`) quoted; the component decomposition is stated in A323296, while
  A323297 carries the e.g.f. No asymptotic formula and no conjecture in any.
  No OEIS edit.
- **Recomputed with the write's own code:** `A_n`, `B_n` for `n ≤ 1200` (all
  201 b-file terms of A323297 and A323296, and all 1001 connected counts of
  A323294), the second exact route for `n ≤ 60`, **every admissible edge set
  for `n ≤ 8`** (counts, connected counts and the defect identity on each
  object); `E_1`, `E_2`, `DE_1` from the contraction rule; the recurrence
  (2.2); the identity behind (7.3); **the reversion (4.10)–(4.11) and all
  three coefficients of (4.8)**; the remainders of (3.2) for `J ≤ 2`, the
  deletion formulas (6.5) and (6.7) and `log A_n − n g(r) = O(r⁵)` against
  exact counts for `n = 100…1200`; **every entry of the diagnostics table of
  Section 10.2** from the exact conditioning formula (all correct roundings;
  truncations in a dated note); `E|1 − Z²| = 4φ(1)`.
- **Remark 4.3 (transseries volume):** growth outside `p0:def:model`; the
  reduced equation (4.10) for `r` is literally
  `plt:def:lw-monomial-log-datum` (slope 1, logarithmic coefficient 4), so
  (4.11) is an exact formal instance of `plt:thm:lw-template` and (4.8)
  follows by the substitution `x = y/g(r)`; the exact-saddle inverse lies
  below every order of the template's chart and is proved directly;
  Theorem 4.1 is an analogue of `p0:thm:staircase`(2).

## Further questions, and the standing rule

Section 11 (the source's six directions: effective constants and certified
inversion, higher likelihood corrections, an optimal hybrid error, moderate
and large edge deviations, larger uniformity, growing deletions), with a
dated note under Vladimir's standing rule of 4 October 2026; added from the
non-claims: explicit constants for Theorem 4.1 and certified diagnostics. No
claim of the source was found false; nothing is refuted.

## Relation to the repository

No other file of the repository names A323297, A323296 or A323294, and no
report of the collection treats intersection-restricted hypergraphs. No
shared result, so no reciprocal note. No Lean or Rocq development treats
these sequences.

## Labels and numbering

All labels carry the prefix `sfh:`: the 83 delivered labels, prefixed before
anything cited them (86 references updated: 71 `\eqref`, 15 `\ref`), and the
write's three (`sfh:sec:provenance`, `sfh:rem:transseries`, `sfh:rem:oeis`);
86 in all. The write's remarks are the last statements of their sections and
its additions contain no numbered display, so every number is delivered
(checked against the `.aux` of a build of the delivered text: 83 labels, 0
differences). Section 1.3 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.3 with the false readings: `A`, `B`, `b` (`A_1(G)` is not the count `A_1`);
`C`, `c` (`c = log 2`); `E` (edges versus the corrections `E_ℓ`); `K`, `L`,
`M`; `N`; `P`, `Q` (the Poisson law `Q` versus a polynomial `Q`); `R`, `r`;
`S`, `T` (the Schur complement `T` is not `T_3 + T_4`); `V`, `v`, `W`; `d`,
`δ`, `ρ`; `κ_j`, `k_j`, `ε`.

## The write's additions

The status note after the abstract, Section 1.3 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 4.3 and
10.1, the dated notes in Sections 10.2, 10.3 and 11, the label prefixes, the
bibliography entry `TSvol`, and the `\file` macro and `writenote`
environment. Everything else is delivered text.

## Files

```text
README.md                        this guide (replaces the delivered README.md)
COMPUTATION.md                   the source's computational supplement: algorithms, bounds, scope, freeze procedure
SOURCES.md                       the source's sources and attribution
article.tex                      the report's main file (delivered, written)
article.pdf                      compiled report, 26 pages
code/build.py                    delivered root builder: manifest, receipts, pdfLaTeX, deterministic ZIP
code/common.py                   shared bounded helpers
code/diagnostics.py              NONCERTIFIED floating diagnostics from exact counts and moments
code/exact_counts.py             component recurrence, exponential-sum convolution, edge-set enumeration, marked identities
code/guard_tests.py              finite input, filesystem, manifest and archive guards
code/reproduce_zip.py            replay of an actual archive in normal and optimized modes
code/symbolic_coefficients.py    Gaussian contraction rule, E1/E2, cumulant derivatives, inverse coefficients
data/count_receipt.json          frozen receipt of exact_counts.py (delivered code/)
data/diagnostic_receipt.json     frozen receipt of diagnostics.py (delivered code/)
data/guard_receipt.json          frozen receipt of guard_tests.py (delivered code/)
data/requirements.txt            mpmath 1.3.0 and SymPy 1.14.0
data/symbolic_receipt.json       frozen receipt of symbolic_coefficients.py (delivered code/)
sections/01_model.tex            Section 1 (written)
sections/02_fourier.tex          Section 2 (labels prefixed)
sections/03_coefficients.tex     Section 3 (labels prefixed)
sections/04_inverse.tex          Section 4 (written)
sections/05_likelihood.tex       Section 5 (labels prefixed)
sections/06_deletion.tex         Section 6 (labels prefixed)
sections/07_gaussian.tex         Section 7 (labels prefixed)
sections/08_hybrid.tex           Section 8 (labels prefixed)
sections/09_transfer.tex         Section 9 (labels prefixed)
sections/10_computation.tex      Section 10 (written)
sections/11_questions.tex        Section 11 (written)
sections/12_references.tex       bibliography (written)
```

Every file except `README.md`, `article.tex`, `article.pdf` and
`sections/*.tex` is byte-identical to its delivery (the root `build.py` moved
to `code/`, the receipts and requirements to `data/`). Not shipped
(retrievable from `60f54ea06`): the delivered `Report240.pdf` (21 pages),
`MANIFEST.sha256` (29 entries, all verified at the write) and the delivered
`README.md` (replaced by this guide).

```sh
git show 60f54ea06:docs/incoming/Report240.zip > <scratch>/r240.zip
```

**Delivered text that names the delivery layout.** `COMPUTATION.md` and
Section 10.3 describe the delivered archive (root `build.py`, receipts under
`code/`, the manifest; a dated note at the end of Section 10 says what is
shipped). `code/build.py` and `code/reproduce_zip.py` expect that layout and
the manifest, so they run only in a re-extracted archive.

**Third-party data.** `data/count_receipt.json` and the programs contain
OEIS terms of A323297 and A323296 (CC BY-SA 4.0, https://oeis.org/LICENSE).
No third-party paper is shipped.

## Rerunning the checks (on scratch copies)

The checkers write their receipts to standard output. From this directory
(Git Bash):

```sh
T=$(mktemp -d); cp -r code data "$T/"; D=$(cygpath -m "$PWD/data"); cd "$T"
for f in exact_counts:count symbolic_coefficients:symbolic diagnostics:diagnostic; do
  py -B code/${f%%:*}.py > ${f##*:}.json        # repeat with py -B -O; SymPy 1.14.0, mpmath 1.3.0
done
py -c "import json,sys; D=sys.argv[1]
for k in ['count','symbolic','diagnostic']: print(k, json.load(open(k+'.json'))==json.load(open(D+'/'+k+'_receipt.json')))" "$D"
```

At the write (7 October 2026, Windows, Python 3.14.4) all three receipts, in
both modes, equalled the shipped ones as JSON. `code/guard_tests.py` stops on
Windows with "backslash output components are forbidden", a path test, not a
mathematical failure. The builder and the ZIP replay were not run.

## Build

pdfLaTeX (fontenc, lmodern, microtype, geometry, amsmath, amssymb, amsthm,
mathtools, booktabs, array, longtable, xcolor, enumitem, fancyhdr, hyperref).
In a scratch copy:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from these files with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 26 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no
overfull or underfull boxes. The delivered text gives 21 pages, equally clean.

## Provenance

- Batch 113 of `docs/incoming`: bundle Report 240 (arrival `60f54ea06`),
  placed by `a4186a946`; written 7 October 2026.
- Sources cited by the report: OEIS A323297, A323296, A323294;
  Odlyzko–Richmond (Aequationes Math. 1985); Arratia–Tavaré (Adv. Math.
  1994); Keevash–Mubayi–Wilson (SIAM J. Discrete Math. 2006); and the
  repository's transseries volume (added by the write).

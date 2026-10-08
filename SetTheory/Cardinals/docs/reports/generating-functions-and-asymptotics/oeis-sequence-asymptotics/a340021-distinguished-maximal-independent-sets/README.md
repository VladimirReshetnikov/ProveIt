# Graphs with a Distinguished Maximal Independent Set (OEIS A340021)

**A uniform Burnside reduction of the unlabeled count to the expected number
of maximal cliques in `G(n, 1/2)`, every fixed algebraic order through a full
discrete Poisson carrier, exact Lambert-W switch points with logistic windows,
and finite Newton inversion with two-ceiling threshold envelopes.**

A single-source report: bundle Report 206 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`f79c9bef1` (batch 112) and written on 7 October 2026. The author line and
the PDF author field read "Report206"; the manuscript names no person, tool
or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Graphs with a distinguished maximal independent set: All fixed order expansions and inverse thresholds for A340021* ("Report206", 4 October 2026) | `Report206.zip` (496,154 bytes, 14 files, no wrapper directory; `Report206.tex`, 513 lines, 16 pp.) | `f79c9bef1` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`U_n` counts graphs on `n` vertices with a distinguished maximal independent
set (black), up to color-preserving isomorphism; `a = log 2`, `N = C(n,2)`;
`b_n = Σ_k C(n,k) 2^{−C(k,2)} (1−2^{−k})^{n−k}` is the expected number of
maximal cliques in `G(n,1/2)`, and the identity Burnside term is
`I_n = 2^N b_n/n!`.

- Section 2: the exact cycle-type formula (5) (Howroyd's program in OEIS).
- **Theorem 3.1:** `U_n = I_n (1 + O(n² 2^{−3n/8}))`, uniformly for
  `U(n,k)/I(n,k)` over `k ≤ n/4`; Corollary 3.2: total-variation and
  nontrivial-automorphism consequences.
- **Theorem 4.1:** for every fixed `R`,
  `U_n = (2^N/n!){H_R(n) + O_R(μ_0(n)(log n)^{2R}/n^R)}` with the full
  discrete carrier `H_R = Σ_{j<R} t^{−j} μ_j(t)` and an exact finite recipe
  for the polynomials `P_j`; `μ_0` is the Poisson transform of `b_n` (19)
  and `μ_1 = −(t²/2)μ_0''` (20).
- Theorem 5.1: a finite-sector expansion in powers of `1/log n` only.
- **Theorems 6.1–6.3:** the black-size law within `O((log n)²/n)` of the
  carrier law; exact switches `t_k = 2^{k+1} W((k+1)/2)` with logistic
  windows (error `O(√(log k/k))`); concentration on an adjacent pair up to
  `O((log log n/log n)^{1/3})`.
- **Theorem 7.1:** finitely many explicit Newton steps from
  `z_0 = x + d` give `⌈z_j − ε⌉ ≤ ν(Y) ≤ ⌈z_j + ε⌉` with
  `ε = O((log x)^{2R}/x^{R+1} + (log x)^{2^{j+1}}/x^{2^{j+1}−1})`; a closed
  second approximation `z_*` (39).

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The maximal-clique expectation and its growth (Bollobás–Erdős;
Fried–Kessler–Shnerb), rigidity (Erdős–Rényi), colored-graph expansions
(Wright), depoissonization (Banderier–Hwang–Ravelomanana–Zacharovas),
split graphs (Troyka) and orbit enumeration (Myrvold–Fowler) are prior; no
general new method and no worldwide priority claim. Fixed orders and sector
widths only; sector expansions give only powers of `1/log n`; slow logistic
and pair laws; existential inverse constants and onsets, no single-ceiling
rule; floating tables use a finite cutoff and certify nothing; the first
symmetry coefficient is not computed.

## The write's findings

- **The OEIS entry** (Remark 10.1): A340021 (#15, 16 February 2025, Andrew
  Howroyd, 2020) quoted. The source saw only a cached snapshot (its b-file
  request returned HTTP 403); the b-file (n = 0..40) equals the write's own
  evaluation of (5) in all 41 terms, so the twenty terms of Table 1 agree
  with the current entry. No asymptotic formula and no conjecture in the
  entry; no OEIS edit.
- **Recomputed:** brute-force canonical counts for `n ≤ 5`; the identity
  sum; `C_1, C_2, C_3, P_2, P_3`, `p_1(j)` (SymPy); the Poisson identity and
  the Charlier identity numerically; **every entry of Tables 2–4** with the
  write's own carrier implementation at 90 digits (all correct six-digit
  roundings); the closed approximation `z_*` against the stated
  `O((log x)³/x²)`.
- **Remark 7.2 (transseries volume):** growth outside `p0:def:model`; after
  `G = sqrt(2F_R/a)` the centre `z_0` agrees with the first two terms of
  `plt:thm:lw-template` for the leading monomial–logarithmic datum, but the
  Newton iterates and `z_*` are not shown to be instances (the carrier's
  lattice phase); Theorem 7.1 is an analogue of `p0:thm:staircase`(2) proved
  directly, not an instance; the switch points `t_k` are exact instances of
  `p0:thm:lambert-core` (positive branch).

## Further questions, and the standing rule

Section 11 (the source's list, with a dated note under Vladimir's standing
rule of 4 October 2026): effective inverse certification, a sharper symmetry
correction, sharper phase laws, growing orders and adaptive sectors, other
edge probabilities; added from the non-claims: interval-certified carrier
coefficients and tables, and the logistic window at moderate `k`. No claim of
the source was found false; nothing is refuted.

## Independent check of the write (7 October 2026)

An independent adversarial check of the batch-112 write (`0c4f9054d`), with
its own code, confirmed every claim of the write and added one precision.

- **OEIS.** A340021 (#15) and its b-file read again: name, comment,
  attributions (Howroyd 2020; Alcover's Mathematica, 2021), twenty displayed
  terms and b-file range `n = 0..40` as quoted; no formula line, no
  conjecture.
- **Exact.** Own evaluation of (5) = all 41 b-file terms; a literal Burnside
  sum over actual permutations (pair orbits walked, inclusion–exclusion over
  white cycles) gives `U_0…U_9`; brute-force canonical count `1,1,2,5,16,66`;
  the identity sum (1) for `n ≤ 8`; the printed `C_1…C_3`, `P_2`, `P_3`, the
  coefficients of (18) at a test point, `p_1(j)`; the Poisson (19) and
  Charlier (20) identities at `t = 7`, `50` to `10⁻¹⁰⁹`.
- **Tables.** Own carrier code at 110 digits recomputes every entry of
  Tables 2–4; all are correct six-digit roundings, including the close cases
  `1.232124998…×10⁻⁴`, `3.655745247…×10⁻⁷`, `1.613545413…×10⁻¹⁵`;
  `q_{k+1} = 0.0878674903…` as the write says; `(z_* − n)x²/(log x)³ = −0.253,
  −0.131, −0.082, −0.042`.
- **Remark 7.2** confirmed per statement (the centre `z_0` agrees with
  `X + q_0` even up to `O(1/x)`; `r_k(t_k) = 1` to `10⁻¹¹⁰`).
- **Precision** (in the check's note): besides `xurl` the write added a
  second preamble package, `array`, which Section 1.2 does not mention (this
  README does); a build of the delivered text with `array` added gives the
  same 16 pages and the same text layout, so no delivered typesetting changes.
- **Also confirmed:** the provenance (496,154 bytes, 14 files, 513 lines,
  16 pages; `MANIFEST.json` 13/13); the 10 staged files byte-identical and
  the inline tables equal to `data/tables.tex`; 54 delivered labels with
  their numbers on the check's own builds; the README listing (13 files);
  no earlier repository mention; the neighbouring reports as described; the
  three programs reproduce the shipped JSON (also `verify_exact.py` under
  `-O`).

The check is recorded in a dated note at the end of Section 1.2. Rebuilt:
20 pages (unchanged), label numbers unchanged.

## Relation to the repository

No other file of the repository names A340021. `a001425-commutative-magmas`
(batch 112) also reduces an unlabeled count to a labeled one by Burnside's
lemma, for a different object; `graph-theory/trapezohedral-minimal-dominating-sets`
and `log-concavity-and-unimodality/independence-system-thresholds` use maximal
independent sets of particular graphs. No shared result, so no reciprocal
note. No Lean or Rocq development treats this sequence.

## Labels and numbering

All labels carry the prefix `mis:`: the 54 delivered labels (50 in the text,
4 in the generated tables), prefixed before anything cited them (44
references updated: 29 `\eqref`, 15 `\ref`), the write's label for Section 1
(`mis:sec:scope`) and its three (`mis:sec:provenance`,
`mis:rem:transseries`, `mis:rem:oeis`); 58 in all. The write's remarks are the
last statements of their sections and its additions contain no numbered
display or table, so every number is delivered (checked against the `.aux` of
a build of the delivered text: 54 labels, 0 differences). Section 1.2 is the
write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.2 with the false readings: `U` (each graph counted once per orbit of its
maximal independent sets), `a`, `N`, `L`, `b_n`/`B`, `μ` (`μ_0(n)` is not
`b_n`), `P`/`p`/`C`, `y`, `k`/`K`/`m`, `W`, `D`/`d`, `s`/`t`, `q`/`r`, and the
inverse symbols `ρ_R`, `ν`, `x`, `z`.

## The write's additions

The status note after the abstract, Section 1.2 (provenance, sources read,
checks, relation, collected non-claims, reading conventions), Remarks 7.2 and
10.1, the dated notes in Sections 8, 9 and 11, the label prefixes and the label
of Section 1, the bibliography entry `TSvol`, the `\file` macro and
`writenote` environment, two preamble packages (`xurl`, which lets the long
Myrvold–Fowler URL break and so removes the delivered build's one underfull
line, and `array`), and the generated tables printed inline instead of
`\input{tables.tex}`. Everything else is delivered text.

## Files

```text
README.md                    this guide (replaces the delivered README.txt)
article.tex                  the report (delivered Report206.tex, written)
article.pdf                  compiled report, 20 pages
code/build.py                deterministic regeneration, PDF and ZIP builder
code/diagnostics.py          220-digit numerical illustrations (Tables 2-4)
code/independent_checks.py   permutation edge orbits with inclusion-exclusion, SymPy identities
code/verify_exact.py         standard-library exact verification (OEIS terms, Burnside rows, inequalities)
data/checks.json             build summary (guard cases, cross-implementation agreement)
data/diagnostics.json        output of diagnostics.py
data/exact_results.json      output of verify_exact.py
data/independent_results.json output of independent_checks.py
data/requirements.txt        SymPy 1.14.0 and mpmath 1.3.0
data/tables.tex              generated table source, printed inline in Section 8
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery (the delivered root files, moved to `code/`
and `data/`). Not shipped (retrievable from `60f54ea06`): the delivered
`Report206.pdf` (16 pages), the delivered `README.txt` (replaced by this
guide), and the pure checksum manifest `MANIFEST.json` (13 entries, verified at
the write).

```sh
git show 60f54ea06:docs/incoming/Report206.zip > <scratch>/r206.zip
```

**Delivered text that names the delivery layout.** `code/build.py` expects
the delivered flat layout (all files at the root, with `MANIFEST.json`) and
writes `Report206.zip`, so it runs only in a re-extracted archive; Section 9
of the report describes the delivered archive (a dated note there says what
is shipped).

**Third-party data.** `data/exact_results.json` and `data/tables.tex` contain
the twenty OEIS terms displayed for A340021 (CC BY-SA 4.0,
https://oeis.org/LICENSE).

## Rerunning the checks (on scratch copies)

Never run the programs in place. The three programs print JSON to standard
output and read no files. From this directory (Git Bash):

```sh
T=$(mktemp -d); cp code/*.py "$T/"; cd "$T"
py -B verify_exact.py > exact.json                 # standard library only, 2 s
py -B independent_checks.py > independent.json     # SymPy 1.14.0, about 30 s
py -B diagnostics.py > diagnostics.json            # mpmath 1.3.0, about 15 s
py -c "import json,sys; d=sys.argv[1]; [print(a, json.load(open(a))==json.load(open(d+'/'+b))) for a,b in [('exact.json','exact_results.json'),('independent.json','independent_results.json'),('diagnostics.json','diagnostics.json')]]" "$(cygpath -m "$OLDPWD/data")"
```

At the write (7 October 2026, Windows, Python 3.14.4) all three outputs
equalled the shipped JSON files, from the shipped code and from a delivered
copy (`verify_exact.py` also under `-O`, identical). The builder was not run.

## Build

pdfLaTeX (lmodern, microtype, amsmath, amssymb, amsthm, mathtools, booktabs,
longtable, geometry, hyperref, xurl, array). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (7 October 2026):
20 pages; no errors or warnings, no undefined references, no multiply
defined labels, no duplicate destinations, no overfull or underfull boxes.
The delivered text (with its `tables.tex`) gives 16 pages and one underfull
line, removed by `xurl`. Rebuilt at the independent check (7 October 2026,
pdfLaTeX ×3, with its dated note): 20 pages, the same clean log.

## Provenance

- Batch 112 of `docs/incoming`: bundle Report 206 (arrival `60f54ea06`),
  placed unprefixed by `f79c9bef1`; written 7 October 2026.
- Sources cited by the report: OEIS A340021; Bollobás–Erdős (1976);
  Fried–Kessler–Shnerb (2016); Banderier–Hwang–Ravelomanana–Zacharovas
  (2014); Erdős–Rényi (1963); Wright (1972); Myrvold–Fowler (2013); Troyka
  (2019); and the repository's transseries volume (added by the write).

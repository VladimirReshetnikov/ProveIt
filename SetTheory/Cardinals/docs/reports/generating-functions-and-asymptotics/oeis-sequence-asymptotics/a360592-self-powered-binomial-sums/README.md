# Self-Powered Binomial Sums (OEIS A360592, A360479, A360747)

**Part I: every fixed algebraic order of `a_p(n) = Σ_k (n−pk)^{pk} C(n−pk, k)`
for every fixed `p` through an exact residue-conditioned Poisson
representation, a critical resummation at `p = 1`, corrected OEIS
coefficients, sharp inactive-vertex laws for `p ≥ 2` and controlled inverses.
Part II: the globally optimal parity-conditioned binomial approximation of the
critical inactive count.**

A two-part report built from two manuscripts of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`a4186a946` (batch 113) and written on 7 October 2026. Report 230's title
block reads "Report 230" (PDF author "Research report"), Report 235's "Report
235" (PDF author "Report 235"); neither names a person, tool or addressee.

| Part | Source | Archive | Shipped as |
|---|---|---|---|
| I | *Corrected Poisson Endpoint Expansions: Critical resummation, inactive vertices, and controlled index inverses for a family of self powered binomial sums* (Report 230, 5 October 2026), the base | `Report230.zip` (630,758 bytes, 22 files, wrapper `Report230/`; `article.tex` with nine section files, 30 pp.) | `article.tex` Part I, `sections/01_overview.tex` … `09_appendix.tex` |
| II | *Optimal Positive Binomial Approximation for the Critical Inactive Count: A global total variation theorem connected to OEIS A360592* (Report 235, 5 October 2026), its `p = 1` continuation | `Report235.zip` (672,890 bytes, 28 files, wrapper `Report235/`; `article.tex` with ten section files, 23 pp.) | `article.tex` Part II, `sections/235-binomial-01_results.tex` … `09_coupling.tex` |

Neither package records a ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status.

## What the report proves

`q = p + 1`, `c_p = exp(p²/q) q^{−1/q}`, `λ = c_p n^{1/q}`; at `p = 1`,
`c = √(e/2)` and `t = n^{−1/2}`. `R_n = n − qk` is the number of inactive
vertices in a labeled directed-graph model of the summands.

**Part I** (Report 230, Sections 1–8 and Appendices A–B):

- Section 2: the formal generating function (2.1), the graph model, the exact
  Poisson identity (2.5) and the root-of-unity filter (2.7); Proposition 2.1:
  `a_p(n+1) > a_p(n)` for `n ≥ p`.
- **Theorem 3.3** (`p ≥ 2`): every fixed order of
  `a_p(n)/M_p(n)`, `M_p(n) = (1/q)(n/q)^{pn/q} e^λ`, as rational polynomials
  `C_{p,j}(c_p)` in `n^{−j/q}`; `C_{p,1} = … = C_{p,p−2} = 0`; explicit
  terms for `p = 2` through `t⁴` and `p = 3` through `t⁶`.
- **Theorem 4.1** (`p = 1`): every fixed order in `n^{−1/2}` (no odd quarter
  powers), `C_{1,1} = c/4 + 11c³/8`, explicit through `C_{1,4}`.
- **Theorems 5.1–5.2** (`p ≥ 2`): the tilted Lambert-W parameter `μ`, mean and
  variance, sharp TV constants `A√(2/π) λ^{3/2}/n` and `A√(2/(πe)) μ/n`
  against conditioned Poisson references, a weighted density expansion, all
  fixed marked orders.
- **Theorems 6.2, 6.5**, Corollary 6.3, Proposition 6.4: Newton inverses from
  an explicit Lambert core, arbitrary fixed index accuracy, a convergent local
  Lagrange series, and the two-ceiling threshold envelope.

**Part II** (Report 235, Sections 9–16 and its Appendix A):

- **Theorem 9.1:** for `p = 1`, the infimum of the TV distance from the law
  of `R_n` to all parity-conditioned binomials is
  `~ (5/8) log 2 √(2/π) μ^{3/2}/n²`, attained by an explicit law;
  asymptotically optimal parameters are characterized
  (`ν − ν_0 = (5/8)(2 log 2 − 3) μ²/n² + o(μ²/n²)`, `M − M_0 = o(√μ)`); the
  moment-matched baseline has the larger constant `(5/16)(2φ(0) + 8φ(√3))`.
- Theorem 11.2: all fixed-order marked cumulants; Theorem 11.3: an all-order
  weighted density generator; Corollary 11.4: the two Poisson TV equivalents
  at `p = 1` (Part I proves them for `p ≥ 2`); Theorem 12.1: the weighted
  cubic comparison; Theorem 13.1 and Lemma 13.2: uniform sensitivity and the
  unique Gaussian minimizer `(2 log 2 − 3, 0)`; Section 14: global
  localization including rare parity events, through an exact
  characteristic-function Jacobian; Appendix A: a bounded residue coupling for
  log-concave weights.

(Section, statement and equation numbers are those of the committed PDF;
Part II's are Report 235's plus eight.)

## What the report does not claim

Fixed `p` and fixed orders only: no secondary exponential sector, optimal
truncation, growing-`p` limit, effective inverse onset or certified constant;
the transcendental diagnostics are not interval-certified, and the `p = 3`
truncation through `t^{12}` is still about 66% wrong at `n = 10⁴`. Part I
asserts no marked law at `p = 1`. Part II optimizes only over the
parity-conditioned binomial family (no exact finite-`n` minimizer, no other
positive family, no other `p`), credits positive binomial fitting, Charlier
corrections and Hermite absolute-moment limits to the literature it names, and
calls its median step elementary `L¹` projection. No worldwide priority claim;
the OEIS comparison was made from snapshots without revision numbers.

## The write's findings

- **The OEIS entries** (Remark 7.1): A360592 (#28, 17 February 2023, Václav
  Kotešovec), A360479 (#40, 19 February 2023, Seiichi Manyama; refinement by
  Kotešovec) and A360747 (#22, 20 February 2023, Manyama; refinement by
  Kotešovec) are the current revisions, so the source compared the current
  formulas. All b-file terms (761, 636, 601) equal the write's evaluation of
  the sums. The source's transcription of the three formula lines into its
  normalization is exact (SymPy, leading factors included). **The leading
  equivalents are right; the first corrections are wrong** (an extra
  `1/(8c_p)` at `p = 1, 2`; a nonzero `n^{−1/4}` term at `p = 3`, where the
  true coefficient is 0): refuted by Theorems 3.3 and 4.1, and against the
  exact sums `(entry multiplier − a_p(n)/M_p(n))/t` is 0.10722073… at
  `n = 10^{14}` (`1/(8c)` = 0.10722048…), 0.04752092… at `10^{18}`
  (0.04752160…) and 0.01863213… at `10^{24}` (0.01863212…). No OEIS edit.
- **Recomputed with the write's own code:** every printed coefficient of both
  Parts (`D_j` against the series of `log G_r`, `C_{2,1..4}`, `C_{3,1..6}`,
  `C_{1,1..4}`, `L_2`, Part II's `ν_0`, `v_+`, `L_*`, the two log densities
  through weight five and their difference `(5/8)t(u³ − 3θtu)`, the
  hierarchy identities, the signed binomial moments, the Gaussian constants);
  the vanishing of `C_{p,1..p−2}` for `p = 4, 5`; the critical expansion
  against the exact sums to `n = 10^{10}` with the write's own `C_{1,5}`,
  `C_{1,6}` (stable residual ratio −11.35); **every printed decimal**
  (Table 1, the critical values, the four marked ratios at `n = 10⁹`, Part
  II's twelve table ratios and four hierarchy ratios, its constants). All are
  correct roundings; where a rounding differs from the truncation, dated notes
  give the truncation.
- **Remark 6.7 (transseries volume):** growth outside `p0:def:model`; the
  Lambert core and the tilt parameter `μ` are exact instances of
  `p0:thm:lambert-core` (positive branch); the Newton iterates and the
  Lagrange series are not shown to be instances of `plt:thm:lw-template` (the
  term `α x^β` lies beyond all powers in the logarithmic chart); Theorem 6.5
  is an analogue of `p0:thm:staircase`(2) and Corollary 6.3 of (3), proved
  directly.
- **Merge:** Part II's Corollary 11.4 is the `p = 1` case of Part I's
  Theorem 5.1, with the same constants. Three unlabelled Part II proofs that
  repeat Part I (the global bound (10.3), Lemma 10.2, the direct check of
  `C_1`; 49, 60 and 46 words) are printed once, in Part I, with dated notes;
  Part II's other restatements carry labels it cites and are kept with notes.

## Further questions, and the standing rule

Part I's Section 8 (effective inverse constants, moderate-size resummation,
critical marked laws, residue effects beyond algebraic order, large order and
growing parameters, sharper marked approximations, broader graph statistics)
and Part II's Section 15.3 (next-order and integer effects, larger positive
families, other parameters and moduli, effective certificates, general
deformed lattice laws, beyond fixed order), each with a dated note under
Vladimir's standing rule of 4 October 2026. Part I's critical marked-law
question is answered by Part II within the conditioned binomial family (note
there); the binomial optimization for `p ≥ 2` is open; the write adds
interval-certified values for the diagnostics. No claim of either manuscript
was found false; the OEIS refinements' first corrections are refuted.

## Relation to the repository

No other file of the repository names A360592, A360479 or A360747. Other
reports use some of the same tools for other objects: Poisson–Charlier
expansions (`a340021-distinguished-maximal-independent-sets`,
`a138178-symmetric-packed-matrices`, `a189281-path-forest-expansions`) and a
TV binomial approximation (`a182220-source-boundary`). No shared result, so
no reciprocal note. No Lean or Rocq development treats this family.

## Labels and numbering

All labels carry `spb:ep:` (Part I) or `spb:ml:` (Part II): the 229 delivered
labels (127 and 102), prefixed before anything cited them (references updated:
Part I 95 `\eqref`, 26 `\ref`; Part II 79 `\eqref`, 40 `\ref`), and the
write's five (`spb:sec:guide`, `spb:ep:part`, `spb:ml:part`,
`spb:ep:rem:transseries`, `spb:ep:rem:oeis`); 234 in all. Part I keeps every
delivered number, including its Appendices A and B; Part II continues the
section counter (Report 235's Section `k`, equation `(k.j)` and Theorem `k.j`
are `k+8`, `(k+8.j)`, `k+8.j` here) and its appendix keeps the letter A. The
write's remarks are the last statements of their sections and its displays
are unnumbered, so every number is delivered up to that shift (checked
against the `.aux` files of builds of the two delivered texts: 229 labels, 0
differences). Part II's citation key `oeis` is Part I's `oeis1` in the merged
bibliography.

## Notation

No symbol was renamed. Letters with several senses within or across the Parts
are tabulated in the Guide with the false readings: `a`, `q` (Part II's `q` is
a success probability or a modulus, never `p + 1`), `c`/`d`, `M`/`N`,
`B`/`𝓑`, `C` (Part II's Charlier `C_2(r; μ)` is Part I's `𝒞_2`, not the
coefficient `C_2(c)`), `ν`, `γ`/`θ`, `α`/`β`/`κ`, `L`/`H`, `U`/`V`/`T`,
`W`/`Z`, `ε`/`ρ`/`h`, `J`/`K`.

## The write's additions

The title block, abstract and status note, the Guide (provenance, sources
read, checks, relation, collected non-claims, reading conventions), the two
Part headers with the delivered abstracts (Report 230's with its Scope
paragraph), Remarks 6.7 and 7.1, the dated notes in Sections 1, 7, 8,
Appendix B and Sections 9–11 and 15–16, the three printed-once notes that
replace repeated proofs, the label prefixes, the counter lines between the
Parts, the merged bibliography with the entry `TSvol`, the `\file` macro and
the `writenote`, `partabstract` and `\partsource` environments, and the union
preamble (Report 235's global list spacing is not used and the running heads
are neutral). Everything else is delivered text.

## Files

```text
README.md                                   this guide (replaces Report 230's delivered README.md)
article.tex                                 the report: preamble, Guide, Part headers, merged bibliography; inputs sections/
article.pdf                                 compiled report, 61 pages
230-endpoint-SOURCES.md                     Report 230's public source guide
230-endpoint-code-README.md                 Report 230's code guide (delivered code/README.md)
235-binomial-COMPUTATION.md                 Report 235's computation guide
235-binomial-SOURCES.md                     Report 235's source notes
sections/01_overview.tex                    Part I, Section 1 (Report 230)
sections/02_exact.tex                       Part I, Section 2
sections/03_subcritical.tex                 Part I, Section 3
sections/04_critical.tex                    Part I, Section 4
sections/05_marked.tex                      Part I, Section 5
sections/06_inverse.tex                     Part I, Section 6
sections/07_computation_sources.tex         Part I, Section 7
sections/08_questions.tex                   Part I, Section 8
sections/09_appendix.tex                    Part I, Appendices A and B
sections/235-binomial-01_results.tex        Part II, Section 9 (Report 235's Section 1)
sections/235-binomial-02_exact.tex          Part II, Section 10
sections/235-binomial-03_marked.tex         Part II, Section 11
sections/235-binomial-04_binomial.tex       Part II, Section 12
sections/235-binomial-05_local.tex          Part II, Section 13
sections/235-binomial-06_global.tex         Part II, Section 14
sections/235-binomial-07_context.tex        Part II, Section 15
sections/235-binomial-08_computation.tex    Part II, Section 16
sections/235-binomial-09_coupling.tex       Part II, Appendix A
code/230-endpoint-build.py                  Report 230's verifier, PDF and ZIP builder (delivered root build.py)
code/230-endpoint-diagnostics.py            mpmath diagnostics (complete sums, marked laws, Newton)
code/230-endpoint-endpoint.py               exact rational generator (coefficients, critical, marked, counts)
code/230-endpoint-selftest.py               exact self-test (normal and -O; --numerical adds mpmath checks)
code/235-binomial-algebra.py                SymPy algebra of Report 235 (generators, log densities)
code/235-binomial-build.py                  Report 235's verifier, PDF and ZIP builder (delivered root build.py)
code/235-binomial-checks.py                 exact checks (writes the receipt)
code/235-binomial-common.py                 shared JSON and guard helpers
code/235-binomial-coupling.py               finite checks of the residue coupling (Appendix A)
code/235-binomial-guard_tests.py            input and output-path guard tests
code/235-binomial-numerics.py               80-digit recurrences, rare-parity and CF Jacobian checks
code/235-binomial-reproduce_zip.py          archive replay
data/230-endpoint-requirements-optional.txt mpmath requirement (delivered code/)
data/230-endpoint-results-diagnostics.json  output of diagnostics.py suite --deep (delivered code/results/)
data/230-endpoint-results-selftest.txt      output of selftest.py --numerical (delivered code/results/)
data/235-binomial-guard_receipt.json        output of guard_tests.py (delivered code/)
data/235-binomial-numerical_receipt.json    output of numerics.py (delivered code/)
data/235-binomial-receipt.json              output of checks.py (delivered code/)
data/235-binomial-requirements.txt          SymPy and mpmath requirements (delivered root)
```

Every file except `README.md`, `article.tex`, `article.pdf` and the section
files is byte-identical to its delivery; the section files are the delivered
ones with the write's label prefixes and notes. Not shipped (retrievable from
`60f54ea06`): the delivered `Report230.pdf` (30 pages) and `Report235.pdf`
(23 pages); Report 235's `article.tex`, its `sections/10_references.tex`
(folded into the merged bibliography) and its `README.md`; and the two pure
checksum manifests `MANIFEST.sha256` (21 and 27 entries, both verified at the
write).

```sh
git show 60f54ea06:docs/incoming/Report230.zip > <scratch>/r230.zip
git show 60f54ea06:docs/incoming/Report235.zip > <scratch>/r235.zip
```

**Delivered text that names the delivery layout.** The code guides,
`235-binomial-COMPUTATION.md` and both `SOURCES.md` files use the delivered
names (`code/endpoint.py`, `code/results/…`, `build.py`, `MANIFEST.sha256`);
the programs import each other by their delivered names; both builders and
Report 235's archive replay expect the delivered layout and verify the
manifest, so they run only in a re-extracted archive. Part I's Appendix B and
Part II's Section 16.3 describe the delivered packages (dated notes there say
what is shipped).

**Third-party data.** `code/235-binomial-checks.py` and
`data/235-binomial-receipt.json` contain the first thirteen terms of OEIS
A360592 (CC BY-SA 4.0, https://oeis.org/LICENSE).

## Rerunning the checks (on scratch copies)

Never run the programs in place. From this directory (Git Bash), restore the
delivered names in a scratch directory:

```sh
T=$(mktemp -d); mkdir -p "$T/c230" "$T/c235"
for f in code/230-endpoint-*.py; do cp "$f" "$T/c230/${f#code/230-endpoint-}"; done
for f in code/235-binomial-*.py; do cp "$f" "$T/c235/${f#code/235-binomial-}"; done
D=$(cygpath -m "$PWD/data")
(cd "$T/c230" && py -B selftest.py --numerical && py -B -O selftest.py \
   && py -B diagnostics.py suite --deep > ../diag230.json)                       # mpmath 1.3.0
(cd "$T/c235" && py -B checks.py > ../checks.json && py -B -O checks.py > ../checksO.json \
   && py -B numerics.py > ../numerics.json)                                      # SymPy 1.14.0, mpmath 1.3.0
py -c "import json,sys; T,D=sys.argv[1:]; [print(a, json.load(open(T+'/'+a))==json.load(open(D+'/'+b))) for a,b in [('diag230.json','230-endpoint-results-diagnostics.json'),('checks.json','235-binomial-receipt.json'),('checksO.json','235-binomial-receipt.json'),('numerics.json','235-binomial-numerical_receipt.json')]]" "$(cygpath -m "$T")" "$D"
```

At the write (7 October 2026, Windows, Python 3.14.4): the self-test printed
"PASS: 89 checks (optimized Python)" and "PASS: 653 checks (ordinary
Python)", the recorded result (631 checks without `--numerical`, also under
`-O`); `diagnostics.py suite --deep` (9 s), `checks.py` (38 s; also under
`-O`) and `numerics.py` gave JSON equal to the shipped files. The guard suite
and the builders were not run (the intake recorded the guard suite's
rejection of Windows backslash paths as a Windows-only failure).

## Build

pdfLaTeX (lmodern, microtype, geometry, amsmath, amssymb, amsthm, mathtools,
booktabs, longtable, array, xcolor, enumitem, hyperref, bookmark, fancyhdr).
In a scratch copy:

```sh
B=$(mktemp -d); cp -r article.tex sections "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built from these files with MiKTeX pdfLaTeX (three
passes, 7 October 2026): 61 pages; no errors or warnings, no undefined
references, no multiply defined labels, no duplicate destinations, no overfull
or underfull boxes (the log's "duplicates ignored" lines are font-map notices
from the delivered `\pdfmapfile` lines, also in the delivered builds). The
delivered texts give 30 and 23 pages with no warnings.

## Provenance

- Batch 113 of `docs/incoming`: bundle Reports 230 and 235 (arrival
  `60f54ea06`), placed by `a4186a946`; written 7 October 2026.
- Sources cited: OEIS A360592, A360479, A360747; DLMF 1.10(vii) and 18.23.5;
  Corless–Gonnet–Hare–Jeffrey–Knuth (1996); Kotešovec (2013, not retrieved by
  the source); Barbour–Kowalski–Nikeghbali; Barbour–Xia (1999); Soon (1996);
  Čekanavičius–Peköz–Röllin–Shwartz (2009); Chhaibi–Delbaen–Méliot–Nikeghbali
  (2020); Méliot–Nikeghbali–Visentin (2022); Saumard–Wellner (2014);
  Dümbgen–Mösching (2022); Ehm (1991, abstract only); and the repository's
  transseries volume (added by the write).

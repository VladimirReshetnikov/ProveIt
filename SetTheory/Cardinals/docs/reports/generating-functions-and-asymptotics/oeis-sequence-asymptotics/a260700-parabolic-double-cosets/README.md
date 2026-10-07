# All Fixed Order Asymptotics for Distinct Parabolic Double Cosets

**Every fixed correction order for OEIS A260700, a proof of Browning's
higher-order conjecture, smooth inverse models and qualified integer
thresholds**

A research report dated 2 October 2026, built from one manuscript. Its
author line reads only "Research manuscript with reproducible computations";
the delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 17 | `double-coset-report.zip` (wrapper directory `double-coset-report/`), arrival commit `096ee7b87`; main file already named `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. Exact integer and rational
computations corroborate the finite identities and the coefficients;
numerical agreement is a diagnostic, not the proof.

## What it proves

`p_n` counts the **distinct subsets** `W_I w W_J` of the symmetric group
`S_n` (standard parabolic subgroups `W_I`, `W_J`; equal subsets with
different presentations counted once), OEIS A260700:
1, 3, 19, 167, 1791, 22715, …. With `ρ = log 2` and
`K = e^(-ρ²/2)/(4ρ²) = 0.40922300504774271232…`:

- **Theorem 1.1 (all fixed orders).** There are polynomials `B_m(r) ∈ Q[r]`
  with `p_n = K n! ρ^(-2n) (Σ_{m≤M} B_m(ρ) n^(-m) + O_M(n^(-M-1)))` for
  every fixed `M`; `B_1(r) = r²/2 - r³ - 11r⁴/12 + r⁵/4` and `B_2` are
  printed, `B_3`, `B_4` in Appendix A. Consequently Browning's
  higher-order conjecture (arXiv Conjecture 5.1, journal Conjecture 41)
  holds with `c = -K B_1(ρ) = 0.108197052893921571585327453732… > 0`, and
  `c > 0` is proved without a numerical sign test.
- **Method.** Starting from Browning's exact enumeration (his Theorem 3.18,
  Proposition 3.19, Section 4.1): uniform generalized-Fubini pole
  extraction for logarithmically growing `j` (Lemma 3.1), summable bounds for
  the signed inner defects (Proposition 4.1), and a joint bound for all
  omitted long-cycle configurations in the outer Stirling transform
  (Section 5).
- **Section 6.** A finite exact coefficient algorithm for any fixed order
  (implemented in `code/coefficients.py`), not a numerical fit.
- **Section 7 (inverse).** Smooth inverse models `x_M(y)` of
  `F_M(x) = K Γ(x+1) ρ^(-2x) P_M(1/x)` with a Lambert-W seed, explicit first
  corrections, Newton error estimates (Propositions 7.1, 7.2) and an
  eventual two-ceiling bracket for the integer threshold
  `N(y) = min{n : p_n ≥ y}` (Corollary 7.3). **The rounding counterexample
  stays:** `y = p_25 + 1` has threshold 26 but `⌈x_1(y)⌉ = 25`, so an
  unconditional `N(y) = ⌈x_M(y)⌉` is false.

## What is not claimed

- The leading equivalent `p_n ~ K n! ρ^(-2n)`, its constant and the exact
  enumerative identities are Browning's (EJC 28(3) (2021), P3.40); Stirling
  transforms and singularity analysis are not claimed as new techniques
  (Kotěšovec's A120733 work is credited for the neighbouring approach).
- Only every **fixed** order: no convergence of the series, no bound uniform
  in `M`, no optimal truncation, no exponentially improved transseries.
- No effective remainder constants or starting indices; the inverse bracket
  is an asymptotic theorem, not a finite-input rounding test, and the smooth
  model is not a canonical interpolation of the sequence.
- Novelty rests on a bounded primary-source search through 2 October 2026
  (no later solution of the precise correction conjecture located); "not a
  certification of universal novelty or a claim of external peer review".
  Nothing was submitted to OEIS, a journal or an external repository.
- The five further questions of Section 9 (effective bounds, growth of
  `B_m(ρ)`, exponentially small contributions, combinatorial meaning, other
  parabolic families) are open; the four computed negative corrections do
  not establish a sign pattern.
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** The seed is the factorial core
  `p0:prop:factorial-core` (`κ = 1`, `d = -1 - 2 log ρ`, `L = log y`) of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`,
  equivalently `t2:eq:unbalanced-core` of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`;
  in `s = log X + d` it is `p0:thm:lambert-core` with `a = b = 1`
  (branch `W_0`). The corrections are the admissible-core reversion
  `p0:thm:core-reversion` (CTI `t2:prop:scaled`); the linear–logarithmic
  `p0:thm:lambert-centered` and CTI's balanced `t2:thm:balanced-inverse`
  do not apply directly (the phase is `x log x`). The bracket is the
  separation condition, part (2) of `p0:thm:staircase`; part (1) (exact
  rounding) does not apply because `F_M` is not an interpolation of `p_n`,
  which is what the counterexample shows. A dated `[write]` note at the end
  of Section 7.2 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt result. The generic staircase arithmetic named
in the Section 7 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern an arbitrary monotone function, not `p_n`.

**Neighbouring report.** The same batch opened
`oeis-sequence-asymptotics/a260952-full-support-signed-permutations`
(manuscript 02: full-support elements of the Weyl groups of types B and D,
A260952, A109253, A112225). Both count objects defined by standard
parabolic subgroups of a Coxeter group and both pass through a Stirling
transform and a Lambert-W seed; the theorems, generating functions and
scales differ (`ρ = log 2`, `n! ρ^(-2n)` here; `τ = log 3`,
`m!/(log 3)^(m+1)` there), neither uses the other, and the A260952 report
counts elements, so it does not answer this report's question 5 (other
parabolic families). The intake's untruncated repository search found no
other report on A260700, Browning's conjecture or parabolic double cosets.
The batch-77 dossier offered one two-Part report instead (Vladimir's call);
the placement kept two reports that cite each other.

**A second neighbour (batch 85B).** The collection report
[`a261781-matrix-compositions`](../a261781-matrix-compositions/) (OEIS
A261780, A261781, A261784; batch 85, manuscripts 06 and 01) uses the same
uniform Fubini pole extraction and positive outer Stirling transform
(Munarini–Poneti–Rinaldi's Proposition 29) on compact rays
n/k ∈ K ⋐ (1,∞), followed by a saddle point, and adds a finite all-orders
coefficient algorithm and a Lambert-W inversion with integer brackets. The
theorems and scales differ (two growing parameters n, k there) and neither
report uses the other's theorems; this report's question 3 (the further
Fubini poles `ρ ± 2πi, …`) has an open counterpart there. That report cites
this one as its method neighbour; a dated `[write]` note in Section 9 here
(`pdc:sec:literature`, added 3 October 2026) records the reciprocal pointer
and names the exact pole-lattice formula `q2:thm:fubini` of the transseries
volume.

**A third neighbour (batch 100).** The collection report
[`a007716-bipartite-multigraphs`](../a007716-bipartite-multigraphs/) (OEIS
A007716 and A007718; bundle Reports 88 and 92) counts the matrices of
A120733 — nonnegative, total sum n, no zero row or column — up to separate
row and column permutations. Its weighted count Σ M_{k,l}(n)/(k! l!)
(`bpm:eq:Z`) is A120733's sum with the factor 1/(k! l!), and it proves the
relative equivalent a_n ~ B_n² e^{W(n)²/2}/n! (`bpm:thm:leading`) by Burnside
and Bell-number saddles, not by a Fubini pole. No theorem is shared; a dated
note in Section 9 here (added 5 October 2026) records the pointer, and that
report already names A120733 as the labelled analogue.

**A fourth neighbour (batch 108).** The collection report
[`a138178-symmetric-packed-matrices`](../a138178-symmetric-packed-matrices/)
(OEIS A138178; bundle Report 238) writes its count as
½ Σ_k 2^(−k) f_n(k) with f_n a polynomial in k and extracts the same Fubini
pole at `ρ = log 2`: a positive coefficient envelope bounds all the nonreal
poles at once, at every polynomial degree, and the pole at `ρ` gives
n!/(2ρ^(n+1)), combined with an involution saddle and an expansion in
n^(−1/2). It bounds the nonreal poles without computing their
contributions, so question 3 here is untouched. No theorem is shared; a
dated note in Section 9 here (added 7 October 2026) records the pointer,
and that report names this one in its Section 1.1 note.

## Notation

Symbols are printed as delivered. A table in the first `[write]` note
(Section 1) fixes the letters with two meanings (`A`, `D`, `a`, `c`, `L`,
`T`, `R`, `C`, `t`, `w`, `x`, `E`) and the tempting false readings: `B_m`
are correction polynomials, not Bernoulli polynomials and not the
signed-permutation counts `B_n(q)` of the A260952 report; `S_a(x)` is a
Faulhaber power sum, not a Stirling number; `p_m(q)` in the A260952 report
are asymptotic coefficients, not counts. No symbol was renamed.

## Labels

Every label carries the prefix `pdc:`. The manuscript's 64 labels were
prefixed before anything cited them (49 `\ref`/`\eqref` updated); no label
was added (64 labels in all). The writing step also added three dated
`[write]` notes (Section 1: provenance, the neighbouring report, notation
table; end of Section 7.2: the instance note; Appendix B: the shipped
layout), three bibliography entries (`pdc-fss`, `pdc-tai`, `pdc-cti`), and
set the bibliography ragged-right. No statement, proof or number of the
manuscript was changed. A batch-85B reciprocal note (3 October 2026) added
a fourth dated `[write]` note (Section 9, before the research questions)
and a fourth bibliography entry (`pdc-mxc`); it adds no label (still 64)
and the PDF stays at 19 pages. A batch-100 reciprocal note (5 October 2026) added a fifth dated
`[write]` note after it and a fifth bibliography entry (`pdc-bpm`); it adds
no label (still 64). A batch-108 reciprocal note (7 October 2026) added a
sixth dated `[write]` note after that one and a sixth bibliography entry
(`pdc-spm`); it adds no label (still 64), and the rebuilt PDF stays at 19
pages with the same clean log.

## Files

```text
README.md                             this guide (replaces the delivery README)
SOURCES.md                            delivered primary-source attribution and scope (bounded search, 2 October 2026)
article.tex                           the report (delivered as article.tex)
article.pdf                           compiled report, 19 pages
code/coefficients.py                  exact fixed-order algorithm of Section 6 (SymPy); writes coefficients-order<M>.json to --output-dir
code/validate.py                      Browning's finite formula by integer recurrences, actual coset enumeration (n ≤ 5), 259 cycle identities; writes exact-values.json, validation.json
code/inverse.py                       Lambert-W/Newton inverse diagnostics and the rounding counterexample (150 digits); writes inverse-validation.json
code/replay.py                        the delivered full replay (first runs verify_manifest.py; see below)
code/verify_manifest.py               SHA-256 check against MANIFEST.json (not shipped)
code/build_pdf.sh                     the delivered PDF build (expects article.tex beside it)
data/b260700.txt                      OEIS A260700 b-file, n = 1..400, retrieved 2 October 2026 (third-party reference data, attributed in SOURCES.md)
data/exact-values.json                p_n and q_n for n = 0..400, computed by validate.py
data/coefficients-order4.json         exact D_m, U_m, B_m (m ≤ 4) with decimal evaluations
data/results-validation.json          recorded validation.json of the delivered full run (n ≤ 400)
data/results-inverse-validation.json  recorded inverse diagnostics, including y = p_25 + 1
data/requirements.txt                 sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement moved `build_pdf.sh` to `code/`,
`requirements.txt` to `data/`, and `results/validation.json`,
`results/inverse-validation.json` to `data/results-validation.json`,
`data/results-inverse-validation.json`. Not shipped: the delivered 16-page
PDF `article.pdf` and `MANIFEST.json` (a checksum ledger, verified 16/16 at
placement and retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/double-coset-report.zip > <scratch>/double-coset-report.zip`.

`data/b260700.txt` (184,552 B) and the `p` column of
`data/exact-values.json` (528,796 B) hold the same 400 values: the intake
checked all `n = 1…400` equal, and `validate.py` compares the two. The
b-file is a third-party copy (its SHA-256 is recorded in `SOURCES.md` and
as `bfile_sha256` in `data/results-validation.json`, delivered bytes kept);
`exact-values.json` is the package's own computation and is regenerable
(`validate.py 400 --output-dir <dir>`); nothing was excluded under the
heavy-artifact rule, since no file reaches 1 MB.

Delivered text that names the delivery layout or unshipped files: the
delivery README (replaced by this guide) and the article's Appendix B
describe a self-contained ZIP with a PDF and `MANIFEST.json` and run
`python -m pip install -r requirements.txt` from the package root (here
`data/requirements.txt`); `code/replay.py` runs `verify_manifest.py`, which
reads `MANIFEST.json`, so in this layout it stops at its first step;
`code/build_pdf.sh` compiles `article.tex` in its own directory (`code/`)
and writes `.build/` and `article.pdf` there. A dated note in Appendix B
says so.

## Rerun the checks (on a scratch copy)

The three computational scripts read only `data/` (through their own
location) and write to `--output-dir`, whose default `replay-output/` is
relative to the **current directory**; Windows also writes the JSON with
CRLF. Run on a copy (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp -r code data "$R" && cd "$R"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/coefficients.py 4 --output-dir out
$PY code/validate.py 40 --output-dir out      # 400 for the full range
$PY code/inverse.py --output-dir out
$PY - <<'EOF'
import json
J = lambda p: json.load(open(p))
print(J('out/coefficients-order4.json') == J('data/coefficients-order4.json'))
print(all(J('out/exact-values.json')[k] == J('data/exact-values.json')[k][:41] for k in 'pq'))
print(J('out/inverse-validation.json') == J('data/results-inverse-validation.json'))
EOF
```

At writing (2 October 2026, loaded machine) the three steps took 14 s, 13 s
and 25 s and all three comparisons printed `True`; `validation.json`
differs from `data/results-validation.json` only in the range fields
(`exact_formula_matches_OEIS_through`, `q_residuals`), because the recorded
file is from the `n ≤ 400` run.

For the delivered `replay.py` (manifest check included), use the delivered
layout: `git show 096ee7b87:docs/incoming/double-coset-report.zip > x.zip`,
extract, and run `python code/replay.py --quick` (or `--full`) in
`double-coset-report/`. At intake `--quick` (n ≤ 40) passed in 133 s with
outputs equal to the delivered ones apart from CRLF and the `--quick` range
fields; `--full` (n ≤ 400) was not run.

## Build the PDF

pdfLaTeX with lmodern, amsmath, amssymb, amsthm, mathtools, booktabs,
microtype, geometry, enumitem, fancyhdr, xcolor, hyperref and listings. From
this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 19 pages,
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source built to 16 pages with the same clean log.)

## Provenance

- Browning, *Counting parabolic double cosets in symmetric groups*,
  Electron. J. Combin. 28(3) (2021), P3.40 (arXiv:2010.13256); OEIS A260700
  and A120733; Kotěšovec, *Asymptotics of the sequence A120733* (2015);
  Schwob (2026), Diaconis–Simper (2022), Renteln (2024),
  Munarini–Poneti–Rinaldi (2009) as neighbouring work (see `SOURCES.md`).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 17 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.

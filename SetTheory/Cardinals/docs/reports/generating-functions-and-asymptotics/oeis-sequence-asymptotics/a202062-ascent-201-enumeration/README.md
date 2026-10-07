# Exact Enumeration of 201-Avoiding Ascent Sequences

**A proof of the Guttmann–Kotěšovec cubic generating function, all-orders
coefficient asymptotics `C μ^n n^(-9/2)`, a controlled inverse, and the
growth constant of A202061 (OEIS A202062)**

A research report dated 1 October 2026, built from one manuscript. Its
author line reads only "A proof and reproducible research report"; the
delivery names no author and no tool, and the PDF metadata has an empty
Author field.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 43 | `oeis-a202062-report.zip` (wrapper directory `a202062-report/`), arrival commit `096ee7b87`; main file `a202062-report.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `f76fcb566` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. Exact-arithmetic
certificates corroborate every finite algebraic identity the proof uses;
finite enumeration is a diagnostic only.

## What it proves

`a_n` counts ascent sequences of length `n` avoiding 201 (no `i < j < k`
with `w_i > w_k > w_j`), `a_0 = 1`, `G(x) = Σ a_n x^n` (OEIS A202062:
1, 1, 2, 5, 15, 52, 201, 843, 3764, 17659, …).

- **Theorem 1.1 (the generating function).** `G` is algebraic of degree 3:
  with `P(x)` the power-series root, `P(0) = 1`, of
  `(1-x)^2 P^3 + (x^2-1) P^2 + x P + x = 0`, `G` is an explicit rational
  expression in `P` and `x`, and equivalently the unique formal root of an
  explicit cubic `𝒫(x, g) = 0`. This is the conjecture of Guttmann and
  Kotěšovec (SLC 87B, 2023). Method: an exact generating tree with two
  state labels (Lemma 2.1), a two-catalytic kernel equation, two rational
  invariants (the second from an order-7 kernel orbit), a formal invariant
  lemma, a quadratic identity, and the three critical branches.
- **Comparison with the conjecture (Section 5).** The manuscript states that
  GK's conjectured cubic (their eq. (3.1)) is exactly equivalent to its own,
  but that GK's printed final combination (their p. 10) has a sign error;
  the corrected relation is `G = y_2/(12x^3) + y_1`. This is the
  manuscript's claim about an external paper. `verify_exact.py` checks the
  correctly signed identity; the intake did not re-read GK's page.
- **Theorem 6.1 (all orders).** For every fixed `M`,
  `a_n = C μ^n n^(-9/2) (Σ_{m≤M} c_m n^(-m) + O(n^(-M-1)))`, where
  `μ = 1/ρ = 7.2958969432…` is the largest root of `μ^3 - 8μ^2 + 5μ + 1 = 0`
  (`ρ = 0.137063339542…` the smallest positive root of
  `x^3 + 5x^2 - 8x + 1`), `C = 13.4299960869439…` in closed form, and every
  `c_m ∈ Q(ρ)`; `c_1, c_2, c_3` exact (`c_1 = -8.3599214862…`). The first
  three odd Puiseux coefficients at `ρ` vanish, so the first non-integral
  power is `7/2`. The amplitude agrees with GK's amplitude polynomial.
- **Theorem 7.1 (inverse).** For a specified positive cut-integral model
  `A_*(s)` of the sequence (`a_n = A_*(n) + O(R^(-n))`), the real inverse
  has a `W_{-1}` leading term and an all-orders expansion with coefficients
  `d_j` from a formal generator; the integer threshold
  `N(Y) = min{n : a_n ≥ Y}` lies between two ceilings, eventually, with
  non-explicit constants.
- **Section 8 (A202061).** Combined with Conway–Conway–Elvey Price–Guttmann
  (EJC 2022, Theorem 4: 120- and 201-avoidance have equal exponential growth
  rates), Theorem 6.1 gives `lim b_n^(1/n) = μ` for the 120-avoiding
  sequence `b_n` (A202061).

## What is not claimed

- The cubic generating function and the leading asymptotic are credited to
  Guttmann–Kotěšovec as a conjecture; the contribution is the proof, the
  all-orders transfer and the inversion.
- Novelty rests on a scoped literature check only (Cerbai 2025 still lists
  the problem as open); "not a substitute for a comprehensive novelty
  review".
- No exact single-ceiling rounding formula for `N(Y)` and no numerical
  certification at any finite `Y`: the envelope constants are not explicit.
- Finite enumeration and numerical tables are diagnostics, not proof.
- For A202061 only the growth constant is established here; the manuscript
  calls the rest of the A202061 asymptotics conjectural. That sentence is
  re-scoped by a dated note (see below).
- Not journal-reviewed; the manuscript's own closing questions (a bijective
  explanation of the order-7 orbit, joint state-label distributions,
  explicit remainder constants, conventional review) are questions, not
  results.
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** Its leading term `λn - κ log n = log(Y/C)` is
  `p0:thm:lambert-core` (`a = log μ`, `b = -9/2`, branch `W_{-1}`), its
  generator is `p0:thm:lambert-centered` (same `a`, `b`, `Q(t) = Σ ℓ_j t^j`),
  and the single-ceiling remark is the separation condition, part (2) of
  `p0:thm:staircase`. All are in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  Part (1) of `p0:thm:staircase` does not apply as stated, because `A_*` is
  not an interpolation of `a_n`. A dated `[write]` note at the end of
  Section 7 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt theorem. The generic staircase arithmetic named
in the Section 7 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `a_n`.

**A202061: a second route, and a re-scoped sentence.** The same batch
opened `oeis-sequence-asymptotics/a202061-ascent-120-deficit` (five
manuscripts, written concurrently with this report). Its Part I
("Logarithmic deficit of 120 avoiding ascent sequences", batch-77
manuscript 39), main theorem of the section "Results and scope", proves
`μ^n e^(-CΦ(n)) ≤ b_n ≤ C μ^n e^(-cΦ(n))` with `Φ(n) = n^(1/3)(log n)^(2/3)`
and identifies `μ` in its section "An exact critical point", without using
the A202062 generating function or the CCEG comparison. So Section 8 here
and Part I there are independent routes to `lim b_n^(1/n) = μ`. A dated
`[write]` note in Section 8 records this and re-scopes the manuscript's
last sentence: the *form* of the subexponential factor is no longer
conjectural (Part I proves the deficit is `Θ(Φ(n))` and excludes every
equivalent `C_0 μ^n exp(-d n^γ) n^g` with `γ ≥ 1/3`, including the
numerically estimated `n^(3/8)`; its later Parts give the limit of the
normalized deficit and every fixed inverse-logarithmic order), while a power
factor and amplitude remain open in both reports. Those results are proved
there, not here.

**Neighbouring reports.** Three batch-77 reports treat ascent sequences
avoiding a pattern of length 3 (the Conway–Conway–Elvey Price–Guttmann
programme): this one (201, algebraic, `μ^n n^(-9/2)`),
`a202061-ascent-120-deficit` (120, same `μ`, stretched-exponential
deficit, not D-finite) and `a202058-ascent-000-growth` (000, factorial
growth). The regimes and methods are disjoint; the shared constant `μ` is
the only overlap. `a126764-lconvex-polyominoes` proves the
Guttmann–Kotěšovec L-convex polyomino asymptotic from the same GK paper and
states that 201-avoiding ascent sequences are not addressed there; the two
reports share only that citation (no generating function, constant,
bijection or method). (These pointers are made here only; the neighbouring
reports are not edited by this write.) *[Dated note, 7 October 2026,
batch-102 reciprocal note: batch 102 added
[`a202059-ascent-100-110-growth`](../a202059-ascent-100-110-growth/)
(bundle Reports 243 and 241) for the 100- and 110-avoiding classes
(A202059, A202060): factorial growth, with root `Θ((log n)^{−2})` after
division by `n!`, and the refutation of the fractional-factorial scale
`Γ(3n/4+1) μⁿ n^g` conjectured by Conway, Conway, Elvey Price and Guttmann.
No shared theorem.]*

## Notation

The manuscript reuses letters with section-local meanings (`t` three ways;
`T` a state type and a trace; `α`, `β`, `R`, `w`, `K`, `D`, `M`, `E`, `d`
two ways each), and `κ = 9/2`, `C = 13.43…`, `α` here are not the `κ`,
`C`, `α` of the A202061 report, where `a_n` and `A(x)` denote A202061. A
table in the first `[write]` note (Section 1) fixes each symbol by section,
with the tempting false readings. No symbol was renamed.

## Labels

Every label carries the prefix `a62:`. The manuscript's 23 labels were
prefixed before anything cited them (21 `\ref`/`\eqref` updated), and nine
section labels `a62:sec:…` were added for the notes: 32 labels in all.
The writing step also added four dated `[write]` notes (Section 1:
provenance, family, a126764, notation table; Section 7: the instance note;
Section 8: second route and re-scoping; Section 9: layout), two
bibliography entries (`a62-tai`, `a62-a61`), and set the bibliography
ragged-right. It restored the diacritic in "Kotěšovec" (four places,
printed "Kotešovec" in the delivery). No statement, proof or number of the
manuscript was changed.

## Files

```text
README.md                        this guide (replaces the delivery README)
article.tex                      the report (delivered as a202062-report.tex)
article.pdf                      compiled report, 12 pages
code/verify_exact.py             exact certificate of every finite algebraic reduction (SymPy); prints one PASS line
code/puiseux.py                  exact number-field Puiseux coefficients and relative corrections; writes two files beside itself
code/inverse.py                  inverse coefficients, exact residual check, one numerical target; writes one file beside itself
code/enumerate_sequences.py      direct-word check of the state transitions and tree counts (standard library)
code/build.sh                    the delivered PDF build (expects a202062-report.tex beside it; see below)
data/certificate-output.txt      recorded verify_exact.py stdout
data/puiseux-output.txt          recorded `puiseux.py --relative-order 5` stdout (β_7…β_13, c_1…c_5, C)
data/puiseux-results.txt         puiseux.py result file: ε, β_7…β_13, c_1…c_3, C (no final newline)
data/relative-coefficients.txt   puiseux.py result file: c_0…c_5 in Q(ρ) (no final newline)
data/inverse-output.txt          recorded `inverse.py --order 5 --target-log 1000` stdout
data/inverse-coefficients.txt    inverse.py result file: d_1…d_5 in terms of ρ and λ
data/enumeration-output.txt      recorded `enumerate_sequences.py --check-length 8 --terms 40` stdout (a_0…a_40)
data/requirements.txt            sympy>=1.12,<2 and mpmath>=1.3,<2
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed `a202062-report.tex` to
`article.tex`, moved the scripts and `build.sh` to `code/` and the recorded
outputs and `requirements.txt` to `data/`. Not shipped: the delivered
10-page PDF `a202062-report.pdf` and `SHA256SUMS` (a checksum ledger,
verified 16/16 at placement). Both survive in the archive:
`git show 096ee7b87:docs/incoming/oeis-a202062-report.zip > <scratch>/oeis-a202062-report.zip`.

Delivered text that names the delivery layout or unshipped files:
`code/build.sh` (compiles and copies `a202062-report.tex` /
`a202062-report.pdf` in its own directory); the article's Section 9 list
(which omits `inverse.py`; dated note added). The delivery README, which
this guide replaces, said "Use Python 3 with SymPy installed" although the
scripts also need mpmath (listed in `requirements.txt`).

## Rerun the checks (on a scratch copy)

`puiseux.py` and `inverse.py` write `puiseux-results.txt`,
`relative-coefficients.txt` and `inverse-coefficients.txt` **next to
themselves**, so running them in `code/` would add files to the
repository; Windows also writes those files and redirected stdout with
CRLF. Run on a copy (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp code/*.py "$R" && cd "$R"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY verify_exact.py > certificate-output.txt
$PY puiseux.py --relative-order 5 > puiseux-output.txt
$PY inverse.py --order 5 --target-log 1000 > inverse-output.txt
$PY enumerate_sequences.py --check-length 8 --terms 40 > enumeration-output.txt
for f in *.txt; do diff -q --strip-trailing-cr "$f" "$OLDPWD/data/$f"; done
```

Do not use `python -O` (the checks are assertions). At intake (2 October
2026, on a heavily loaded machine) the four commands took about 87 s, 57 s,
48 s and 20 s, every check passed, and all seven outputs matched the
shipped files modulo line endings.

## Build the PDF

pdfLaTeX (the preamble uses `\pdfmapfile`) with amsmath, amssymb, amsthm,
lmodern, microtype, hyperref, enumitem and booktabs. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 12 pages,
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source built to 10 pages with two underfull boxes in
the bibliography, removed by the ragged-right setting.) `code/build.sh` is
kept as delivered; to use it, copy it to a scratch directory together with
`article.tex` renamed to `a202062-report.tex`.

## Provenance

- Guttmann–Kotěšovec, Sém. Lothar. Combin. 87B (2023), Article 2;
  Cerbai, Electron. J. Combin. 32(3) (2025), P3.6; Conway–Conway–Elvey
  Price–Guttmann, Electron. J. Combin. 29(4) (2022), P4.25, Theorem 4;
  Flajolet–Sedgewick, *Analytic Combinatorics*, Chapters VI–VII; OEIS
  A202062 (accessed 1 October 2026).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 43 (cluster P1); arrival
  `096ee7b87`, placement `f76fcb566`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.

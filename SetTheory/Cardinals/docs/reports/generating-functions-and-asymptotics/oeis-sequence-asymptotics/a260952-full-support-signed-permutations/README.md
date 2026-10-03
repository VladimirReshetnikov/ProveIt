# Full Support Signed Permutations and Their Asymptotic Coefficients

**A proof of Kotěšovec's A260952 large-order conjecture with every fixed
correction, late coefficients as a positive Stirling transform, a
sparse-sign Poisson crossover, and growth-index inverses (OEIS A260952,
A109253, A112225)**

A research report dated 2 October 2026, built from one manuscript. Its
author line is empty, the PDF metadata has an empty Author field, and the
delivery names no author and no tool.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 02 | `Coxeter_Full_Support_Asymptotics.zip` (wrapper directory `Coxeter_Full_Support/`), arrival commit `096ee7b87`; main file `Coxeter_Full_Support_Asymptotics.tex`, now `article.tex` | none: no ProveIt commit is named and no repository path is continued | `d0e6008d9` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor
a tool), unrefereed, not formalized. Exact integer recurrences, symbolic
series and a brute-force enumeration corroborate the finite identities and
coefficients; the numerical checks through index 600 are consistency
checks, not proofs.

## What it proves

With `g(x) = Σ n! x^n`, `C = 1 - 1/g` (indecomposable permutations `c_n`,
A003319) and `B_n(q) = [x^n] g(qx)/g(x)`: `b_n = B_n(2)` counts the
full-support elements of the Weyl group `B_n` (A109253), `d_n = (b_n - 3c_n)/2`
those of `D_n` (A112225), and `a_m = A260952(m) = 2^m p_m(2)`, where
`B_n(q)/(q^n n!) ~ Σ p_m(q) n^(-m)`.

- **Theorem 1 (the conjecture).** Kotěšovec's 2015 conjecture
  `a_m ~ -2^(m+1) m!/(9 (log 3)^(m+1))` holds, with the explicit corrections
  `1 - 2τ/m - 9τ²/(4(m)_2) - 27τ³/(2(m)_3) - 1755τ⁴/(16(m)_4) + O(m^(-5))`,
  `τ = log 3`, every further fixed order by a finite formula (the next two
  are printed), and `a_m < 0` for every `m ≥ 1`.
- **Section 2.** `Z_n(u) = B_n(1+u)` is the generating polynomial of
  full-support signed permutations by number of negative entries (an
  elementary verification of the classical sign-weighted extension).
- **Lemma 2 and Theorem 3.** Every fixed order for `c_n/n!` in falling
  factorials, and separate all-order expansions of the two exact endpoint
  sums `L_n(q)`, `H_n(q)`, uniformly for `1/4 < |q| < 4`, with formal
  generators.
- **Theorem 4 (late coefficients).** `p_m(q)` as a positive Stirling
  transform with every fixed order of its late expansion on the scale
  `τ = log(1+q)`, uniformly on compact `q`-intervals; Theorem 1 is its case
  `q = 2`.
- **Theorem 5 (sparse signs).** Every fixed order of `B_n(1+λ/n)/n!`,
  locally uniformly in complex `λ`; the number of negative signs converges
  to a Poisson(`λ`) variable conditioned to be positive.
- **Section 8 (inverse).** Lambert-W inverses for the three carriers
  `K α^n Γ(n+1)(1 + Σ u_j n^(-j))` and an integer-threshold enclosure of
  stated rounding width.

## What is not claimed

- The `B`/`D` models, generating functions and connectivity
  characterization are credited to Bergeron–Hohlweg–Zabrocki (J. Algebra
  303 (2006), Propositions 23–26); the shifted-Stirling / compound-Poisson
  construction and integral representations to Martin–Kearney
  (Combinatorica 35 (2015)) as "prior methodology"; the connected-permutation
  expansion is classical (Comtet 1972); the leading factorial asymptotics
  and several corrections of A109253/A112225 are already in the OEIS. These
  credits are kept as delivered.
- No convergence of an infinite expansion, no optimal truncation, no
  complete transseries; a fixed truncation of the main series does not
  resolve the exponentially small second endpoint.
- The separate endpoint bounds are not extended to `q ≥ 4`.
- The threshold enclosure describes a rounding ambiguity; it asserts no
  exact ceiling decision near a sequence value and no canonical
  interpolation of the sequence.
- Priority rests on a bounded source search (2 October 2026); "exhaustive
  historical priority is not asserted".
- **The inversion is an instance of repository results, with no novelty
  claimed for the method.** The seed `n_0 = ℓ/W(αℓ/e)` is the factorial
  core `p0:prop:factorial-core` (`κ = 1`, `d = log α - 1`, `L = ℓ = log y`)
  of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  (its slope is the printed `D_0 = log(α n_0)`), equivalently
  `t2:eq:unbalanced-core` of
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`;
  in `s = log X + d` it is `p0:thm:lambert-core` with `a = b = 1` (branch
  `W_0`). The corrections and the formal Newton iteration are the
  admissible-core reversion `p0:thm:core-reversion` (CTI `t2:prop:scaled`);
  `p0:thm:lambert-centered` and CTI's balanced `t2:thm:balanced-inverse`
  do not apply directly (the phase is `x log x`). The enclosure is the
  separation condition, part (2) of `p0:thm:staircase`; part (1) (exact
  rounding) does not apply to the smooth truncation. A dated `[write]` note
  at the end of Section 8 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status; the
manuscript used no ProveIt result. The generic staircase arithmetic named
in the Section 8 note is formalized as `Fabius.staircase_ceil` and
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`;
those lemmas concern an arbitrary monotone function, not `a_m` or `B_n(q)`.

**Neighbouring report.** The same batch opened
`oeis-sequence-asymptotics/a260700-parabolic-double-cosets` (manuscript
17: every fixed order for the distinct parabolic double cosets of `S_n`,
A260700, and a proof of Browning's higher-order conjecture). Both count
objects defined by standard parabolic subgroups of a Coxeter group and
both pass through a Stirling transform and a Lambert-W seed; the theorems,
generating functions and scales differ (`τ = log 3`, `m!/(log 3)^(m+1)`
here; `ρ = log 2`, `n! ρ^(-2n)` there), and neither uses the other. The
intake's untruncated repository search found no other report on A260952,
A109253, A112225 or full-support elements of Coxeter groups (indecomposable permutations,
A003319, appear elsewhere only in passing). The batch-77 dossier offered one
two-Part report instead (Vladimir's call); the placement kept two reports
that cite each other.

## Notation

Symbols are printed as delivered. A table in the first `[write]` note
(Section 1) fixes the letters with two meanings (`τ`, `D`, `a`, `K`, `A`,
`u`, `v`, `w`, `ℓ`, `x`) and the readings that clash with the A260700
report: there `B_m(r)` are correction polynomials and `p_n` counts double
cosets, while here `B_n(q)` counts signed permutations and `p_m(q)` are
asymptotic coefficients; `c_n` here counts indecomposable permutations, not
Browning's constant `c`. No symbol was renamed.

## Labels

Every label carries the prefix `fss:`. The manuscript's 46 labels were
prefixed before anything cited them (29 `\ref`/`\eqref` updated), and nine
section labels `fss:sec:…` were added for the notes: 55 labels in all. The
writing step also added three dated `[write]` notes (Section 1:
provenance, the neighbouring report, notation table; end of Section 8: the
instance note; Section 9: the shipped layout), three bibliography entries
(`fss-pdc`, `fss-tai`, `fss-cti`), and set the bibliography ragged-right.
No statement, proof or number of the manuscript was changed.

## Files

```text
README.md                    this guide (replaces the delivery README)
SOURCES.md                   delivered source list and attribution (bounded audit, 2 October 2026)
article.tex                  the report (delivered as Coxeter_Full_Support_Asymptotics.tex)
article.pdf                  compiled report, 11 pages
code/derive.py               symbolic coefficient generator (SymPy); prints to stdout
code/verify.py               exact recurrences, signed-permutation enumeration (n ≤ 6), numerical checks through 600 (mpmath); writes ../data/verification.json and prints a summary
code/replay.sh               the delivered replay (expects derive.py, verify.py under code/ next to it; see below)
code/build.sh                the delivered PDF build (expects Coxeter_Full_Support_Asymptotics.tex beside it)
data/coefficients.txt        recorded derive.py stdout: five sparse-sign and six late correction orders
data/verify_summary.json     recorded verify.py stdout ("all_exact_assertions_passed", max_n 600)
data/verification.json       detailed checks through index 600, written by verify.py (no final newline)
data/requirements.txt        sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement renamed
`Coxeter_Full_Support_Asymptotics.tex` to `article.tex` and moved
`build.sh` and `replay.sh` to `code/` and `requirements.txt` to `data/`.
Not shipped: the delivered 9-page PDF `Coxeter_Full_Support_Asymptotics.pdf`
and `SHA256SUMS` (a checksum ledger, verified 12/12 at placement and
retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/Coxeter_Full_Support_Asymptotics.zip > <scratch>/Coxeter_Full_Support_Asymptotics.zip`.

Delivered text that names the delivery layout or unshipped files: the
delivery README (replaced by this guide) lists the `.tex`/`.pdf` names,
`build.sh`, `replay.sh` and `SHA256SUMS` at the package root;
`code/replay.sh` changes to its own directory and runs `code/derive.py`,
so in the shipped layout it does not find the scripts (and would create
`code/data/`); `code/verify.py` writes `verification.json` into the
`data/` directory beside its parent, i.e. **over the shipped
`data/verification.json`**; `code/build.sh` compiles
`Coxeter_Full_Support_Asymptotics.tex` in its own directory. A dated note
in Section 9 says so.

## Rerun the checks (on a scratch copy)

Because `verify.py` overwrites `data/verification.json`, and Windows writes
CRLF, run on a copy (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp -r code data "$R" && cd "$R"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/derive.py > coefficients.txt
$PY code/verify.py > verify_summary.json     # also rewrites data/verification.json in the copy
for f in coefficients.txt verify_summary.json data/verification.json; do
  diff -q --strip-trailing-cr "$f" "$OLDPWD/data/${f#data/}" && echo "same $f"
done
```

At writing (2 October 2026) the two steps took 10 s and 5 s and all three
outputs matched the shipped files modulo line endings. At intake the
delivered `bash replay.sh`, run in the delivered layout, passed (rc 0,
166 s on a heavily loaded machine) with the same result. For the delivered
`replay.sh`, use the delivered layout:
`git show 096ee7b87:docs/incoming/Coxeter_Full_Support_Asymptotics.zip > x.zip`,
extract, and run `bash replay.sh` in `Coxeter_Full_Support/` (it rewrites
that copy's `data/`).

## Build the PDF

pdfLaTeX with inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, geometry, microtype, hyperref and enumitem. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 11 pages,
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. (The delivered source built to 9 pages with the same clean log.)
`code/build.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to
`Coxeter_Full_Support_Asymptotics.tex`.

## Provenance

- OEIS A260952 (Kotěšovec, 5 August 2015), A109253, A112225, A003319;
  Bergeron–Hohlweg–Zabrocki, J. Algebra 303 (2006), 831–846;
  Martin–Kearney, Combinatorica 35 (2015), 309–315; Comtet, C. R. Acad.
  Sci. Paris A 275 (1972), 569–572 (see `SOURCES.md`).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 02 (cluster P4); arrival
  `096ee7b87`, placement `d0e6008d9`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.

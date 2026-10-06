# Lonesum Decomposable Matrices to All Orders (OEIS A299907)

**A complete expansion of `a_n` in powers of `n^(-1/2)` with explicit `C`,
`c_1`, `c_2` and an all-orders Gaussian coefficient recipe, a global contour
lemma, inverse threshold brackets that keep the rounding error inside the
ceiling, and the exact sum `a_n = Σ_k k! B_k S(n+1,k+1)^2` with
`B_k` = A000262**

A research article ("Report 132" of a session bundle), built from one
manuscript dated 2 October 2026. Its author line reads "Report 132" and its
PDF author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 132 (batch 108) | `A299907_All_Orders_Matrix_Asymptotics_and_Inversion_Source.zip` (18 files in the wrapper directory `Report132_bundle/`, 369,597 bytes, SHA-256 `ad4d45c0…b16feea1362`), arrival commit `60f54ea06`; main file `Report132.tex` (334 lines, 8 pp.) | none: the package names no ProveIt commit; its `sources.md` mentions a "bounded repository-topic review" without naming a repository or commit | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository formalizes lonesum decomposable matrices or this asymptotic.

## Trust boundaries

- **Cited input.** Kamano's exponential generating function
  `F(x,y) = exp(x + y + 1/(1 − (e^x − 1)(e^y − 1)) − 1)` (Discrete Math. 341
  (2018) 341–349, arXiv:1701.07157, Theorem 3.1, eq. (9)), his uniqueness of
  the decomposition (Proposition 1.2), his forbidden-submatrix theorem
  (Theorem 2.1) and his Stirling formula (Proposition 4.1). The exact
  enumeration is his formula summed over the decomposition order.
- **Proved by hand in the source.** The expansion (Theorem 1), from the
  generating function alone, through the saddle, a global contour estimate
  (Lemma 1) and a Gaussian recipe; the doubling `a_{n+1} ≥ 2a_n`; the inverse
  brackets of Section 5. All remainder constants and onsets are existential.
- **Computer algebra.** The printed `γ, A, B, P_1, P_2, c_1, c_2` are
  algebra the text does not show; the delivered scripts reproduce them, and
  the write's own series program (written from eq. (9) of the article)
  reproduces them exactly. `c_3` (Remark 2) is an output of the delivered
  recipe only.
- **Finite checks** (the delivered checker, the write's brute force through
  `4 × 4`, the table to `n = 3200`) prove nothing asymptotic.

## What it proves

`a_n = D(n,n)` counts `n × n` binary matrices that, after independent row and
column permutations, are block diagonal with lonesum blocks having no zero
line, plus zero rows and columns; equivalently, induced-`P_5`-free bipartite
graphs on two fixed labelled shores of size `n`. `ℓ = log 2`,
`β = sqrt(2/ℓ)`. Statement numbers are the delivered ones.

- **Theorem 1 (`lsd:thm:asympt`)**: for every fixed `M`,
  `a_n = (n!)^2 C ℓ^(−2n) n^(−5/4) e^(β sqrt n) (Σ_{j≤M} c_j n^(−j/2) + O_M(n^(−(M+1)/2)))`,
  `C = exp(−5/8 + 1/(8ℓ)) / (π (2ℓ)^(1/4) sqrt(1 − ℓ)) = 0.33947395869341…`,
  `c_1 = −0.53170633782380…`, `c_2 = −0.16357013012662…` in closed form
  (eqs. (3)–(5)), and `c_j = E Q_{2j}` (eq. (11)) for a product Gaussian
  functional.
- **Lemma 1 (`lsd:lem:arc`)**: the loss `1/d − Re 1/(1 − P)` is at least
  `c min(v²/d² + u²/d³, 1/d)` near the saddle and `c/d` elsewhere on the
  torus, so only the central box contributes.
- **Section 5**: `N(T) = min{n : a_n ≥ T}` lies in
  `[⌈X_1 − K_1/(sqrt(x) h)⌉, ⌈X_1 + K_1/(sqrt(x) h)⌉]` and in the sharper
  bracket around `X_2` (eq. (13)), with `x = L/(2W(L/(2eℓ)))`, `L = log T`;
  for every `M`, `⌈y_M − E_M⌉ ≤ N(T) ≤ ⌈y_M + E_M⌉` with `y_M` the root of an
  explicit `Φ_M`; Newton iteration from `x`.
- **Section 6**: `a_n = Σ_k k! B_k S(n+1,k+1)^2` (eq. (15)) with the
  recurrence (14) for A000262, and a table of `R_n` for
  `n = 100, 400, 800, 3200`.

Added by the write (6 October 2026), with proofs, marked `[write]`:

- **Remark 1 (`lsd:rem:graph`)**: lonesum decomposability is a property of
  the connected components (each nontrivial one is a connected chain graph,
  via Kamano's Proposition 1.1 = Ryser), and the forbidden configurations are
  exactly the induced `P_5`, in both directions (the source checked one);
  a brute-force check of all shapes up to `4 × 4` three ways.
- **Remark 2 (`lsd:rem:c3`)**: the delivered recipe at order 3 gives
  `c_3 = −sqrt2 N_3(ℓ)/(106168320 ℓ^(9/2) (ℓ − 1)^3) = −0.26674650591076…`,
  the value the source stored but did not claim; the exact counts behave
  accordingly, approaching `c_4 = 1.00342017659501811…` (stated since the
  independent check below; the remark first said "close to 1").
- **Remark 3 (`lsd:rem:transseries`)**: Section 5 against the transseries
  volume, statement by statement (next sections).
- **Remark 4 (`lsd:rem:oeis`)**: the three OEIS entries quoted; the entry's
  Mathematica double sum is eq. (15); a misprint in A299906's example
  (below).
- Section 1.1 (`lsd:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), a note on the package at the end of
  Section 6, and in Section 7 (`lsd:sec:further`) a note on each source
  question and two added questions.

## Correction: a misprint in the example of A299906

The live entry A299906 (revision #24, 26 October 2019, read 6 October 2026),
"Array read by antidiagonals: T(n,k) = number of n X k lonesum decomposable
(0,1) matrices.", prints its example row `n = 5` as

    1, 32, 634, 8528, 90446, 833432, ...,

(verbatim), so `T(5,4) = 90446`. The correct value is **90946**:
transposition is a bijection between `5 × 4` and `4 × 5` lonesum decomposable
matrices, the same table prints `T(4,5) = 90946`, the entry's data list 90946
at both positions, and `D(5,4) = 1 + 465 + 13500 + 50700 + 26280 = 90946`
term by term from the rectangular exact sum (Remark 4(c)). Recorded only:
**nothing was submitted to the OEIS.**

Remark 4(a) also notes a word-order trap: A299907's name, "Number of
decomposable lonesum n X n (0,1) matrices.", read as "lonesum matrices that
are decomposable", would describe a subset of the lonesum matrices (14 of
size `2 × 2`), whereas `a_2 = 16`; the data are Kamano's lonesum decomposable
matrices, the term A299906 uses after its 2019 name correction. This is a
reading convention, not a correction of the entry.

## Against the transseries volume (Remark 3)

`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`:

- the Lambert root `x` is an **instance**, verbatim, of
  `p0:prop:factorial-core` with `(κ, d) = (2, −2(1 + log ℓ))` and target
  `L`; the report's `h = log(x/ℓ)` is the proposition's `v + 1`, and `2h` its
  core slope;
- `X_1` and `X_2` are an **instance after a change of variable**
  (`y = x(1 + E)`, `t = x^(−1/2)`) of `p0:thm:core-reversion`, with
  `Λ = h`, `h_vol(u) = (1+u) log(1+u) − u`, over a ring in which `log x` and `h`
  are constants (as `p0:rem:core-instances` treats the core slope); the
  source's three cancellation identities are the first three coefficients;
  the theorem is formal, the error orders are the source's;
- `N(T)` **is** the staircase `N_*` of `p0:def:three-inverses` (`a_n` is
  strictly increasing from `n = 0`); the brackets are **analogues, not
  instances,** of `p0:thm:staircase` (no interpolation is constructed; they
  come from envelopes);
- `y_M` is a numerical root, not a formal object; `plt:thm:lw-template` does
  not apply to `Φ_M` (the `β sqrt y` term, and `−(5/4) log y` with
  Stirling's corrections, violate (H3); the write first named only the
  former) but applies to the core alone.

No novelty is claimed for the inversions.

## What is not claimed

From the source, kept in the article (collected in Section 1.1):

- Remainder constants and onsets are existential; no certified finite-`n`
  bound or finite-`T` bracket; numerical tests do not supply one.
- No worldwide novelty or priority: "a limitation on priority assessment,
  not a claim of worldwide novelty or the resolution of a named open
  conjecture"; the search was bounded and Khera's 2021 dissertation was not
  inspected; the generating function and exact enumeration are Kamano's.
- The graph statement fixes the labelled bipartition (not graphs up to
  isomorphism, not an unspecified bipartition).
- `⌈X_1⌉` is not a valid rounding rule; the error stays inside the ceiling.
- No central or local limit theorem for the number of blocks; no optimal
  truncation or exponentially small terms.
- The stored `c_3` is not claimed by the source.
- Finite checks and the QA procedure check reproducibility and named finite
  identities only; integrity hashes are not authorship authentication; PDF
  byte identity holds only in the delivering TeX environment.

The write adds: `c_3` in Remark 2 is computer-algebra output of the delivered
recipe; Remark 3 classifies statements and proves nothing new about `a_n`.

## Further questions

Section 7 (`lsd:sec:further`) keeps the source's four questions as delivered
(effective remainders; rectangular aspect ratios; the number of blocks;
beyond all orders), with a note on what each needs, and adds (Vladimir's
standing rule of 4 October 2026):

5. **The shape of `c_j`** (`lsd:q:pattern`, added by the write): for
   `j = 1, 2, 3` the denominators are `192, 192², 15·192³` times
   `ℓ^(3j/2)(ℓ − 1)^j` and the numerators have degree `3j`; does it persist?
6. **The literature boundary** (`lsd:q:literature`, from the source's
   prior-art paragraph): Khera's dissertation, unread by source and write.

Two statements the source made without proof are now proved (Remark 1).
**Nothing in the source was found to be wrong**; the one correction concerns
OEIS text.

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows, Python 3.14.4):
  the 16 staged files are byte-identical to the archive; `MANIFEST.json`
  17/17 with a closed inventory. The dossier read the manuscript in full and
  found no error; it checked the induced-`P_5` reading of `U`, `C` from its
  closed form and the `−(1/4) log n` term, and reran on a copy `check.py`
  (normal and `-O`: pass), `derive_general.py 2`, `derive.py` and
  `validate.py --max-n 100` (the `n = 100` row).
- At the write (6 October 2026, same machine): the live OEIS entries
  (A299907 #15, A299906 #24, A000262 #515), Kamano arXiv:1701.07157v1,
  Khera–Lundberg–Melczer arXiv:1912.08850v2 (Remark 2) and Bényi–Ramírez
  arXiv:1804.03949v1 (Section 4.3, Theorem 11) were read; every proof was
  rechecked line by line; an independent series program re-derived
  eq. (9) through `t^4` and `c_1`, `c_2` exactly; the saddle expansions,
  the eigenvalue limits (at the exact saddle for `n = 10^4, 10^6, 10^8`), the
  contour identity, the Jacobian, the prefactor, the inverse identities, the
  doubling and eqs. (14)–(15) were checked; the table was recomputed from
  exact integers for `n = 100, 400, 800` (and `1600`); all binary matrices up
  to `4 × 4` were classified three ways; Alcover's Mathematica line was run in
  Wolfram 15; the delivered package was rerun from a fresh extraction (route
  A below: `check.py` normal and `-O` pass in about 5 s; `derive_general.py 3`
  about 10 s) and from the shipped files (route B: pass).
- Not read: Khera's dissertation; the journal versions behind the arXiv
  texts.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`6ef3f0983`), with its own code:
  Remark 1 by four independent deciders (literal decomposition search with
  lonesum as uniqueness of the line sums, criterion (b), Kamano's 12-matrix
  set, induced-`P_5` search) on every shape up to `4 × 4`, and by the last two
  on every shape up to `5 × 5` (all `2^25` matrices at `5 × 5`): no
  disagreement, `D(5,4) = D(4,5) = 90946`, `D(5,5) = 833432`. The A299906
  misprint confirmed in the live entry (still #24): `T(5,4) = 90946` by the
  formula, by enumerating all `2^20` matrices of size `5 × 4` and by
  transposition; all 66 data terms and all 16 terms of A299907 match. An
  independent 90-digit expansion of eq. (9) through `t^8` gives `c_1`, `c_2`
  (to `10^{−89}`), `c_3` (agreeing with the closed form of Remark 2 to 88
  digits) and `c_4 = 1.0034201765950181116370…`; the delivered
  `derive_general.py 4`, rerun when the check was applied, gives the same
  `c_4` to 69 digits (denominator `30·192^4 ℓ^6 (ℓ−1)^4`, numerator degree 12:
  the pattern of Question 5, not claimed). Exact `a_n` to `n = 3200`
  reproduce the table and Remark 2; `n²(R_n − Σ_{j≤3})` = 0.916 … 0.987
  approaches `c_4`, and the next remainder times `n^{5/2}` is a stable
  −0.874 … −0.907. Remark 3 re-derived (SymPy for (b)). No mathematical error;
  two statements made more precise with dated notes keeping the first
  wording (Remark 2 states `c_4`; Remark 3(d) names all the terms that
  violate (H3)). The check is recorded at the end of Section 6.

## Relation to the repository

**Formal status.** No statement of this report is formalized, and placement
in the collection confers no formal status. Generic ingredients are
formalized in `Analysis/FabiusFunction/Lean/FabiusFunction/`:
`Fabius.lahNumber` and `Fabius.X_mul_mkOne_pow` (the Lah column generating
function `(t/(1−t))^k = Σ_n k! L(n,k) t^n/n!`, from which `Σ_k L(n,k)` =
A000262 follows by summing over `k`), `Fabius.stirlingSecond_succ_succ_eq_sum`,
and the generic rounding facts `Fabius.staircase_ceil`,
`Fabius.staircase_separation`. None is a statement of this report.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):
`a122399-surjection-diagonal` (the diagonal of `1/(1 − u e^y(e^x − 1))`: a
pole, not the exponential of a pole, with the same `(n!)^2` scale and
Stirling machinery; it credits Khera–Lundberg–Melczer);
`a089479-fixed-permanent-matrices` (same batch; mentions a
lonesum-decomposable report as a different model);
`a261781-matrix-compositions` (cites Khera–Lundberg–Melczer). The six other
single-source matrix reports of batch 108 share a style but no theorem.

**Stale claims and reciprocal notes.** Before batch 108 no file of the
repository named A299907, A299906 or lonesum decomposable matrices. The
README of `congruences-and-valuations/a321941-asymptotic-coefficient-integrality`
says "A000262 occurs nowhere else in the repository", which this report makes
stale; a correction and a pointer in `a122399-surjection-diagonal` are
proposed separately, not applied here.

## Notation

A table at the end of Section 1.1 fixes the letters the source reuses, with
the tempting false readings: `D(m,n)` against `D = 1 − q²`, `D_1`, `D_2`,
Khera–Lundberg–Melczer's `D_{n,k}`, Kamano's `D_k(m,n)` and A299906's `T`;
`A(z) = e^z − 1` against the Gaussian `A`; `B_{11}, B_{12}, B = 1 − ℓ, B_k`;
three meanings of `k`; `c_j` against the constants `c, c_0` of Lemma 1; `d`,
`d_j`; `h` (two meanings); `x, y, m` (Section 4 and 5 meanings); `ℓ, L, T`
against the transseries volume's `ℓ, L` and A299906's `T`; `t, U, V, u, v`;
`β, γ` (not Euler's constant); `P, P_j, Q_j, E`; `N(T)`, `W = W_0`;
`S(n,k)`. Symbols of the transseries volume carry the subscript "vol". No
symbol of the source was renamed.

## Labels

Every label carries the prefix `lsd:` (none existed in the repository). The
manuscript's 17 labels (`eq:` 15, `thm:` 1, `lem:` 1) were prefixed before
anything cited them, and the 14 references to them updated. The write added
8: `lsd:rem:graph`, `lsd:rem:c3`, `lsd:rem:transseries`, `lsd:rem:oeis`,
`lsd:sec:provenance`, `lsd:sec:further`, `lsd:q:pattern`, `lsd:q:literature`.
The report has 25 labels; builds of the delivered text and of this one give
all 17 delivered labels the same numbers (aux files compared). The added
remarks have their own counter (the source has none), the added subsection
closes Section 1, the added questions continue the source's list, and the
added displays are unnumbered.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered Report132.tex; labels prefixed, [write] additions)
article.pdf                  compiled report, 15 pages
sources.md                   the source's bibliography and search boundary (delivered at the root)
code/derive_general.py       all-orders recipe (11), any order (delivered at the root)
code/derive.py               separate direct expansion of P_1, P_2, c_1 (delivered at the root)
code/exact.py                exact integer enumeration (15) and a second exact route (delivered at the root)
code/formulas.py             C, c_1, c_2 and the inverse centres X_1, X_2 (delivered at the root)
code/validate.py             exact large-n diagnostics (delivered at the root)
code/check.py                closed-inventory integrity and finite checks (delivered at the root)
code/build.py                deterministic PDF build (delivered at the root)
code/qa.py                   reproducibility QA (delivered at the root)
code/package.py              manifest sealing and ZIP packaging (delivered at the root)
code/safe_output.py          no-clobber output helpers (delivered at the root)
data/fixtures.json           A299907 for 0 <= n <= 15 (OEIS terms; delivered at the root)
data/diagnostics_3200.json   C, beta, c_1, c_2, c_3 and diagnostics for n <= 3200 (delivered at the root)
data/requirements.txt        sympy==1.14.0, mpmath==1.3.0 (delivered at the root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report132.pdf` (the delivered 8-page PDF, 347,319 bytes); `MANIFEST.json`
(1,457 bytes, 17 SHA-256 entries, verified at placement; repository policy
ships no checksum manifests); and the delivery `README.md` (4,364 bytes),
staged at placement and replaced by this guide (summarized below).

**Delivered text that names the delivery layout or files not shipped.** The
programs import one another and read `fixtures.json` and `Report132.tex`
from their own directory, so they do not run under the shipped names in
place. `check.py` in its default mode verifies a closed inventory of the 18
delivered names (including `Report132.pdf` and `MANIFEST.json`) and their
hashes; `build.py` compiles `Report132.tex`; `qa.py` compares a rebuild with
`Report132.pdf` and replays a fresh archive; `package.py --seal` rewrites
`MANIFEST.json` **in place** (never run it in the repository; on the shipped
layout it refuses, as the inventory does not match). `build.py`, `qa.py`,
`package.py` and `safe_output.py` need POSIX (`O_DIRECTORY`, `O_NOFOLLOW`,
`mkfifo`). Section 6 of the article and `sources.md` speak of "the
accompanying bundle" and "the article" in the delivered layout.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A299907_All_Orders_Matrix_Asymptotics_and_Inversion_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # ad4d45c02c098dce8432c72c103686c8d7f7fec85514bfa109eddb16feea1362, 369,597 bytes
cd "$T" && unzip -q a.zip && cd Report132_bundle   # 18 files
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later with `sympy==1.14.0` and `mpmath==1.3.0`
(`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python ...`
works). Never run anything in the repository.

**Route A, delivered layout** (as the delivery README gives it; run at the
write on Windows):

```sh
cd "$T/Report132_bundle"
python3 -B check.py                       # PASS: closed inventory and SHA-256 integrity; PASS: finite checks
python3 -B -O check.py
python3 -B derive_general.py 2            # c 1, c 2 as in eqs. (4)-(5); order 3 gives c_3 (Remark 2)
python3 -B derive.py
python3 -B validate.py --max-n 100        # the n = 100 row of the table
```

`validate.py --max-n 3200` repeats the stored diagnostics (long). The PDF
rebuild, `qa.py` and `package.py` need POSIX and pdfTeX and were not run by
the intake.

**Route B, from the shipped files, any OS** (tested at the write):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a299907-lonesum-decomposable-matrices
B=$(mktemp -d); cp "$R"/code/*.py "$R/data/fixtures.json" "$B/"; cp "$R/article.tex" "$B/Report132.tex"; cd "$B"
python3 -B check.py --finite-only         # every finite check; the default mode stops at the inventory, as designed
```

Use `py` where `python3` is not on the path.

## Build the PDF

pdfLaTeX (T1 fontenc, lmodern, microtype, amsmath, amssymb, amsthm, booktabs,
array, geometry, hyperref); the bibliography is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (also 15 pages at the write): 15 pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. The delivered source builds the same way to 8 pages, also
without warnings. The article keeps the delivered preamble lines that
suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report132.tex` under the delivering toolchain (pdfTeX
1.40.26, TeX Live 2025/dev/Debian), not to this build.

## From the delivery README

The delivery README (replaced by this guide) called `Report132.pdf` "the
reader article" and summarized the results as above, with constants and
onsets "existential" and no certified finite-`n` bound or worldwide novelty;
listed the dependencies (tested with Python 3.12.14, SymPy 1.14.0, mpmath
1.3.0); gave the routine verification of Route A, noting that a changed
manifest "can legitimize a file edit for integrity purposes" and that
SHA-256 integrity "is not cryptographic authorship authentication"; gave the
calculation commands, noting that the stored `c_3` is not claimed and that
"Numerical residual convergence is evidence about implementation, not proof
of the asymptotic theorem"; gave POSIX rebuild, QA and packaging commands
writing to a fresh temporary directory; described `package.py --seal` as a
maintainer operation, "not a verification command"; and ended on scope: the
generating function and enumeration are Kamano's, ordinary lonesum
asymptotics are prior work, the graph interpretation fixes both shores, and
the source search was bounded.

## Rights

Repository contents are MIT-0. The article and `data/fixtures.json` quote
OEIS terms and text of A299907, A299906 and A000262; OEIS content is
published by The OEIS Foundation Inc. under CC BY-SA 4.0
(https://oeis.org/LICENSE), and those terms remain under that licence. No
third-party PDF is shipped. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: Kamano (Discrete Math. 341 (2018);
  arXiv:1701.07157); OEIS A299907, A299906, A000262; Khera, Lundberg and
  Melczer (Adv. Appl. Math. 123 (2021) 102118; arXiv:1912.08850); Bényi and
  Ramírez (arXiv:1804.03949); Khera's 2021 dissertation (not inspected).
  Added by the write: the transseries volume and the FabiusFunction Lean
  declarations named above (by path, not as bibliography).
- Batch 108 of `docs/incoming`, bundle Report 132; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report132.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.

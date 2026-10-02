# All-Orders Asymptotics and Asymptotic Inversion for A292507

**The binomial transform of partitions without ones: all-orders Poincaré expansion, finite coefficient algorithm, reversion and integer-threshold brackets**

A research note dated 1 October 2026, built from one manuscript. The
delivery names no author or tool (its author line reads "Research note").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 01 | `A292507_report_and_code.zip` (main file `a292507_asymptotics.tex`, 474 lines, 10-page PDF) | none | `4f11bc9c0` (arrival `096ee7b87`) | the whole article, Sections 1–8 |

**Status: unrefereed; not formalized; AI-assisted delivery channel.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq.

For

    a_n = sum_{k=0}^{n} C(n,k) b(k),   b(k) = p(k) − p(k−1)
        (partitions of k without parts 1; OEIS A292507: 1, 1, 2, 5, 13, 33, 82, 201, 488, 1176, ...)

the article proves:

- **Theorem 1.1** an all-orders Poincaré expansion
  `a_n = C 2^n n^(−3/2) e^(β√n) (Σ_{j≤M} c_j n^(−j/2) + O_M(n^(−(M+1)/2)))`
  with `β = π/√3`, `C = (π/6) e^(π²/24)`, closed forms of `c_1, c_2, c_3`,
  and the additive logarithmic form (7), which specifies the subleading
  terms of Kotěšovec's logarithmic conjecture additively;
- **Section 4** a finite algorithm for every `c_j` (Gaussian tilted moments
  of the binomial variable, formula (25)); `c_1 … c_6` computed
  (`c_1 = −4.41001…`, `c_2 = 15.80700…`, …, `c_6 = 2492.654…`);
- **Proposition 5.1, Theorem 5.2** the real model `𝒜_M` is eventually
  increasing with an explicit residual bound `|x_0 − x_M(y)| ≤ (2/log 2)|F_M(x_0) − Y|`,
  and its inverse has an all-orders reversion `T_J(X)` in `X^(−1/2)` and
  `log X`, with `U_1`, `U_2` explicit;
- **Theorem 6.1** shrinking integer-threshold brackets
  `⌈x_M(y) − B_M X^(−r)⌉ ≤ N(y) ≤ ⌈x_M(y) + B_M X^(−r)⌉`, `r = (M+1)/2`,
  with existence constants.

The only analytic input is Nemes' explicit partition-remainder estimate
(Lemma 2.2 of his 2024 paper), used for the finite difference `b(k)`.

## What is not claimed

Every limitation and priority caveat of the delivery is kept in the article:

- The leading binomial-smoothing mechanism is prior art (OEIS A218481, 2015
  and 2023 comments); the leading constant is a direct application of it.
  The logarithmic conjecture is Kotěšovec's (2019) and the coefficient
  formula Gutkovskiy's (2021). A limited literature search found no
  published higher `c_j` or inverse; **no publication priority or novelty is
  claimed**.
- No convergence of the correction series and no complete exponential
  transseries; the secondary partition sectors are not analysed.
- The constants of Theorem 6.1 (and `D_M`) are existence constants, not
  certified thresholds; no unconditional `N(y) = ⌈x_M(y)⌉` is asserted.
- The floating-point diagnostics (the two tables of Section 7, the inverse
  value at `n = 10000`) are not interval certificates, and their signs prove
  no universal error sign. The finite checks do not prove the expansion.

## Labels and the write

Every label carries the prefix `bpt:`. The 49 delivered labels were
prefixed (50 references updated) before anything else cited them, and the
write added one, `bpt:provenance`: **49 → 50**. Section, theorem and
equation numbers are the manuscript's own and none changed. No statement,
proof or number of the manuscript was changed and no symbol renamed; the
preamble gained `array`, `xurl` and the `writenote` environment.

Six `[write]` notes were added (all of 2 October 2026):

1. a new unnumbered section *Provenance, status and reading conventions*
   (after the abstract): provenance, pin, status, the replays;
2. in the same section, a table of reused letters (`c` vs `c_j`; `λ = β/2`,
   not the volume's `λ = π√(2/3)`; `C` vs the unspecified `C` of (18); the
   two unrelated `B_M` of (22) and (40); `P`, `b`, `D`, `F`, `E`, `K`,
   `M`, `L`, `t`, `v`, `T`, `r`);
3. after Lemma 2.1: `P(x)` is the dominant Rademacher sector `P_{1,+}` of
   the transseries volume's partition chapter, whose `p3:prop:relative` and
   `p3:thm:tail` (`K = 1`) give `|p(k) − P(k)| = O(e^{c√k/2})`, enough for
   Lemma 2.1 (derivation by the writer, not part of the delivery);
4. after Theorem 5.2: the reversion is an instance of
   `p0:thm:lambert-core` / `p0:thm:perturbed-inversion`, no novelty claimed;
5. after Theorem 6.1: the brackets are the staircase mechanism
   `p0:thm:staircase` (1)–(2), whose generic arithmetic is formalized
   (below);
6. at the end of Section 7: the shipped names of the scripts and outputs,
   and the overwrite hazard.

## Files

```text
README.md                        this guide (replaces the delivery README.txt)
article.tex                      the report (delivered as a292507_asymptotics.tex)
article.pdf                      compiled report, 12 pages
code/reproduce.py                coefficient algorithm to any order, exact a_n, forward and model-inverse diagnostics
code/validate_inverse.py         symbolic check of the displayed U_1, U_2 against the general recursion
data/verification.json           recorded run: reproduce.py --order 6 --max-n 10000 (exact c_0..c_6, six diagnostic rows)
data/inverse_verification.json   recorded output of validate_inverse.py
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`4f11bc9c0` is the delivered `a292507_asymptotics.tex` byte for byte; the
write changed only labels and the preamble and added the notes above.

**Not shipped** (both survive in the arrival commit, see below): the
delivered `README.txt` (staged as `README.md` at placement and replaced by
this guide in the write; its reproduction notes and scope statement are
folded in here and in the article) and the delivered 10-page PDF. The
delivery had no checksum manifest.

**Delivered text that uses delivery names.** The delivery was flat;
placement moved the scripts to `code/` and the JSON records to `data/`. The
article's Section 7 listing (`python3 reproduce.py … --output
verification.json`, `pdflatex a292507_asymptotics.tex`) uses the delivered
names; a `[write]` note gives the shipped ones. `validate_inverse.py`
imports `reproduce` from its own directory and writes
`inverse_verification.json` into the **current** directory;
`reproduce.py` writes `--output` (default `verification.json`, default order
4) into the current directory.

## Relation to the repository

**Formal status.** Placement in the collection confers no formal status. No
A292507 statement is formalized anywhere in the repository. The only
formalized ingredient touched is generic: `Fabius.staircase_ceil` and
`Fabius.staircase_separation`
(`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`),
rounding facts for an arbitrary strictly monotone interpolation; they give
no formal status to Theorem 6.1.

**Instances of repository results, with no novelty claimed for the
method.** All in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:

- the reversion (Theorem 5.2) has the Lambert core `p0:thm:lambert-core`
  (`αx − γ log x = Y`) as dominant block and is a perturbed inversion in the
  sense of `p0:thm:perturbed-inversion`; the article itself expands in
  `X^(−1/2)` and `log X` without the Lambert normalisation;
- the integer brackets (Theorem 6.1) are the staircase mechanism
  `p0:thm:staircase` (1)–(2), applied to the model inverse with the model
  error as bracket radius;
- the partition input: `P(x)` of (8) is the dominant sector `P_{1,+}`
  (`p3:eq:dominant-in-N`, `p3:thm:exact-sectors`) of the volume's chapter
  on the partition numbers (`p3:sec:top`), which also gives an alternative to
  Nemes' bound sufficient for Lemma 2.1 (note 3 above) and describes the
  secondary sectors the article leaves aside. That chapter inverts `p(n)`
  itself; it does not treat the binomial transform.

The main expansion is a single-scale Poincaré series, which is why the
report sits in this collection and not in `Analysis/Transseries`.

**Neighbouring reports.** Other partition-type asymptotics in
`oeis-sequence-asymptotics/` (`a022629-distinct-partition-norms`,
`a097356-sqrt-restricted-partitions`,
`a238016-restricted-partitions-cubic-boundary`,
`a291698-moving-fugacity-partitions`) treat other weighted or restricted
partition counts; none treats a binomial transform, and no theorem is
shared. (These pointers are made here
only; those reports are not edited by this write.)

## Rerun the checks (on a scratch copy)

Both scripts write into the working directory, so run them on a copy, never
in `data/` (Git Bash, from this directory):

```sh
R=$(mktemp -d) && cp code/reproduce.py code/validate_inverse.py "$R" && cd "$R"
export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY reproduce.py --order 6 --max-n 10000 --output verification.json > reproduce.out
$PY validate_inverse.py      # prints the agreement line, writes inverse_verification.json
diff --strip-trailing-cr verification.json         <this directory>/data/verification.json
diff --strip-trailing-cr inverse_verification.json <this directory>/data/inverse_verification.json
```

On Windows Python both JSON files are written with CRLF line endings
(text-mode `write_text`); the shipped files are LF, so compare with
`--strip-trailing-cr` (or run under a POSIX Python). The delivery used
Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0. On 2 October 2026 (Windows,
Python 3.14, same SymPy and mpmath, a loaded machine) `reproduce.py` took
37 s and `validate_inverse.py` 54 s; both outputs were identical to the
shipped files apart from line endings, and `validate_inverse.py` printed
"Both displayed inverse polynomials agree symbolically with the general
recursion." Higher orders are accepted (`--order J`); symbolic cost grows
with the order.

## Build the PDF

pdfLaTeX with geometry, amsmath/amssymb/amsthm, mathtools, booktabs,
longtable, fontenc (T1), lmodern, microtype, hyperref, listings, array and
xurl. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 12 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. The log carries 698
`fontmap entry ... already exists, duplicates ignored` warnings from the
delivered preamble's `\pdfmapfile{+lm.map}` lines (MiKTeX already loads
those maps); the delivered text gives the same 698 and builds to 10 pages.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/A292507_report_and_code.zip > a292507.zip
unzip a292507.zip -d a292507-delivery   # flat: no wrapper directory
```

The archive (356,698 bytes) holds the delivered `README.txt` and
`a292507_asymptotics.pdf` besides the shipped files.

## Provenance

- One manuscript: batch 77, manuscript 01 (`A292507_report_and_code.zip`),
  arrival `096ee7b87`, placement `4f11bc9c0`, written in the batch-77 write
  phase (2 October 2026). No merge, so no merge choices.
- Pin: none; the delivery continues no ProveIt path. At placement no
  repository file mentioned A292507, A218481, A002865 or A292622.
- External sources (as delivered): OEIS A292507, A218481, A292622 (accessed
  1 October 2026); G. Nemes, Ramanujan J. 65 (2024) 1757–1771,
  arXiv:2402.07115 v2, Lemma 2.2; Banerjee–Paule–Radu–Schneider, Rocky
  Mountain J. Math. 54 (2024) 1551–1592.

# Uniform Asymptotics and Moving Zeros for the Level 15 Family of Cooper

**Modular connection proofs for the ten constants of Cooper's Table 8, a uniform two-singularity expansion at ε = −5, and the moving odd-index parameter zero**

A research report dated 2 October 2026, built from one manuscript. Its
author line is empty.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 33 | batch 77, manuscript 33 | `modular-crossover-replay.zip` (main file `modular-crossover.tex`, 999 lines, 21-page PDF) | none (names no repository revision) | `4f11bc9c0` (arrival `096ee7b87`) | the whole article, Sections 1–12 |

**Status: AI-assisted delivery channel, unrefereed, not formalized.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq. The word
"replay" in the archive name names the packaging, not a repair: no earlier
repository report treats Cooper's level 11, 14, 15 or 24 sequences or
A284756.

For Cooper's level-15 family `T_ε(n)` (a five-term recurrence, real
polynomials of degree `n` in `ε`; Cooper, arXiv:2302.00757v2, Theorem 8.1)
the article proves:

- **Theorem 1.1** a uniform two-singularity expansion to every fixed order on
  the closed disc `|ε + 5| ≤ 1/10`, with rates `R₊ = ε + 11`, `R₋ = ε − 1`,
  amplitudes `C₊ = (ε+11)^{3/2}/(20π^{3/2})`, `C₋ = (1−ε)^{3/2}/(2π^{3/2})`,
  and an **additive** error that stays valid where the two terms cancel;
- **Corollary 1.2** in the window `ε = −5 + u/n`, uniformly for bounded
  complex `u`,

      T_{−5+u/n}(n) / (A 6ⁿ n^{−3/2}) = e^{u/6} + 10(−1)ⁿ e^{−u/6} + O(1/n),
      A = 6^{3/2}/(20π^{3/2}),

  with explicit polynomials `P_{j,±}(u)` at every order;
- **Theorem 1.3** for every large odd `n`, exactly one zero of
  `u ↦ T_{−5+u/n}(n)` in `|u − 3 log 10| < 1`, real and simple, with

      ε_n = −5 + 3 log(10)/n + (162/125 − (9/2) log 10)/n² + O(n^{−3})

  and the next two coefficients in closed form; no real zero in any bounded
  window for large even `n`; and (Corollary 9.1) fixed local complex zeros
  of both parities;
- **Sections 3–6** explicit path, sheet and connection proofs
  (Theorem 3.1, Lemma 3.2, Proposition 6.1) for **all ten constants of
  Cooper's Table 8** (levels 11, 14A/B/C/C̄, 15A/B/C/C̄, 24), including the
  two negative-axis connections 15B and 14C̄ with exact eta multipliers
  (Table 1);
- **Proposition 8.1** a finite exact generator for every fixed correction
  order `b_m`, with `b_1, b_2, b_3` printed for several cases and `b_{2,±}`,
  `b_{3,±}` as polynomials in `ε`;
- **Proposition 10.1** a qualified, non-effective threshold inverse for
  positive sequences.

## What is not claimed

Every limitation and priority caveat of the delivery is kept in the article:

- The ten constant formulas are Cooper's (arXiv v2, 8 May 2024, Section 10,
  Table 8, where they are labelled conjectured and determined numerically);
  the level-11 equivalent is Václav Kotěšovec's in OEIS A284756 (2 April
  2017). Guillera–Zudilin (2013, Example 6 and eq. (27)) supply the positive
  modular radial principle; Cooper–Ye (2016, Section 7) the negative-`q`
  machinery; Campbell–Cooper–Ye (2026) identify positive Fricke endpoints.
  What the article claims is the explicit proofs with their hypotheses.
- The uniform expansion and the zero law "were not found in the sources
  examined"; the literature search is explicitly bounded (Cooper–Ge–Ye 2015
  and Cooper's 2017 book not fully searched; the 2025 published version not
  compared page by page) and **no historical priority is claimed**.
- Theorem 1.3 is local in the rescaled parameter: no global location of the
  `n` zeros, no claim that odd `n` has only one real zero, no relative
  equivalent at the cancellation point.
- No convergence of `Σ b_j n^{−j}` and no uniformity as the truncation order
  grows; no conclusion for complex-zero indices `k` growing with `n`.
- Proposition 10.1 keeps the unknown asymptotic error inside the ceiling; it
  is not a certified finite-`n` enclosure and gives no explicit constant or
  cutoff. No ordered inverse for complex or signed coefficients.
- The replay's numerics use 100 decimal digits and are not interval
  certificates; finite checks do not replace the analytic proofs.
- The OEIS identifiers of the 14A, 14B, 15A, 15B and 24 sequences were not
  verified by the delivery; none is inferred.
- The three "Further directions" of Section 11 are open.

## Labels and the write

Every label carries the prefix `cmz:`. The 91 delivered labels (`sec:main`,
`eq:15rec`, `thm:uniform`, …) were prefixed before anything cited them, with
their 90 references; the write added one, `cmz:provenance`: **91 → 92**.
No theorem, equation, section or table number changed (the `.aux` numbers of
all 91 delivered labels equal those of a build of the delivered text). No
statement, proof or number of the manuscript was changed and no symbol was
renamed.

Four `[write]` notes were added (all of 2 October 2026):

1. a new subsection 1.2 *Provenance, status and reading conventions*:
   provenance, pin, status and the intake checks;
2. in the same subsection, a table of the letters the manuscript reuses
   (`u` as the competition variable and as `Re τ`; `r, R, R_±`; `s`; `A`,
   `B`; `C`; `D`; `M`; `h`, `L`; `P`, `w`; `v`; `a, b, c, d`; the sequence
   names), and the conventions of the shipped data (below);
3. at the end of Section 10: the inverse is an instance of the transseries
   volume's inversion apparatus (below), with no novelty claimed;
4. at the end of Section 12: the relation to
   `a279619-level-seven-gamma-constant` (below).

## Files

```text
README.md                         this guide (replaces the delivery README)
article.tex                       the report (delivered as modular-crossover.tex)
article.pdf                       compiled report, 23 pages
code/replay.py                    the delivered replay: exact algebra and 100-digit checks, six stages
code/coefficients_primary.py      module imported by replay.py: the fixed-case generator (Prop. 8.1)
code/coefficients_auxiliary.py    module imported by replay.py: level 14/15 data and the generator in algebraic fields
code/build.sh                     delivery-state tool: offline pdfLaTeX build of modular-crossover.tex
data/expected_coefficients.json   exact b_0 ... b_6 for the fixed cases and the crossover data, read by replay.py
data/expected_replay.json         the delivery's recorded replay output (Python 3.12.14, status PASS)
data/requirements.txt             sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`4f11bc9c0` is the delivered `modular-crossover.tex` byte for byte; the write
changed only labels and added the notes above.

**Not shipped** (all survive in the arrival commit, see below): the
delivered 21-page PDF, `MANIFEST.sha256` (11 entries, verified 11/11 at
placement and retired) and `verify_manifest.py` (which checks only that
ledger). The delivered README is replaced by this guide; its content is kept
here (results, attribution and limits above; data conventions, replay and
build below).

**Delivered text that uses delivery names.** The delivery was one flat
directory. `code/build.sh` builds `modular-crossover.tex` in its own
directory into `.build/` and copies `modular-crossover.pdf` beside itself;
it cannot build `article.tex` and should not be run here (use the build
below). `code/replay.py` reads `expected_coefficients.json` **from its own
directory**, so it fails when run from `code/` (the file is in `data/`). The
delivered README's commands `python verify_manifest.py` and
`pip install -r requirements.txt` name an unshipped file and the delivered
location.

## Exact-data conventions (from the delivery README)

In `data/expected_coefficients.json` the symbol `x` in a primary fixed-case
coefficient denotes the selected algebraic root `r = 1/R`, not the
generating-function variable. The auxiliary coefficients are already
evaluated in their algebraic fields. In the crossover data, `e` denotes `ε`,
`u` is the competition variable and `U` a limiting zero (the centre `U` of
Corollary 9.1). The article defines the branches.

## Relation to the repository

**Formal status.** Placement in the collection confers no formal status. No
statement of this report is formalized anywhere in the repository, and no
Lean or Rocq development treats Cooper's sequences or modular connection
constants. (The repository's Lean and Rocq files named `Cooper` are D. C.
Cooper's quantifier elimination for Presburger arithmetic, unrelated.)

**An instance of repository results, with no novelty claimed for the
method.** The leading equation `λX − (3/2) log X = L` behind the inverse
iteration (10.1) is the dominant block `p0:thm:lambert-core` (with
`a = λ`, `b = −3/2`, large solution on the `W₋₁` branch); the expansion
(10.3) treats `log S_K` as a perturbation in the sense of
`p0:thm:perturbed-inversion`; and the "error inside the ceiling"
qualification of Proposition 10.1 is the separation condition of
`p0:thm:staircase` (2), all in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.

**Neighbouring report.**
`oeis-sequence-asymptotics/a279619-level-seven-gamma-constant` treats a
level-seven sequence whose square sequence A183204 belongs to Cooper's
sporadic Apéry-like family. Its third derivation (batch 77, manuscript 32;
Proposition `l7g:tr:prop:local`, Remark `l7g:tr:rem:gz`) differentiates a
Fricke involution at its fixed point, a level-seven instance of the
mechanism of this report's Theorem 3.1 and (3.3), and credits the same
Guillera–Zudilin eq. (27). The two reports share no theorem; neither
manuscript cites the other. That report is not edited by this write (a
reciprocal note is a separate commit).

## Rerun the replay (on a scratch copy in the delivered layout)

```sh
R=$(mktemp -d)
cp code/replay.py code/coefficients_primary.py code/coefficients_auxiliary.py \
   data/expected_coefficients.json "$R"
cd "$R"
uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 \
   python replay.py --output fresh_replay.json
diff --strip-trailing-cr fresh_replay.json <this directory>/data/expected_replay.json
```

Always pass `--output` (the default `replay_results.json` is written in the
current directory). On Windows the output is written with CRLF line endings;
compare with `--strip-trailing-cr`. On 2 October 2026 (Python 3.13.5, SymPy
1.14.0, mpmath 1.3.0, on a loaded machine) all six stages printed PASS in
44.5 s and the output was identical to `data/expected_replay.json` except for
the recorded Python version. The delivery says the replay normally takes
about ten seconds and that low-level roundoff displays can vary with
dependency versions.

The replay asserts: exact `b_0 … b_6` for all ten fixed cases and the
amplitude identities; the exact matrices and eta multipliers of the
negative connections; high-precision eta identities and fixed-point
derivatives; recurrence/asymptotic comparisons through `n = 2000` for all
ten cases; the exact crossover polynomials and zero coefficients through
order 3 and the Appell identity through degree 12; additive sample checks
for both parities and complex `u`, including the cancellation value; the
moving odd-index zeros and one fixed complex zero branch of each parity;
inverse examples verified against exact neighbouring recurrence values.

**Checks made at intake (independent of the replay).** With SymPy and
mpmath: the first terms of 15A and 15B from (1.1); `b_{1,±}` of (1.4) from
the general formula (8.2), symbolically in `ε`; `u_1` of (1.8); the zero
`u_n` of `T_{−5+u/n}(n)` for `n = 101, 201, 401, 801` against
`u_0 + u_1/n + u_2/n² + u_3/n³` of (1.9)–(1.10), where `n⁴` times the
residual settles near 417 (consistent with a fourth coefficient of that
size); and the vanishing of Kotěšovec's sextic `704c⁶ − 1936c⁴ − 1020c² − 1331`
at `c = π^{3/2} C₁₁` (residual `5·10⁻⁴⁷`, limited by the 50-digit root `r`). The proofs were not
re-derived.

## Build the PDF

pdfLaTeX with fontenc (T1), lmodern, amsmath/amssymb/amsthm/mathtools,
geometry, booktabs, array, longtable, microtype, hyperref and enumitem. From
this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 23 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. (The delivered text builds
to 21 pages here, also without warnings.)

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/modular-crossover-replay.zip > mc.zip
unzip mc.zip -d mc-delivery    # files under modular-crossover/
```

The archive (455,516 bytes) holds the delivered README, the 21-page PDF,
`MANIFEST.sha256` and `verify_manifest.py` besides the shipped files.

## Provenance

- One manuscript: batch 77, manuscript 33 (`modular-crossover-replay.zip`),
  arrival `096ee7b87`, placement `4f11bc9c0`, written in the batch-77 write
  phase (2 October 2026). No merge, so no merge choices.
- Pin: none; the delivery names no ProveIt revision and continues no
  repository path.
- External sources (as delivered): S. Cooper, arXiv:2302.00757v2 (2024) and
  Contemp. Math. 818 (2025); Guillera–Zudilin (2013); Cooper–Ge–Ye (2015);
  Cooper–Ye, Trans. AMS 368 (2016); Campbell–Cooper–Ye, arXiv:2602.09352v1
  (2026); Flajolet–Sedgewick (2009); OEIS A284756 (consulted 2 October 2026).

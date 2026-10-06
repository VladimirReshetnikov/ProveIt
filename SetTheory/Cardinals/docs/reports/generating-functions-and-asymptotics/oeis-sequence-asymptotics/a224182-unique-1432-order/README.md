# Permutations with Exactly One 1432 (OEIS A224182)

**The order `b_n = Θ(9ⁿ/n³)` with explicit constants `1/2187` and `81`,
without a computer; an inverse bracket of width `11/2`; and a
computer-certified exact image of the marked split**

A research article dated 2 October 2026 ("Report 139" of a session bundle),
built from one manuscript. Its author line reads "Report 139" and its PDF
author field is empty: it names no person, tool or addressee. The package
carries no "prepared for private review" line, no e-mail address and no
personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 139 (batch 105) | `A224182_Polynomial_Growth_Order_and_Inverse_Bounds_Source.zip` (wrapper directory `Report139/`, 10 files, 1,316,107 bytes, SHA-256 `ba737c31…642c`), arrival commit `60f54ea06`; main file `Report139.tex` (707 lines, 10 pp.) | none: the package names no ProveIt commit, path or report | `e85586b7c` (batch 105) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The order theorem has
a conventional, computer-free proof. The exact-image theorem (Theorem 7.1)
is computer-assisted (below). No asymptotic statement rests on a
computation.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 — `M_{n−3} ≤ b_n ≤ (n+2)A_{n+2}`
  for `n ≥ 4`, `M_m ~ (m/3)A_m`, hence `b_n = Θ(9ⁿ/n³)` and
  `1/2187 ≤ liminf b_n/(nA_n) ≤ limsup b_n/(nA_n) ≤ 81` — rests on the
  eight-case proof of Lemma 5.1, the marked inverse, the inflation of
  Proposition 4.1, the entropy estimate of Section 3 and two cited theorems:
  Regev's three-row strip asymptotic `A_n ~ C_0 9ⁿ/n⁴`,
  `C_0 = 81√3/(16π)` (not read by the write; exact `A_n` for `n ≤ 400` are
  consistent with it), and Krattenthaler's growth-diagram Theorems 1–3
  (located by the write in arXiv math/0510676v2, Section 2; not re-derived).
  The shape-Wilf ingredient is attributed to Backelin, West and Xin, whose
  journal text neither the source nor the write read.
- **What is certified by computation.** Theorem 7.1 (the split is a
  bijection onto the *eligible* marked centres of 1432-avoiders of size
  `n+2`, so `b_n = Σ_{q ∈ Av_{n+2}(1432)} #{eligible K}`): necessity and the
  reduction of any false positive to at most eight source points are proved
  by hand; sufficiency then rests on an **exhaustive finite certificate** —
  every source of size 4–8 with at least two occurrences and every designated
  core passing the four singleton-region tests (0, 0, 6, 130, 1938 cases,
  **2,074** in all) has a split that still contains 1432. The shipped
  `data/checks-fixtures.json` (864,678 bytes) holds every one of the 2,074
  cores with its source, split and an explicit forbidden quadruple; two
  independently written programs (`code/primary.py`, word substitution;
  `code/coordinate.py`, integer coordinates) re-enumerate the list and must
  agree. The fixture regenerates exactly from the programs (about 5 s at the
  write; 43–49 s at placement, under load; see "Rerun").
- **The finite tests prove nothing asymptotic.** The other fixture values
  (counts, minima distributions, skeleton digests through size 8, 75,419
  restriction commutations, 110,459 interior centres, 314 inflations, the
  collision, the 106 versus 107 board counts) are cross-checks of the
  combinatorics, not part of any proof of Theorem 1.1.
- **Priority is not established** beyond the source's scoped search; see
  Remark 8.1 for the upper order.

## What it proves

`b_n` counts permutations of `[n]` with exactly one occurrence of 1432; by
reversal this is OEIS A224182 (defined with 2341, offset 1). `A_n =
|Av_n(1432)|`, proved equal to `|Av_n(1234)|` (A005802). Statement numbers
follow the section counter and are the delivered ones.

- **Theorem 1.1 (`u1432:thm:main`)**: the bounds and constants above, and
  `log b_n = n log 9 − 3 log n + O(1)`. All computer-free.
- **Section 2**: minima skeletons as full matchings of a Ferrers board
  (Lemma 2.1); `N_1432(π)` as a sum of supports of contained decreasing triples
  (equation (6)); for each fixed skeleton, equally many
  1432- and 1234-avoiders (Proposition 2.2, the shape-Wilf step through
  Krattenthaler's growth diagrams); Remark 2.3: the correspondence does not
  transfer occurrence counts (106 versus 107 on an explicit board).
- **Section 3**: `D_{m,r} ≤ C(m,r)² Cat(m−r)`, so the minima fraction of a
  uniform avoider tends to `1/3`: `M_m ~ (m/3)A_m`.
- **Section 4**: inflating a marked left-to-right minimum into a 1432 block
  injects marked avoiders of size `m` into one-occurrence permutations of size
  `m+3` (Proposition 4.1); Corollary 4.2: for `τ_k = 1 ⊕ δ_k`,
  `liminf b⁽ᵏ⁾_n/(nA⁽ᵏ⁾_n) ≥ k^{−2k−1}` (no upper bound claimed).
- **Section 5**: the Burstein-type split (adapted from Burstein's 321
  construction), the four forced singleton regions (R1)–(R4), the eight-case
  proof that the split avoids 1432 (Lemma 5.1), the exact marked inverse, and
  an explicit collision showing the mark is needed.
- **Section 6**: the constants `C_− = C_0/2187`, `C_+ = 81C_0`;
  `b_{n+1} ≥ 2b_n` (`n ≥ 4`); Corollary 6.1: the threshold
  `N(x) = min{n ≥ 4 : b_n ≥ x}` satisfies
  `⌈T_{C_+}(x) + o(1)⌉ ≤ N(x) ≤ ⌈T_{C_−}(x) + o(1)⌉` with
  `T_C(x) = (log x + 3 log log x − 3 log log 9 − log C)/log 9`; the unrounded
  endpoints differ by `11/2`, so `N(x) = (log x + 3 log log x)/log 9 + O(1)`.
- **Section 7**: Theorem 7.1, the exact image (computer-assisted, above).

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Remark 6.2 (`u1432:rem:lambert`)**: the inverse is an instance of the
  transseries volume's `p0:thm:lambert-core` with `a = log 9`, `b = −3`
  (large solution `X = (3/λ)(−W₋₁(−(λ/3)e^{−(L−log C)/3}))`, whose two-term
  expansion is `T_C`), and `N(x)` is the integer staircase of
  `p0:def:three-inverses`, so `p0:thm:staircase`(1) applies to every admissible
  interpolation; the source proves its bracket directly from envelopes.
- **Remark 6.3 (`u1432:rem:nonalg`)**: the generating function of A224182 is
  **not algebraic** — Theorem 1.1 makes `z + z² + z³ + B(z)` satisfy the
  hypotheses of Bóna–Burstein's Lemma 6.3 (arXiv:2101.00332v3; proof credited
  there to Alin Bostan) with `K = 9`, `m = 3`. The source does not state this.
  Bóna–Burstein's own theorems do not cover 1432 (their family `321 ⊖ ρ` is
  only 4321 in length four).
- **Remark 8.1 (`u1432:rem:mrr`)**: on the upper order and Mansour, Rastegar
  and Roitershtein (see next section).
- Section 1.1 (provenance, the sources as the write read them, relation to
  the repository, reading conventions, collected non-claims), the note at the
  end of Section 8.1 (shipped layout, reruns), and Section 9.1.

## What was known: the upper order and MRR

The source says that the proof of Theorem 3.1 of Mansour, Rastegar and
Roitershtein (SIAM J. Discrete Math. 34(2) (2020) 1011–1038; arXiv:1905.05646)
"displays the stronger one-step estimate `f_m^ξ(n) ≤ n Σ_{r<m} f_r^ξ(n−1)`",
which for `ξ = 1432`, `m = 1` "would give `b_n ≤ nA_{n−1}` and hence the same
upper order", and claims no novelty for the upper order. The write read that
proof (arXiv v1, pp. 28–29, and the published author manuscript, PubMed
Central PMC7144682): the display is printed there, but it is derived from one
sentence — delete the leftmost letter of the leftmost occurrence and rename —
and that map recovers `π` only with the position **and the value** of the
deleted letter, so the argument as printed gives the factor `n²`, not `n`.
The fibres do exceed `n`: `4571263 ∈ Av_7(1432)` has nine preimages in `S_8`
(the largest fibre is 2, 4, 6, 9, 12 for `n = 5, …, 9`); Remark 8.1 proves
the example by hand. With `n²` one gets only `b_n ≤ n²A_{n−1} = O(9ⁿ/n²)`,
one power short. MRR's Theorem 3.1 (equal exponential rates) is unaffected.
So, among the sources read, **the marked split of Section 5 is the only
complete proof of `b_n = O(9ⁿ/n³)`**; whether the factor-`n` inequality holds
is Question 4 (no violation in brute force; if true it gives `limsup ≤ 1/9`).
The placement commit `e85586b7c` said "the upper order was known
(Mansour-Rastegar-Roitershtein)"; this qualifies it.

## What is not claimed

From the source, kept in the article (collected at the end of Section 1.1):

- No leading equivalent, no convergence of `b_n/(nA_n)`, no proof of the
  candidate `3/80` (Conway–Guttmann's conjectured *ratio* `C_1/C_0`, not
  `C_1`), no D-finiteness. The two `o(1)` errors are not asserted equal or
  effective; the inverse width concerns unrounded endpoints, "not an exact
  count of admissible integers or a certified finite numerical threshold".
- No matching upper bound for `1 ⊕ δ_k`, `k ≥ 4`; no limiting density of
  eligible centres.
- No novelty for the upper order; no worldwide priority claim; the source
  check was "scoped, not an exhaustive worldwide literature review".
- Theorem 7.1 is computer-assisted, the main theorem is not; the numerical
  cross-checks and the archive seal are not formal verification, a digital
  signature or proof of an amplitude. The Backelin–West–Xin full text was not
  retrieved; Burstein's paper does not by itself prove Lemma 5.1.
- "No repository publication, outside contact, or external submission is part
  of this deliverable."

The write adds: its numbers (Section 9.1) are exact ratios of OEIS terms or
floating-point extrapolations and certify no limit.

## Further questions

Section 9.1 of the article ("Further questions and research",
`u1432:sec:further`) states every unproved claim as an open question with its
source, sketch and what is missing (Vladimir's standing rule of 4 October
2026). **Nothing in the source was found to be wrong.** One external
attribution is qualified (Remark 8.1).

1. **Does `b_n/(nA_n)` converge, and to `3/80`?** (`u1432:q:limit`; source;
   Conway–Guttmann Section 5.3, who estimate `0.0375 ± 0.0005` from the 18
   OEIS terms and 26 further approximate terms). *Recomputed at the write*
   from the OEIS terms (`n ≤ 18`) and exact `A_n`: `r_n = b_n/(nA_n)` =
   0.0369735, 0.0375056, 0.0378384, 0.0380455, 0.0381713, 0.0382435,
   0.0382801, **0.0382927**, 0.0382892 at `n = 10, …, 18`. It exceeds `3/80`
   from `n = 11`, increases through `n = 17` and **decreases for the first
   time at `n = 18`** (by `3.5·10⁻⁶`). Polynomial extrapolations in `1/n`
   (degrees 1–4, last 2–5 terms) give 0.0382, 0.0361, 0.0367, 0.0370. The
   placement record called the ratio "above 3/80 and rising"; the turn at
   `n = 18` corrects that reading. Nothing here is a bound, and 18 terms
   cannot separate `3/80` from nearby values.
2. **A limiting density of eligible centres** (`u1432:q:density`): by
   Theorem 7.1, `b_n/(nA_n)` converges iff the mean number of eligible centres
   of a uniform avoider of size `n+2`, divided by `n`, does; `3/80`
   corresponds to `n/2160`.
3. **Sharper constants, narrower bracket** (`u1432:q:constants`).
4. **The one-step inequality with the factor `n`** (`u1432:q:mrr`):
   `b_n/(nA_{n−1})` rises from 0.0417 (`n = 4`) to 0.2787 (`n = 18`); brute
   force over every `m`, `n ≤ 7`, for seven patterns of length 3 and 4 finds no
   violation.
5. **A matching upper bound for `τ_k`, `k ≥ 4`** (`u1432:q:tau`).
6. **A computer-free sufficiency proof for Theorem 7.1** (`u1432:q:image`).
7. **D-finiteness** (`u1432:q:dfinite`): not algebraic (Remark 6.3); D-finite
   or not is open.
8. **External inputs and priority** (`u1432:q:external`).

## Checks made at intake

On copies (5 October 2026; Windows, Python 3.14.4, standard library only):

- At placement (batch-105 dossier), in the delivered layout:
  `verify.py check` PASS (3 s); `replay` and `-O replay` PASS (43–49 s; the
  two `replay-result.json` files identical to each other and to
  `checks/fixtures.json`); `selftest` PASS, 51 tests (238 s); `manifest.json`
  9/9 entries verified. `build`, `pack` and `reproduce` (pdfTeX and frozen-PDF
  comparison) were not run.
- At the write, on a fresh extraction of the archive from `60f54ea06` (route A
  below): `check` PASS; `replay` and `-O replay` PASS in about 5 s each, both
  outputs byte-identical to the shipped `data/checks-fixtures.json`. On copies
  of the shipped programs (route B): `replay.run()` reproduces the fixture's
  content exactly (about 4 s). All 8 staged files are byte-identical to the
  archive.
- Independent intake programs: the split exhaustively for `n ≤ 10`; the
  bounds (2) for `n ≤ 9`; `b_n` by brute force for `n ≤ 10` against the OEIS;
  `|Av_m(1432)| = |Av_m(1234)|` for `m ≤ 6`; the collision, the sole-support
  example and the 106/107 counts. At the write: `b_n` by brute force for
  `n ≤ 8`, exact `A_n` by the hook-length formula, the ratios above, the MRR
  fibres for `n ≤ 9`, the one-step test, and `n⁴A_n/(C_0 9ⁿ)` = 0.8975,
  0.9469, 0.9730, 0.9864 at `n = 50, 100, 200, 400`.
- The dossier read the manuscript in full and checked by hand the eight cases,
  the inflation argument and its `τ_k` version, the entropy maxima, the
  constants `1/2187`, `81`, `11/2`, monotonicity and the restriction reduction
  of Theorem 7.1. No error.
- Sources read by the write: OEIS A224182 (revision #11, 3 Sep 2026);
  Conway–Guttmann, EJC 32(1) (2025) P1.3, Sections 4, 5.3, 5.5 (the 5.5 slip
  naming A224182 for class V is real, as the source says; their Section 4 makes
  it too); MRR (above); Bóna–Burstein Lemma 6.3 and Theorems 4.1, 5.5, 6.2;
  Nakamura arXiv:1301.5080 Section 3.2, Theorem 4 (located); Krattenthaler
  Theorems 1–3 (located); Burstein, EJC 18(2) P21 (located). Not read: Regev;
  Backelin–West–Xin.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq; no formal file treats pattern occurrences. Placement in the collection
confers no formal status.

**Neighbouring reports** (paths under `SetTheory/Cardinals/docs/reports/`):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a217057-unique-pattern-occurrences`
  (same batch; **see also**): exactly one 1234 (A217057), 1243 (A224179) and
  12345 (A224248), bundle Reports 134–138 and 140. It shares the normalizer
  `A_n = |Av_n(1234)|` and Regev's `C_0`, and its Report 136 proves
  non-algebraicity of the A224179 generating function from the same
  Bóna–Burstein Lemma 6.3 as Remark 6.3 here. The methods otherwise share
  nothing (tableau spine, strips and unitary integrals, amplitudes there;
  minima skeletons, Ferrers boards and a split, an order here); neither source
  cites the other. Note: Report 136 writes `b_n` for A224179, not A224182.
- `enumerative-combinatorics/a273821-first-pattern-failure`, Part II,
  "A worked example: first failure of 1432" (`fpf:lp:sec:example`): the
  patterns `τ_r = 1 ⊕ δ_r` of Corollary 4.2, through a different statistic.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a047874-long-increasing-subsequences`:
  `A_n` is the number of permutations with longest increasing subsequence at
  most 3, a partial row sum of A047874.
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (`p0:thm:lambert-core`, `p0:thm:staircase`): Corollary 6.1 is an instance
  (Remark 6.2); no novelty is claimed for the inversion.

**Stale claims.** The manuscript makes no claim about the repository, and
before batch 105 no file mentioned A224182, A005802, Conway–Guttmann, Regev,
Bóna–Burstein or Backelin–West–Xin. Nothing to correct.

## Notation

A table at the end of Section 1.1 fixes the letters the manuscript reuses,
with tempting false readings: `b_n` (A224182 here, A224179 in Report 136,
filed in `a217057`),
`A_n` (equal cardinalities, not equal sets), `N_1432(π)` versus the threshold
`N(x)`, `M_n` versus Report 136's marks `M(σ)`, `C_0`/`C_1`/`C_±` (`3/80` is
`C_1/C_0`), core values `a, b, c, d` versus split points `B, C, D, X, Y`, `k`
(a core position, and the tail length of `τ_k`), `K`, `δ`/`δ_k`, `D_{m,r}`,
`λ = log 9`, `L = log x`, (R1)–(R4), and Conway–Guttmann's `ψ^{III}_r(n)`.
No symbol was renamed.

## Labels

Every label carries the prefix `u1432:` (none existed in the repository). The
manuscript's 34 labels (`eq:` 18, `sec:` 7, `thm:` 2, `lem:` 2, `prop:` 2,
`cor:` 2, `rem:` 1) were prefixed before anything cited them,
and every `\ref`/`\eqref` was updated. The write added 14:
`u1432:sec:provenance`, `u1432:rem:lambert`, `u1432:rem:nonalg`,
`u1432:rem:mrr`, `u1432:sec:questions` (the delivered Section 9, unlabelled
before), `u1432:sec:further`, and the questions `u1432:q:limit`,
`u1432:q:density`, `u1432:q:constants`, `u1432:q:mrr`, `u1432:q:tau`,
`u1432:q:image`, `u1432:q:dfinite`, `u1432:q:external`. The report has 48
labels; a build of the delivered text and of this one give all 34 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections and the added displays are unnumbered, so no
theorem or equation number moved.

## Files

```text
README.md                    this guide (replaces the delivery README)
article.tex                  the report (delivered Report139.tex; labels prefixed, [write] additions)
article.pdf                  compiled report, 17 pages
SOURCES.md                   the source-provenance record (delivered SOURCES.md)
code/verify.py               integrity, replay, self-test, build and pack tool (delivered at the package root)
code/primary.py              exact implementation 1: word substitution (delivered code/)
code/coordinate.py           exact implementation 2: integer coordinates (delivered code/)
code/replay.py               combines and cross-checks the two (delivered code/)
data/checks-fixtures.json    sealed fixture with the 2,074-case certificate (delivered checks/fixtures.json)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery (checked again at the write).

**Not shipped**, recoverable from the arrival commit (next section):
`Report139.pdf` (the delivered 10-page PDF, 357,901 bytes); `manifest.json`
(1,270 bytes, a SHA-256 inventory of the other nine files; repository policy
ships no checksum manifests; verified at placement); and the delivery
`README.md` (8,172 bytes), staged at placement and replaced by this guide (its
content is summarized under "From the delivery README").

**Delivered text that names the delivery layout or files not shipped.**
`code/verify.py` hard-codes the package root as its own directory and a closed
inventory of `README.md`, `SOURCES.md`, `Report139.tex`, `Report139.pdf`,
`verify.py`, `checks/fixtures.json`, `code/*.py` and `manifest.json`: **it does
not run in this directory** (and its `README.md` check refers to the
delivered README, not this guide). `SOURCES.md` speaks of "this archive";
Section 8.1 of the article of "the offline archive", "this editable LaTeX
article and PDF". Use the routes below.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A224182_Polynomial_Growth_Order_and_Inverse_Bounds_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # ba737c317e23c15f344f81e3d6be5004014242d65578ada2f2a90a5afdfd642c, 1,316,107 bytes
cd "$T" && unzip -q a.zip     # creates Report139/
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only; no network. Isolated mode `-I`
is mandatory (the programs refuse to run without it). Never run anything in
the repository, and give output paths that do not yet exist outside the
package.

**Route A, delivered layout** (tested at the write):

```sh
cd "$T"; mkdir out
python3 -I -B Report139/verify.py check
python3 -I -B Report139/verify.py replay --output out/normal          # about 5-50 s
python3 -I -B -O Report139/verify.py replay --output out/optimized
cmp out/normal/replay-result.json Report139/checks/fixtures.json
cmp out/normal/replay-result.json /path/to/ProveIt/<this report>/data/checks-fixtures.json
python3 -I -B Report139/verify.py selftest --output out/selftest      # about 4 minutes
```

`build`, `pack` and `reproduce` (two fresh pdfTeX builds compared with the
frozen PDF, deterministic ZIP packing) need the recorded TeX installation and
were not run by the intake.

**Route B, from the shipped programs** (tested at the write; it skips the
integrity layer and checks the mathematics only):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a224182-unique-1432-order
T=$(mktemp -d); cp "$R/code/primary.py" "$R/code/coordinate.py" "$R/code/replay.py" "$T/"; cd "$T"
python3 -I -B -c "import sys, json; sys.path.insert(0, '.'); import replay; r = json.loads(json.dumps(replay.run())); print(r == json.load(open(sys.argv[1], encoding='utf-8')))" "$R/data/checks-fixtures.json"
```

It prints `True` (about 4 s at the write). Use `py` where `python3` is not on
the path.

## Build the PDF

pdfLaTeX (geometry, fontenc, lmodern, microtype, amsmath, amssymb, amsthm,
booktabs, hyperref, and array for the write's table); the bibliography is
embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 5 October 2026: 17 pages;
no errors or warnings, no undefined references or citations, no multiply
defined labels, no duplicate PDF destinations, no overfull or underfull
boxes. The delivered source built the same way gives 10 pages with one
`amsmath` warning (`\atopwithdelims`, from `\choose`); the write typesets the
three binomials with `\binom` (identical output). The article keeps the
delivered preamble lines that suppress PDF dates and trailer identifiers; the
delivered byte-identity check of the PDF applies to the delivered
`Report139.tex` under the delivering TeX installation, not to this build.

## From the delivery README

The delivery README (replaced by this guide) described "a self-contained
offline companion" with the article, its PDF, "two independent exact integer
implementations, a complete finite obstruction certificate, a strict
read-only verifier, and source provenance"; it stated that the main order
proof is computer-free and that the package "does not prove a leading
equivalent, convergence of b_n/(n A_n), the candidate amplitude ratio 3/80,
or D-finiteness". It documented the commands of route A (`check`, `replay`
normal and `-O`, `selftest`, `build`, `pack`, `reproduce`, and a
maintainers' `seal` that writes a proposed manifest to an external file); the
two implementations (old values `3v`, new values `3c−1`, `3c+1`; 46,224
permutations of sizes 4–8, 5,102 single-occurrence sources); the certificate
(zero-based indices; every record reconstructed by both programs); the
integrity rules (closed inventory, strict JSON, rejection of symlinks,
duplicate keys, non-finite or boolean numbers; output paths must not exist);
and that the seal "is an integrity and reproducibility seal, not an
authenticated digital signature or a security sandbox for hostile code". Its
"Scope of conclusions" repeated the non-claims above and that "the published
MRR proof displays a stronger one-step upper inequality" that the report
does not rely on (see Remark 8.1 for what that display rests on).

## Rights

Repository contents are MIT-0. The shipped fixture holds recomputed values
only, no OEIS data file. The article quotes OEIS terms of A224182 (through
`b_18`) and ratios computed from them; OEIS content is published by The OEIS
Foundation Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those
terms remain under that licence. Nothing was submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A224182; Nakamura (arXiv:1301.5080,
  2013); Conway and Guttmann, EJC 32(1) (2025) P1.3; Burstein, EJC 18(2)
  (2011) P21; Backelin, West and Xin, Adv. Appl. Math. 38 (2007);
  Krattenthaler, Adv. Appl. Math. 37 (2006); Regev, Adv. Math. 41 (1981);
  Mansour, Rastegar and Roitershtein, SIAM J. Discrete Math. 34(2) (2020).
  Added by the write: Bóna and Burstein, arXiv:2101.00332v3; the transseries
  volume of this repository.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 105 of `docs/incoming`, bundle Report 139; arrival `60f54ea06`,
  placement `e85586b7c`, written 5 October 2026. Single source, so no merge
  choices. The delivered `Report139.tex` is shipped as `article.tex`; the
  delivered programs, fixture and `SOURCES.md` as listed above.

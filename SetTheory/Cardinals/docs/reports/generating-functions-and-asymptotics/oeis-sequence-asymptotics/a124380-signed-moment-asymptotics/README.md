# Asymptotic Expansions and Inversion for A124380

**An exact signed-moment decomposition, both saddle sectors to every fixed order, a Lambert-normalised smooth inverse and a conditional integer-threshold rule**

A research report dated 1 October 2026, built from one manuscript. The
delivery names no author or tool (its author line reads "Research report").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 06 | batch 77, manuscript 06 | `a124380-reproducibility.zip` (wrapper `a124380-asymptotics/`, main file `a124380-asymptotics.tex`, 593 lines, 14-page PDF) | none | `4f11bc9c0` (arrival `096ee7b87`) | the whole article, Sections 1–8 and Appendices A–B |

**Status: unrefereed; not formalized; AI-assisted delivery channel.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq. Its
"mathematical review" record (`data/mathematical-review.json`) is the
delivery's own and names no reviewer.

For

    sum_{n>=0} a_n z^n = sum_{k>=0} z^k prod_{j=1}^{k} (1 + j z)
        (OEIS A124380: 1, 1, 2, 4, 9, 22, 57, 157, 453, 1368, 4296, ...)

with `x = √(n/2)`, `L = log x`, `B = x²(2L − 1)`, the article proves:

- **Theorem 2.1** an exact decomposition `a_n = I_n + (−1)^n J_n` into a
  positive moment `I_n = ∫_0^∞ t^(n+2t+1) e^(−t²)/Γ(1+t) dt` and a signed
  moment `J_n = ∫_0^∞ t^(n−2t+1) e^(−t²)/Γ(1−t) dt`;
- **(1.3), Theorems 4.1 and 5.1** the multiplicative equivalent
  `a_n ~ (e^(1/2)/2) x exp{B + x(L+1) + L²/8}` (more than the OEIS
  logarithmic conjecture of Kotěšovec, 2024) and every fixed-order relative
  expansion, both in exact-saddle form and with coefficients `q_j(L)`
  polynomial in `L` (degree ≤ 3j), with the logarithmic coefficients
  `P_1 … P_4` explicit;
- **Proposition 3.2, Theorems 6.1 and 6.2** the signed sector is
  exponentially smaller (`|J_n|/I_n ≤ exp{−2x(L+1) + O(L²)}`) and has its own
  every-order expansion `J_n = 𝓜_n^− {Im(e^(iθ_n) Σ q_j^−(L)/x^j) + O(…)}`,
  `θ_n = πx − π(L+2)/4`, with the error measured against the amplitude
  `𝓜_n^−`, so it stays valid near zeros of the sine; and the exact identity
  (6.7) `q_j^−(L) = (−1)^j q_j(L − iπ)`;
- **Corollary 5.2** eventual strict log-convexity, with
  `log(a_{n−1}a_{n+1}/a_n²) ~ 1/(2n)`;
- **Theorem 7.1** the inverse `ν(y)` of the continuation `s ↦ log I_s`:
  with `X = √(y/W(y/e))`, `ν(y) = 2X² + Σ_{j≤M} b_j(Λ) X^(1−j) + O(…)`,
  an all-orders recurrence (7.5)–(7.6), `b_0 … b_4` explicit (Appendix A),
  and implicit inverses (7.9);
- **(7.10)** a conditional certification rule for the integer threshold
  `T(y) = min{n : a_n ≥ e^y}` from certified interval data.

The combinatorial models are prior work, credited in the article:
Chen–Fan–Zhao (2010; partial matchings avoiding neighbour alignments,
Theorems 1.1 and 2.1) and Cerbai–Claesson–Sagan (2024; restricted-growth
words, Theorem 4.5 and Lemma 4.6); Temme's uniform Stirling-number
asymptotics (1993) is the nearest analytic precedent.

## What is not claimed

Every limitation and priority caveat of the delivery is kept, in the
article or (for the README-only ones) in a `[write]` note and here:

- **No publication priority**: a targeted literature check found no
  sequence-specific relative asymptotic theorem of this form, which neither
  establishes priority nor exhausts the literature. The models and their
  precedence are established work.
- No convergence and no optimal truncation of the formal series; no
  complete exponential, resurgent or transseries classification.
- No relative equivalent for `J_n` uniform in `n`: the oscillatory error is
  normalised by the exponential amplitude, not by a possibly tiny or zero
  sine. A finite algebraic truncation of `I_n` generally has an error much
  larger than `J_n`; the smaller sector describes the exact difference
  `a_n − I_n` only.
- No unconditional rounding: `T(y) = ⌈ν(y)⌉` is **not** asserted, and the
  `O`-constants of Sections 4–7 are not certified finite-`n` bounds; the
  rule (7.10) needs separately certified `η`, `m` and `[ℓ, u]`.
- The numerical tables and quadratures are diagnostics, not interval
  certificates (the quadratures truncate Gaussian tails twenty units from the
  saddle).
- **Open questions** (from the delivered README; printed in a `[write]` note
  at the end of Section 8): (1) uniformity of the bivariate identity (2.6)
  when the record-count fugacity varies with `n`, and the resulting laws for
  the number of records; (2) an efficient certified integer-threshold
  algorithm from explicit constants and interval quadrature, including levels
  exponentially close to an integer crossing; (3) the large-order growth and
  optimal truncation of both coefficient families, related to the signed
  sector without assuming a transseries; (4) how small `J_n` can be along
  integer subsequences, and how its sign changes are governed by `θ_n`.

## Labels and the write

Every label carries the prefix `sma:`. The 63 delivered labels were
prefixed (44 references updated) before anything else cited them, and the
write added one, `sma:provenance`: **63 → 64**. Section, theorem and
equation numbers are the manuscript's own (equations are numbered within
sections) and none changed. No statement, proof or number of the manuscript
was changed and no symbol renamed; the preamble gained `xurl` and the
`writenote` environment.

Six `[write]` notes were added (all of 2 October 2026):

1. a new unnumbered section *Provenance, status and reading conventions*
   (after the abstract): provenance, pin, status, the replays and an
   independent check of the first terms, `q_1` and `q_2`;
2. in the same section, a table of reused letters (`x, L` vs `X, Λ` and
   Appendix A's `L = Λ`; `y` as a local offset and as a **logarithmic**
   level; `B` vs Bernoulli `B_{2r}`; `𝓜_n`, `M_n(a)`, `M`; `m`; `μ` vs
   `μ_m`; `c = 1/2 − log 2` vs unspecified `c, C`; `A`; `R`; `K`; `q_j`,
   `P_j`; `E` vs the complex functional `𝓔`; `N`; `ν`, `T`);
3. after Theorem 7.1: the Lambert normalisation is the inverse-Gamma core
   (`T = X²`: `T(log T − 1) = y`), an instance of repository results, no
   novelty claimed (below);
4. after (7.10): the rule has the shape of `p0:thm:staircase` (2); the
   generic arithmetic is formalized (below);
5. at the end of Section 8: the delivered README's four research questions;
6. at the end of Appendix B: the shipped names.

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered as a124380-asymptotics.tex)
article.pdf                        compiled report, 16 pages
code/replay_coefficients.py        exact positive-sector phase, q_j and P_j to any order (JSON to stdout)
code/replay_inverse.py             exact d_j and b_j of the inverse to any order (JSON to stdout)
code/replay_oscillatory.py         exact q_j^- (sine/cosine parts) of the signed sector (JSON to stdout)
code/derive_real_laplace.py        independent direct symbolic derivation through order four (run by verify_all.py)
code/verify_all.py                 phase/Gaussian cross-checks, inverse composition, 15 initial terms, identity (2.2) to 60 digits, diagnostics to n = 1000
code/verify_oscillatory.py         complex-shift identity, negative-sector expansion, amplitude-scaled quadratures to n = 10000
code/check_sector.py               first correction at the negative real saddle, quadratures to n = 10000
code/independent_checks.py         independent finite-product, explicit-moment and inverse-composition checks; every Appendix A polynomial
code/build.sh                      delivery-state tool: builds a124380-asymptotics.pdf (delivered at the archive root)
code/package_release.py            delivery-state tool: writes SHA256SUMS and the release zip (delivered at the archive root)
data/positive-order4.json          recorded: replay_coefficients.py --order 4
data/positive-order6.json          recorded: replay_coefficients.py --order 6
data/inverse-order4.json           recorded: replay_inverse.py --order 4
data/oscillatory-order4.json       recorded: replay_oscillatory.py --order 4
data/verification.log              recorded stdout of verify_all.py
data/oscillatory-elementary.log    recorded stdout of verify_oscillatory.py
data/oscillatory-saddle.log        recorded stdout of check_sector.py
data/independent-checks.log        recorded stdout of independent_checks.py
data/mathematical-review.json      the delivery's review record (scope, checks, limitations; hashes the delivered TeX)
data/visual-qa.txt                 the delivery's page-by-page visual check of its 14-page PDF
data/requirements.txt              sympy==1.14.0, mpmath==1.3.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`4f11bc9c0` is the delivered `a124380-asymptotics.tex` byte for byte; the
write changed only labels and the preamble and added the notes above. The
four `.log` files are matched by the root `.gitignore` (`*.log`) and were
force-added at placement.

**Renames at placement.** `receipts/X` → `data/X` (same file names);
`requirements.txt` → `data/requirements.txt`; `build.sh` and
`package_release.py` (archive root) → `code/`; the `code/` scripts kept
their paths. **Not shipped** (all survive in the arrival commit, see
below): the delivered README (replaced by this guide; its content is folded
in here and in the article), the delivered 14-page PDF, and `SHA256SUMS`
(verified 24/24 at placement and retired).

**Delivered text that uses delivery names.** The article's Appendix B
(`receipts/`, "a README, dependency specification, and checksum manifest",
"the report PDF"; a `[write]` note gives the shipped names);
`code/build.sh` (`a124380-asymptotics.tex`, `receipts/`);
`code/package_release.py` (`a124380-asymptotics.pdf`, `.tex`, `README.md`,
`requirements.txt`, `build.sh`, `receipts/`, `SHA256SUMS`, the zip name);
`data/mathematical-review.json` (`a124380-asymptotics.tex`);
`data/visual-qa.txt` (`a124380-asymptotics.pdf`, 14 pages).

**Stale delivery records.** `data/mathematical-review.json` records the
SHA-256 of the delivered TeX; `article.tex` has since gained labels and
notes, so the hash no longer matches a shipped file (the delivered bytes are
in the archive and at `4f11bc9c0`). `data/visual-qa.txt` describes the
delivered 14-page PDF, not the 16-page `article.pdf`.

## Relation to the repository

**Formal status.** Placement in the collection confers no formal status. No
A124380 statement is formalized anywhere in the repository. The only
formalized ingredient touched is generic: `Fabius.staircase_ceil` and
`Fabius.staircase_separation`
(`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`),
rounding facts for an arbitrary strictly monotone function; they give no
formal status to (7.10).

**Instances of repository results, with no novelty claimed for the
method.** All in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:

- the Lambert normalisation (7.3) solves the inverse-Gamma core
  `T(log T − 1) = R` (`p6:sec:gamma`, `p6:eq:gamma-core-eq`) with
  `T = X²`, `R = y`, i.e. `w = W_0(y/e)`, `X² = y/w`; the general block is
  `p0:thm:lambert-core` / `p6:lem:core`, and the recurrence (7.5) is a
  reversion around that core of the kind in `p0:thm:lambert-centered` and
  `p0:thm:perturbed-inversion`. Only the core is shared: the lower-order
  terms of `log I_s` are not those of `log Γ`, and the report's own inverse
  is (7.7);
- the threshold rule (7.10) has the shape of the separation condition
  `p0:thm:staircase` (2); part (1) would need an exact interpolation of
  `a_n`, which `I_s` is not.

The expansions are Poincaré series with a separately controlled
exponentially smaller sector, not a transseries, which is why the report
sits in this collection and not in `Analysis/Transseries`.

**Neighbouring reports.** `oeis-sequence-asymptotics/a122399-surjection-diagonal`
and `a277364-bell-asymptotics` treat other Stirling-number sums by saddle
methods, and `a122399` also uses the inverse-Gamma core `p6:sec:gamma` for
its inverse initializer; no theorem is shared. (These pointers are made here
only; those reports are not edited by this write.)

## Rerun the checks

The checkers and generators write only to standard output and import their
siblings from their own directory, so they run in place from the report
directory without touching shipped files (Git Bash):

```sh
TMP=$(mktemp -d)
export PYTHONUTF8=1 PYTHONDONTWRITEBYTECODE=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/independent_checks.py   > "$TMP/independent-checks.log"
$PY code/verify_all.py           > "$TMP/verification.log"
$PY code/verify_oscillatory.py   > "$TMP/oscillatory-elementary.log"
$PY code/check_sector.py         > "$TMP/oscillatory-saddle.log"
$PY code/replay_coefficients.py --order 4 > "$TMP/positive-order4.json"
$PY code/replay_coefficients.py --order 6 > "$TMP/positive-order6.json"
$PY code/replay_inverse.py --order 4      > "$TMP/inverse-order4.json"
$PY code/replay_oscillatory.py --order 4  > "$TMP/oscillatory-order4.json"
for f in "$TMP"/*.log "$TMP"/*.json; do diff --strip-trailing-cr "$f" "data/$(basename "$f")"; done
```

Redirect to a scratch directory (`$TMP`), never into `data/`.
`PYTHONDONTWRITEBYTECODE=1` stops the sibling imports from leaving a
(git-ignored) `code/__pycache__/`. On Windows the redirected stdout
has CRLF line endings; the shipped files are LF, so compare with
`--strip-trailing-cr`. The delivery used Python 3.12.14, SymPy 1.14.0 and
mpmath 1.3.0. On 2 October 2026 (Windows, Python 3.14, same SymPy and
mpmath, on a scratch copy of `code/`, a loaded machine) all eight runs
exited 0 and all eight outputs were identical to the shipped ones apart
from line endings; times: `independent_checks.py` 120 s, `verify_all.py`
33 s, `verify_oscillatory.py` 34 s, `check_sector.py` 25 s, the generators
14–30 s each. Generator conventions: in `replay_inverse.py` the symbol `c`
means `1/2 − log 2`; in `replay_oscillatory.py` the symbol `p` means `π`.
Any finite `--order` is accepted; large symbolic orders can be expensive,
and asymptotic series need not improve at every successive order for a
fixed input.

**Delivery-state tools.** Never run `code/build.sh` or
`code/package_release.py` in this directory. `build.sh` changes into its own
directory (`code/`), creates `receipts/` and `.build/` there and compiles
`a124380-asymptotics.tex`, which is not there; `package_release.py` expects
the delivered root layout and, in it, rewrites `SHA256SUMS` and writes a
release zip. Both reproduce the **delivered** package; run them only inside
an extraction of the archive (see below).

## Build the PDF

pdfLaTeX with geometry, fontenc (T1), lmodern, microtype,
amsmath/amssymb/amsthm, mathtools, booktabs, array, hyperref, fancyhdr and
xurl. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 16 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull boxes. The log has one underfull `\hbox`
(badness 1348) in the bibliography entry for Cerbai–Claesson–Sagan; the
delivered text gives the same box and builds to 14 pages.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/a124380-reproducibility.zip > a124380.zip
unzip a124380.zip -d a124380-delivery   # files under a124380-asymptotics/
```

The archive (423,552 bytes) holds the delivered README, PDF and
`SHA256SUMS` besides the shipped files.

## Provenance

- One manuscript: batch 77, manuscript 06 (`a124380-reproducibility.zip`),
  arrival `096ee7b87`, placement `4f11bc9c0`, written in the batch-77 write
  phase (2 October 2026). No merge, so no merge choices.
- Pin: none; the delivery continues no ProveIt path. At placement no
  repository report treated A124380.
- External sources (as delivered): OEIS A124380 (consulted 1 October 2026);
  W. Y. C. Chen, N. J. Y. Fan, A. F. Y. Zhao, arXiv:1009.4535 (2010);
  G. Cerbai, A. Claesson, B. E. Sagan, arXiv:2408.06959 (2024); N. M. Temme,
  Stud. Appl. Math. 89 (1993) 233–243.

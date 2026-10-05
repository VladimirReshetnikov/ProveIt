# Growing Powers of Mahonian Coefficients

**A parity-sensitive theta crossover for sums of `r`-th powers of Mahonian
numbers when `r` grows like the inversion variance (context: OEIS A380274,
A380275)**

A research report dated 1 October 2026, built from one manuscript, printed
in full. Its author line is "Research note"; the delivered PDF has no author
metadata. It names no tool and no author.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 55 | batch 77, manuscript 55 | `oeis-mahonian-crossover-result.zip`, arrival commit `096ee7b87` (wrapper `oeis-mahonian-crossover-result/`, main file `mahonian_crossover.tex`, 10-page PDF; PDF, `SHA256SUMS` and `manifest.json` not shipped) | none: no ProveIt commit is named and no repository file is cited | `aa7345800` | Sections 1–9 (numbers as delivered), after an unnumbered report note |

**Status:** AI-assisted? Not stated by the delivery. Unrefereed, not
formalized. The proofs are backed by exact rational coefficient
calculations and by high-precision evaluations of exact Mahonian rows
(`n ≤ 322` by the producer, odd `n ≤ 483` by an independent check); these
check algebra and parity conventions, not the error bounds. The shipped
`audit.md` is the delivery's own review.

## What it proves

`M_n(k)` is the number of permutations of `n` with `k` inversions,
`S_n(r) = Σ_k M_n(k)^r` (real `r > 0`; for integral `r` it counts `r`-tuples
of permutations with equal inversion number), `V_n = n(n−1)(2n+5)/72` the
inversion variance, `μ = n(n−1)/4`, `δ = μ − ⌊μ⌋ ∈ {0, 1/2}` (by `n mod 4`),
`C_n = M_n(⌊μ⌋)` and `T_{n,r} = S_n(r)/C_n^r`. With
`Z_δ(q) = Σ_{x∈Z+δ} e^{−qx²/2}` and `Θ_δ(q) = e^{qδ²/2} Z_δ(q)`:

- **Theorem 1:** `T_{n,r_n}/Θ_δ(r_n/V_n) → 1` for every `r_n → ∞`; hence
  `T ~ √(2πV_n/r_n)` if `r_n/V_n → 0`, `T → Θ_δ(ρ)` if `r_n/V_n → ρ` along a
  parity class, `T → 1 + 2δ` if `r_n/V_n → ∞`, with first shell
  `T − (1+2δ) ~ 2q_n^{r_n}`, `q_n = M_n(⌊μ⌋−1)/C_n`, however fast `r_n`
  grows.
- **Corollary 2:** the common inversion count of `r_n` colliding random
  permutations, minus `μ`, tends to the discrete Gaussian on `Z + δ` in the
  critical window (total variation), to a normal law after scaling below
  it, and to the one or two modes above it.
- **Theorem 3:** an explicit uniform correction on compact windows,
  `T_{n,r} = Θ_δ(ρ_n a_[4](n)) − (81ρ_n/(25n⁴)) Ψ_δ(ρ_n) + O_K(n^{−5})`.
- **Theorem 4:** the unnormalized equivalent
  `S_n(r) = (n!/√(2πV_n))^r exp{−ρ_n(3n²/400 + 5883n/490000 + 13963/500000)} Z_δ(ρ_n)(1 + O(n^{−1}))`.
- **Theorem 6:** uniform expansions to every fixed order, by a formal
  generator over the rationals (Section 5).
- **Theorem 7:** on the fixed critical path `r_n = ρV_n`, a Lambert-`W_0`
  index inverse with `O(1/X)` error (`n = X − 1/8 + O(1/log X)`), an
  arbitrary-order real model with inverse error `O(n^{−L−4}/log n)`, and a
  discussion of discrete thresholds.

## What is not claimed

- **No fixed-power result.** The fixed-real-power equivalent with three
  corrections, including OEIS A380274 (`r = 3`) and A380275 (`r = 4`), is
  Wang's (*Fixed-Power Sums of Mahonian Coefficients*, June 2026, Zenodo
  DOI 10.5281/zenodo.20548010); his Remark 2 excludes varying `r`. The
  manuscript says so in its abstract and Section 9, kept verbatim.
- **No priority.** The targeted literature search (`literature.md`,
  1 October 2026) did not locate the theorem, but "this is not a priority
  certificate". The full Vilenkin–D'yachkov paper was not available, so its
  uniformity in Rényi order is unverified.
- No novelty for the method: Fourier recovery of microscopic curvature
  (Canfield–Janson–Zeilberger), discrete Gaussian theta normalizers
  (Agostini–Améndola, Nielsen) and high-order entropy limits are prior art.
- No convergence of the infinite expansion, no exponentially small
  remainder and no resurgent transseries (Section 5); no parity-independent
  critical-window limit; no certified onset for nearest-integer recovery,
  and no ceiling rule for arbitrary thresholds (Section 7).
- The numerical tables are consistency checks at 90 (producer) and 85
  (independent) digits, not interval certificates.

**Inversion mechanics.** Section 7's inverse is an instance of the
transseries volume
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`:
in `Z = log X − 1` the defining equation is `4Z + log Z = log(36y/ρ) − 4`,
which is `p0:thm:lambert-core` with `a = 4`, `b = 1` (branch `W_0`); the
correction `−g(X)/f'(X)` is the first-order term of
`p0:thm:perturbed-inversion`; the threshold discussion is the situation of
`p0:thm:staircase`. No novelty is claimed for the inversion mechanics; a
dated note in Section 7 says so.

## Notation

No symbol was renamed and no normalization changed. The manuscript reuses
`Y_n` (Corollary 2: a centred inversion count; Section 7: `log S_n(ρV_n)`),
`q`, `V`, `f`, `g`, `J`, `A`, `B`, `H`; the report note lists each pair.
The subscript of `Θ_δ` is the lattice shift. The neighbouring ballot-sum
report writes `Θ_τ(α) = Σ_j e^{−4τ(j−α)²}` with a scale as subscript; the
two are related by `Z_δ(q) = Θ^{tbs}_{q/8}(δ)` (dated note in Section 9).

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, and its place in the collection gives it no formal status. The only
related formal statement is the generic staircase lemma
`Fabius.staircase_separation` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, about
an arbitrary monotone interpolation, not about `S_n(r)`.

**Neighbouring report.** `a357825-theta-ballot-power-sums` (same category)
proves the same kind of crossover for high powers of ballot numbers: its
`tbs:thm:critical` is a critical theta regime with a varying phase, and its
research question Q6 asks for a reusable lattice-peak theorem for positive
triangular arrays. This report is a further instance (the Mahonian array,
shifts `0` and `1/2` only); it does not prove that general theorem, and Q6
stays open. Neither manuscript cites the other. No other report mentions
Mahonian power sums, A380274 or A380275 (repository search, 2 October 2026).
The pointer is made here and in the article's Section 9 note only; the
ballot-sum report is not edited.

*[Update, 5 October 2026, batch 98D.]* Question Q6 is now answered in a
sufficient-hypothesis form by Part II of `a357825-theta-ballot-power-sums`
(a general lattice-peak transfer theorem, labels `tbs:lpt:`), and its
Proposition 21.1 proves that this report's critical window is an instance,
with the local law from `mgp:eq:profileleading` and an exponential majorant
from log-concavity (a reorganization of this report's own proof). The
sentence above that "Q6 stays open" is superseded; the ballot-sum report
now also points here. Part II writes ϑ(q,δ) for this report's Z_δ(q). Dated
note after the Section 9 note of the article.

## Labels

Every label carries the prefix `mgp:`: the manuscript's 26 labels, prefixed
before anything cited them, and `mgp:sec:note` for the added report note
(27 in total). Theorem, equation and section numbers are the manuscript's
(checked against a build of the delivered `mahonian_crossover.tex`).

Changes to the manuscript's text: the label prefixes, the unnumbered report
note after the abstract, three dated `[write]` notes (Sections 7, 8 and 9),
PDF title metadata, and two preamble additions (`array`, a path macro). No
statement, proof, symbol or number was changed. A reciprocal note of 5 October 2026 (batch 98D), marked "[write,
2026-10-05]", follows the Section 9 note; it adds no label and changes no
number.

## Files

```text
README.md                           this guide (replaces the delivery README)
article.tex                         the report (delivered as mahonian_crossover.tex)
article.pdf                         compiled report, 12 pages
audit.md                            the delivery's own mathematical audit (as delivered)
literature.md                       the delivery's literature boundary, checked 1 October 2026 (as delivered)
code/derive_coefficients.py         exact rational weighted-Fourier coefficients (SymPy); prints to stdout
code/check_crossover.py             exact Mahonian rows, 90-digit evaluations (mpmath); writes three JSONs beside itself
code/audit_independent.py           independent Hermite/Edgeworth calculation, odd n to 483, inverse checks; writes beside itself
code/verify_results.py              regression checks; hashes mahonian_crossover.tex beside itself; writes verification.json
code/verify.sh                      runs the four programs with python3, writing beside the scripts
code/build.sh                       builds mahonian_crossover.tex beside itself
data/coefficients.txt               recorded output of derive_coefficients.py
data/numerical_checks.json          30 critical-window cases (rho = 0.2, 1, 5; n to 322)
data/endpoint_checks.json           30 subcritical and supercritical checks
data/unnormalized_checks.json       30 checks of Theorem 4
data/producer_checks.txt            stdout of check_crossover.py (per-n timings)
data/audit_independent_results.json independent symbolic and numerical results (30 cases)
data/audit_symbolic.txt             independent rational coefficients
data/independent_checks.txt         stdout of audit_independent.py
data/verification.json              output of verify_results.py
data/replay.log                     stdout of verify_results.py (byte-identical to verification.json)
data/quality_receipt.json           the delivery's PDF and audit receipt (hashes of the unshipped tex and PDF)
data/provenance.json                topic, sources and computation summary
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery; all have LF line endings.
`data/replay.log` is committed with `git add -f`, because the root
`.gitignore` ignores `*.log`.

**Renames.** Placement renamed `mahonian_crossover.tex` to `article.tex`,
moved the six scripts to `code/`, `receipts/producer_checks.txt` and
`receipts/independent_checks.txt` to `data/`, and every other output and
record to `data/`. Not shipped (all in the arrival commit): the delivered
PDF, `SHA256SUMS` (verified 24/24 at placement) and `manifest.json` (a
second SHA-256 ledger).

**Delivered text that still uses delivery names.**
- `code/verify_results.py` reads `numerical_checks.json`,
  `audit_independent_results.json`, `endpoint_checks.json` and
  `unnormalized_checks.json` beside itself, and asserts that the SHA-256 of
  `mahonian_crossover.tex` beside itself is the audited
  `dc2d592d…c3ce`. The shipped `article.tex` is the rewritten report, so
  the delivered manuscript must be taken from the placement commit (recipe
  below).
- `code/verify.sh` calls `python3` and writes `coefficients.txt`, the JSON
  outputs and `receipts/*.txt` beside the scripts; run in `code/` it would
  scatter outputs there. `code/build.sh` writes `receipts/` and `.build/`
  beside itself.
- `audit.md` gives its paths relative to `/workspace/shared/oeis-mahonian-crossover/`,
  a delivery workspace; `quality_receipt.json` and `audit.md` hash the
  delivered tex and PDF.
- The article's Section 8 says "the accompanying programs" and "the data
  file"; a dated note names the shipped files.

## Rerunning the checks

Run on a scratch copy in the delivered flat layout, never in place. From
this directory (Git Bash):

```sh
R=$(mktemp -d) && mkdir "$R/receipts" && cp code/*.py "$R/"
git show aa7345800:SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a380274-mahonian-growing-powers/article.tex > "$R/mahonian_crossover.tex"
cd "$R"
U="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$U derive_coefficients.py > coefficients.txt
$U check_crossover.py > receipts/producer_checks.txt
$U audit_independent.py > receipts/independent_checks.txt
$U verify_results.py > replay.log
```

Then compare each output with its counterpart in `data/` using
`diff --strip-trailing-cr` (Windows writes CRLF). On 2 October 2026 the four
steps took about 22 s, 11 s, 62 s and 2 s here; all passed, and every output
equalled the recorded one modulo CR, except that
`receipts/producer_checks.txt` differs in its per-`n` timing values. The
delivered manuscript (`git show aa7345800:…/article.tex`, the file placed
before this write) is byte-identical to the archive's
`mahonian_crossover.tex`; it can also be taken from
`git show 096ee7b87:docs/incoming/oeis-mahonian-crossover-result.zip`.
No delivered file was excluded as a heavy artifact (the largest data file is
27 KB), so nothing needs reconstructing.

## Build the PDF

pdfLaTeX with geometry, amsmath, amssymb, amsthm, booktabs, array,
microtype and hyperref. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX. It has 12
pages (the delivered manuscript alone builds to 10), with no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations and no overfull boxes. One underfull line remains in the
bibliography; the delivered manuscript has the same one.

## Provenance

- Batch 77 of `docs/incoming`, manuscript 55, archive
  `oeis-mahonian-crossover-result.zip`: arrival `096ee7b87`, placement
  `aa7345800`, written in the batch-77 write phase (2 October 2026). No pin.
- Inputs: Wang (2026, two author versions), Canfield–Janson–Zeilberger
  (arXiv:0908.2089), Agostini–Améndola, Nielsen, Vilenkin–D'yachkov (1998,
  abstract only), Bobkov–Marsiglietti (2019); `literature.md` also discusses
  Madiman–Melbourne–Roberto, Salminen–Vignat, Zhang and
  Helton–Hughes–Schlosser.
- Single source, so no merge choices. Write choices: the report note is
  unnumbered so that every number stays the manuscript's; the internal
  reuse of letters is tabulated, not resolved by renaming.

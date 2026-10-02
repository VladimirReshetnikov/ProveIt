# Asymptotic Enumeration and Inversion for A122399

**The diagonal of 1/(1 − u e^y(e^x − 1)): all-orders saddle expansion, exact contour, controlled inverse, block-count CLT and prime-power periodicity**

A research report dated 1 October 2026, built from one manuscript. The
delivery names no author or tool (its author line reads "A proof and
reproducible research report").

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 35 | batch 77, manuscript 35 | `oeis-a122399-research.zip` (main file `a122399-report.tex`, 389 lines, 8-page PDF) | none; a scoped index search at `76c0887a6` (`proof.md:9`) | `f76fcb566` (arrival `096ee7b87`) | the whole article, Sections 1–8 |

**Status: unrefereed; not formalized; AI-assisted delivery channel.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq.

For

    a_n = sum_{k=0}^{n} k^n k! S(n,k)        (OEIS A122399; 1, 1, 9, 211, 9285, ...)

the article proves:

- **(2.1)–(2.3)** an exact, absolutely convergent vertical-contour formula for
  the two-size numbers `A_{m,n}` (`a_n = A_{n,n}`), via the Mittag-Leffler
  identity (2.2), with an explicit nonasymptotic tail bound;
- **(3.5)** an all-orders saddle expansion of `A_{m,n}`, uniform for `m/n`
  in compact subsets of `(0, ∞)`, with the finite coefficient formula (3.4);
- **(4.1)** `a_n = C D^n (n!)^2 n^(-1/2) [1 − 0.0600744…/n + 0.0075945…/n^2 +
  0.0037132…/n^3 − 0.00036298…/n^4 + O(n^-5)]`, with
  `D = 3.161088653865…` (= OEIS A317855), `C = 0.327628285569…`, and `c_1`
  in closed form (4.2);
- **(5.1)–(5.4)** a controlled inverse along the sequence, a Lambert-W₀
  initializer with Newton steps, and integer-threshold ceiling envelopes;
- **(6.2)** a Gaussian limit for the number of occupied blocks, mean
  `μn + μ_0`, variance `σ²n`, `μ = 1/y = 0.8737024…` (the OEIS constant
  `r`), `σ² = 0.0889169…`;
- **(7.1)** `a_{n+φ(p^r)} ≡ a_n (mod p^r)` for every prime `p`, `r ≥ 1` and
  `n ≥ r`; in particular `p − 1` is a period mod `p` from `n = 1`, which
  proves the OEIS conjecture (Peter Bala, 2022) in that sense.

## What is not claimed

Every limitation and priority caveat of the delivery is kept in the article:

- The leading equivalent is Kotěšovec's (OEIS, 9 August 2018) and the growth
  constant was identified in 2013; neither is claimed as new. The methods are
  standard analytic saddle / ACSV methods; Khera–Lundberg–Melczer (lonesum
  matrices, a different denominator) is credited for directional and
  higher-order expansions. **No global novelty claim is made.**
- No least period in (7.1), and no strengthening of the prime-power case to
  `n ≥ 1` (the audit notes `a_1 = 1` and `a_3 = 211` differ mod 4).
- No canonical transseries sectors and no secondary-saddle expansion: the
  strip decomposition of Section 2 is exact but not claimed canonical, and a
  fixed-order truncation of (4.1) has algebraic, not exponential, error.
- No growing-direction or boundary-uniform statement (`m/n → 0` or `∞`).
- No local limit theorem, Edgeworth terms or large deviations for the block
  count.
- The O-constants of (3.5) and (5.1)–(5.4) are existence constants, not
  certified finite-input bounds; rounding a real inverse alone does not
  settle an integer boundary.
- The quadratures of the checks are high-precision diagnostics, not interval
  certificates. The finite checks do not replace the analytic proofs.
- The four questions of Section 8 are open.
- The delivery's repository search (1 October 2026) is scoped
  nonduplication evidence, not a proof of absence; no OEIS submission or
  other external write was made.

## Labels and the write

Every label carries the prefix `a122:`. The 14 delivered labels were
pandoc-generated section names (`results-and-attribution`, `proof`, …); they
were prefixed before anything cited them (nothing did), and the write added
one, `a122:provenance`: **14 → 15**. Section and equation numbers are the
manuscript's own, typed by hand (`secnumdepth` is 0; tags such as (2.1) are
fixed `\tag`s), and none changed. No statement, proof or number of the
manuscript was changed and no symbol renamed.

Six `[write]` notes were added (all of 2 October 2026):

1. a new unnumbered section *Provenance, status and reading conventions*
   (after *Results and attribution*): provenance, pin, status, the audit;
2. in the same section, a table of the letters the manuscript reuses (`p`
   for `1/(1+e^z)`, for `x/y` and for a prime; `r` for a Taylor index, a
   Newton count, a prime-power exponent and the OEIS constant; `x, y`; `a`;
   `m`; `C, C_J, E_J`; `μ`; `D`);
3. after (5.2): the initializer is an instance of the inverse-Gamma core
   `p6:sec:gamma` (`p6:eq:gamma-core-eq` with `T = √D N`, `R = √D L/2`) of
   the transseries volume, kin to `p6:lem:core` and `p2:thm:multi-scaling`;
   only the core is shared;
4. at the end of Section 5: the rounding remarks are `p0:thm:staircase`
   (1)–(2), whose generic arithmetic is formalized (below);
5. after the proof of (7.1): Bala's credit, the formalized surjection
   formula, the secant-number neighbour;
6. after the source list: what A317855 is (checked on 2 October 2026), the
   shipped names of the scripts, and the Fubini row `n = 0`.

## Files

```text
README.md                                  this guide (replaces the delivery README)
article.tex                                the report (delivered as a122399-report.tex)
article.pdf                                compiled report, 10 pages
proof.md                                   the delivered pre-layout Markdown source of the article
source_review.md                           the delivery's literature and repository-search record (1 Oct 2026)
quality_checks.md                          the delivery's release checklist
audit-independent_audit.md                 the delivery's independent mathematical audit
code/check_a122399.py                      producer: exact rational phase, saddle coefficients, exact comparisons to n = 800
code/export_exact_coefficients.py          producer: exact rational corrections through order four (reads phase_coefficients.txt)
code/verify_contour_inverse.py             producer: 9 contour/tail checks, 40 inverse checks (reads numerical_results.json)
code/verify_congruences.py                 producer: 1621 congruences of (7.1) in 23 prime-power cases
code/audit-independent_audit.py            the independent audit's script (delivered as audit/independent_audit.py)
code/make_report.py                        delivery-state tool: proof.md -> a122399-report.tex via pandoc
code/audit-check_transcription.py          delivery-state tool: proof.md vs a122399-report.tex (delivered as audit/check_transcription.py)
code/build.sh                              delivery-state tool: builds a122399-report.pdf
code/verify_all.sh                         delivery-state tool: the full replay, in place
data/test_output.txt                       recorded stdout of check_a122399.py
data/numerical_results.json                written by check_a122399.py
data/phase_coefficients.txt                written by check_a122399.py (f_0 ... f_16)
data/exact_coefficients.txt                written by export_exact_coefficients.py
data/contour_inverse_output.txt            recorded stdout of verify_contour_inverse.py
data/contour_inverse_results.json          written by verify_contour_inverse.py
data/congruence_results.json               written by verify_congruences.py (23 cases)
data/audit-independent_audit_output.txt    recorded stdout of the audit script
data/audit-independent_audit_results.json  written by the audit script
data/audit-transcription_checks.json       written by check_transcription.py (31 displays, 182 inline)
data/audit-reviewed_hashes.json            the audit's hash record of the delivery-state files
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`f76fcb566` is the delivered `a122399-report.tex` byte for byte; the write
changed only labels and added the notes above.

**Not shipped** (all survive in the arrival commit, see below): the delivered
README (replaced by this guide; its reproduction notes are folded in here),
the delivered 8-page PDF, `SHA256SUMS` (verified 28/28 at placement and
retired), and `audit/report-extracted.txt` (27,662 bytes of text extracted
from the delivered PDF; read by no script, and stale once the article is
rebuilt).

**Delivered text that uses delivery names.** The delivery was a flat
directory with an `audit/` subdirectory. Placement moved scripts to `code/`
and outputs to `data/`, and flattened `audit/X` to `audit-X`. Text still
naming the delivery layout: the article's source list (items 4–7; a
`[write]` note gives the shipped names), `proof.md` (same list),
`quality_checks.md` (`audit/independent_audit.md`),
`audit-independent_audit.md` (`independent_audit.py`,
`independent_audit_results.json`, `reviewed_hashes.json`,
`check_transcription.py`, `python audit/independent_audit.py`), and every
script: each reads and writes files **next to itself**, and the audit script
reads the producer outputs from its parent directory. `make_report.py`,
`build.sh`, `audit-check_transcription.py` and `verify_all.sh` name
`a122399-report.tex`/`.pdf` and `proof.md`.

**Stale delivery records.** `data/audit-reviewed_hashes.json`,
`data/audit-transcription_checks.json` and `quality_checks.md` record
SHA-256 values of the delivered README, TeX and PDF. The README and the
article have since been rewritten and the PDF rebuilt, so those three
entries no longer match shipped files; the code and data entries describe
the delivered bytes, which are shipped unchanged. The audit's statements are
about the delivered mathematics, which the article prints unchanged.

## Relation to the repository

**Formal status.** Placement beside the collection's other reports, and
near the Lean developments named here, confers no formal status. No A122399
statement is formalized anywhere in the repository: not (7.1), not the
asymptotic, not the CLT. What is formalized are generic ingredients:

- `Fabius.factorial_mul_stirlingSecond_eq_sum`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StirlingBasisChange.lean`),
  the surjection formula `k! S(n,k) = Σ_j (−1)^(k−j) C(k,j) j^n` used in the
  proof of (7.1). With Euler's theorem (Mathlib's `Nat.ModEq.pow_totient`)
  it makes (7.1) a small formalization target; none exists.
- `Fabius.fubini` (`Analysis/FabiusFunction/Lean/FabiusFunction/OrderedBell.lean`),
  the Fubini numbers `Σ_k k! S(m,k)`, which are the row `A_{m,0}` of the
  report's two-size array.
- `Fabius.staircase_ceil`, `Fabius.staircase_separation`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`),
  generic rounding facts for a strictly monotone interpolation; they give no
  formal status to (5.1)–(5.4).

**An instance of repository results, with no novelty claimed for the
method.** The inverse initializer (5.2) solves the core equation
`T(log T − 1) = R` of the inverse-Gamma section `p6:sec:gamma`
(`p6:eq:gamma-core-eq`; general block `p6:lem:core`, scaled family
`p2:thm:multi-scaling`) with `T = √D N`, `R = √D log A / 2`, and the rounding
remarks after (5.4) are `p0:thm:staircase` (1)–(2), all in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
Only the core is shared; the report's own all-orders inverse is `ν_J` of
(5.1). The main expansion is a single-scale Poincaré series, not a
transseries, which is why the report sits in this collection and not in
`Analysis/Transseries`. The same volume's chapter `q2:sec:fubini`
(`q2:thm:fubini`) gives the exact pole-lattice formula for the Fubini row
`n = 0`, which lies outside the compact-direction theorem (3.5).

**Neighbouring reports.**
`oeis-sequence-asymptotics/a277364-bell-asymptotics` treats another
Stirling sum, `Σ_{k ≤ n/2} S(n,k) ~ B_n`, by classical Bell/Stirling saddle
methods: same genre, different sequence and constants, no shared theorem.
`congruences-and-valuations/secant-number-periodicity` classifies when the
secant numbers A000364 are periodic modulo `m`, where the analogous OEIS
conjecture (period dividing `φ(m)`, pure from index one) fails; (7.1) is a
sibling in kind, with no shared result. (These pointers are made here only;
those reports are not edited by this write.)

**Stale sentence.** `proof.md:9` (not printed in the article) and
`source_review.md` say that a search of the repository index found no
A122399 or A317855 match. That was true on 1 October 2026; the only match
now is this report.

## Rerun the checks (on a scratch copy in the delivered layout)

The scripts read and write next to themselves, so running them from `code/`
would fail (inputs are in `data/`), and copying them into `data/` would
overwrite shipped outputs. Recreate the delivered layout in a scratch
directory (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir "$R/audit"
cp code/check_a122399.py code/export_exact_coefficients.py \
   code/verify_contour_inverse.py code/verify_congruences.py "$R"
cp code/audit-independent_audit.py "$R/audit/independent_audit.py"
cd "$R" && export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY check_a122399.py > test_output.txt          # writes numerical_results.json, phase_coefficients.txt
$PY export_exact_coefficients.py                # writes exact_coefficients.txt
$PY verify_contour_inverse.py > contour_inverse_output.txt
$PY verify_congruences.py                       # writes congruence_results.json
$PY audit/independent_audit.py > audit/independent_audit_output.txt
```

Run them in this order (each later script reads an earlier one's output),
then compare with `diff --strip-trailing-cr` against `data/` (Windows writes
CRLF; the shipped files are LF). The delivery used Python 3.12, mpmath 1.3.0
and SymPy 1.14.0. At placement (2 October 2026, on a heavily loaded machine)
the four producer scripts took 134 s, 64 s, 137 s and 88 s, all passed, and
all seven outputs came out identical to the shipped ones modulo line
endings. **The audit script was not replayed**: it was stopped at a
170-second cap without output, so expect several minutes; its shipped
output reports PASS with largest coefficient discrepancy `2.5e-80`.

**Delivery-state tools.** `make_report.py`, `audit-check_transcription.py`,
`build.sh` and `verify_all.sh` reproduce the **delivered** TeX and PDF, not
this `article.tex`: `make_report.py` regenerates `a122399-report.tex` from
`proof.md` with pandoc (and would overwrite a file of that name),
`check_transcription.py` asserts exactly 31 displays and reads
`a122399-report.tex` by name, and `verify_all.sh` calls bare `python` and
rewrites every output, the TeX and the PDF in place. Never run them in this
directory. `check_transcription.py` also hashes the delivered PDF, which is
not shipped, so replay both tools inside an extraction of the archive (see
*Retrieving the excluded delivery files*):

```sh
cd a122399-delivery/oeis-a122399-research
py make_report.py && py audit/check_transcription.py
```

On 2 October 2026, with pandoc 3.9.0.2, this regenerated
`a122399-report.tex` identical, modulo CRLF line endings, to the delivered
file and hence to `article.tex` as placed in `f76fcb566`, and the check
passed (31 displays, 182 inline expressions, 3 new).

## Build the PDF

pdfLaTeX with geometry, fontenc (T1), lmodern, microtype, amsmath/amssymb/amsthm, hyperref, xurl,
enumitem, booktabs and array. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 10 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes. The log carries 684
`fontmap entry ... already exists, duplicates ignored` warnings from the
delivered preamble's `\pdfmapfile{+lm.map}` lines (MiKTeX already loads
those maps); the delivered text gives the same 684 and builds to 8 pages.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/oeis-a122399-research.zip > a122399.zip
unzip a122399.zip -d a122399-delivery   # files under oeis-a122399-research/
```

The archive (395,389 bytes) holds the delivered README, PDF, `SHA256SUMS`
and `audit/report-extracted.txt` besides the shipped files.

## Provenance

- One manuscript: batch 77, manuscript 35 (`oeis-a122399-research.zip`),
  arrival `096ee7b87`, placement `f76fcb566`, written in the batch-77 write
  phase (2 October 2026). No merge, so no merge choices.
- Pin: none for the delivery; `proof.md:9` and `source_review.md` record a
  scoped search of the public repository index on 1 October 2026 at commit
  `76c0887a6`. The delivery continues no ProveIt path.
- External sources (as delivered): OEIS A122399 (inspected 1 October 2026)
  and A317855; Khera, Lundberg, Melczer, *Asymptotic Enumeration of Lonesum
  Matrices*, Adv. Appl. Math. 123 (2021), 102118, arXiv:1912.08850. The
  A317855 identification and Bala's credit were checked on the OEIS on
  2 October 2026.

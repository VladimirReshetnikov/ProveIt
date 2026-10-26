# CRT anchors and shared constants for Diophantine consistency

Research iteration 22 for Vladimir Reshetnikov and ProveIt, 26 October 2026
(UTC date). Start with the complete native TeX/PDF report in `report/`.

## Extract both ZIP parts

Extract BOTH `ConZFC_CRT_Anchors_Round22_2026-10-26_part1.zip` and
`ConZFC_CRT_Anchors_Round22_2026-10-26_part2.zip` into the same parent directory.
They populate one common release folder, with no overlapping files. Neither
part alone is the complete collection. Each archive is below 4 MB; `PARTS.json`
records the partition. No additional source download is needed for replay.

## Selected equations

Each ordinary proof, composed with its named inherited calibration, establishes
in ZFC that absence of solutions in the stated domain is equivalent to Con(ZFC).
It does not assume consistency or separately assert unsolvability.

| Unrestricted integer polynomial | Variables | Degree | Residuals | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Principal quartic | 215 | 4 | 154 | 7081 | 8880 |
| Balanced quartic | 215 | 4 | 154 | 7315 | 4096 |
| Low-height quartic | 215 | 4 | 154 | 16077 | 2304 |
| Dimension quartic | 214 | 4 | 153 | 7078 | 1052028 |
| Reciprocal companion | 212 | 10 | 151 | 55820 | 31104 |

The principal improves the previous 217-variable/7396-term/height8880 equation
in dimension and support at unchanged height. The balanced equation further
trades a little support for lower height. The 212-variable equation is NOT a
quartic: it merges the two power pools with one quintic residual. Its complete
expanded degree-ten polynomial is supplied, not merely a construction recipe.
The report prints all 154 principal quartic residuals and specifies the
reciprocal companion with its exact maps and finite arrays.

| Quartics with coefficients only plus or minus one | Variables | Terms |
|---|---:|---:|
| Minimum selected dimension | 493 | 24828 |
| Close dimension tradeoff | 494 | 24648 |
| Compact | 496 | 20548 |
| Compact tradeoff | 504 | 18297 |
| Balanced compact | 507 | 17524 |
| Balanced | 546 | 12139 |
| Retained sparse tradeoff | 557 | 11991 |
| Sparse | 605 | 8305 |
| Sparser | 701 | 7141 |

All have exact degree four and constant one. Monic constant-product and shared
scale-chain definitions give the new reductions. The unchanged 557/11991 point
is retained as a tradeoff. Five previous selected points have dominating new
successors; the 493-variable point buys fewer coordinates with greater support.

The three TEN-POSITIVE-INTEGER equations keep degree/operation pairs 240/82,
232/85 and214/87, but use a newly justified coherent whole Start4127 tuple.
Their four actual fixed coefficients shrink from 295388 to 97046 minimal unsigned
bytes, a 67.146% reduction. The arithmetic graph structures, degrees and costs
are unchanged; changing the fixed numerals generally changes the polynomial.
The full native-interface bridge, all coefficient bytes and reconstruction are
included. This tuple must not be partially substituted into the separate
six-port unrestricted-integer family. No new integer11 result is claimed here.

## Main new arguments

- A cofinally large even CRT index serves as the shared Pell semantic anchor.
  A larger label-weight parameter compensates for the removed label-size test.
  The actual local arithmetic circuit supplies a checked exponent majorant.
- Weighted and quadratic growth choices reduce the direct presentation while
  preserving the ordinary witness construction and exact source transformations.
- For the reciprocal companion, a proved cofinal subfamily has q congruent to 1
  modulo3. Writing q=3u+1 excludes bases 0 and −1, but deliberately permits unit
  cases. Reciprocal pooling restores the four original pool rows before the
  original sign bootstrap is invoked. The canonical construction uses original
  even H, F=t^K and a compatible mod3 choice; no odd-H substitution is made.
- Constant products and chained scales remain triangular monic definitions.
  Their full source pullbacks and all final coefficients are independently checked.
- The whole Start4127 coefficient specialization is proved through the native
  interface with fresh witnesses; it is not inferred from matching port names
  or numerical boxes.

## Reproduce offline

After extracting both parts, run from the common root with Python 3.10 or later:

    python3 -B verify_release.py

The standard-library verifier checks the exact inventory, makes a disposable
copy and executes all 15 steps in `VERIFY_PLAN.json`. Deep optimized steps set
PYTHONOPTIMIZE=1, including nested processes. The default performs the complete
height-one reconstruction and mutation checks and can take several minutes.
The original sealed tree is unchanged.

Save a fresh receipt outside the sealed directory:

    python3 -B verify_release.py --output ../new_verification.json

For file identity alone:

    python3 -B verify_release.py --integrity-only

The delivered height evidence records complete isolated normal/deep-optimized
rebuilds. The final archive audit also binds all its executable, configuration,
source, constructor and coefficient bytes to that completed snapshot, with
separately reviewed proof-prose corrections. A hash-bound reuse of a completed
check is not presented as a newly executed whole final root plan. The default
command above remains available to perform that full reconstruction afresh.

Rebuild the PDF in a working copy with ordinary TeX Live:

    sh report/build_report.sh

Use a fresh extraction for strict inventory verification after generating TeX
auxiliary files. See `CLOSURE_MAP.md` for dependencies and historic inventories.

## Scope

Comparison snapshot: ProveIt ef0c534c1ae1e312c61a2a9a5a3f18f5516fd42b.
Incoming Library/Git packets and additional consolidated sources166,168,170,171
are explicitly distinguished. Some consolidated trees were pruned upstream;
exact restored bytes and remaining gaps are recorded, not silently presented
as standalone complete original archives. All dependencies required by the
selected equations in THIS release are retained.

These are ordinary ZFC-equivalence proofs and exact finite artifact audits,
not new end-to-end Lean/Rocq certificates, global minimality claims, worldwide
priority claims or proofs of consistency. No repository was modified.

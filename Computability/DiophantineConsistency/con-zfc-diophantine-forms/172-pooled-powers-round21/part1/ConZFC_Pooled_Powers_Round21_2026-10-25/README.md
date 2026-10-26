# Pooled powers and quadratic projections for ZFC consistency

Research iteration 21 for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Start with `report/ConZFC_Pooled_Powers_Round21_2026-10-25.pdf`.

## Extract both ZIP parts

The full release is split across two ordinary ZIP files, each below 4 MB:

- `ConZFC_Pooled_Powers_Round21_2026-10-25_part1.zip`
- `ConZFC_Pooled_Powers_Round21_2026-10-25_part2.zip`

Extract BOTH into the same parent directory. They populate one folder named
`ConZFC_Pooled_Powers_Round21_2026-10-25`, with no overlapping file entries.
Neither ZIP alone is the complete executable proof/source collection.
`PARTS.json` lists the exact file partition; the combined manifest authenticates
all files. This ordinary split retains the full numerical and ordinary proof
dependencies without opaque compression or downloading anything during replay.

## Selected results

Each ordinary theorem, composed with its explicitly retained calibration,
establishes in ZFC that lack of a solution in the stated domain is equivalent
to Con(ZFC). The domains are part of the theorem and must not be interchanged.

| Direct quartic over unrestricted integers | Variables | Rows | Terms | Height |
|---|---:|---:|---:|---:|
| Principal | 217 | 154 | 7396 | 8880 |
| Lower height | 217 | 154 | 14793 | 3200 |
| Fewer variables | 216 | 153 | 25602 | 5632 |

The principal improves all varying metrics over the inspected 225-variable
pooled-power input. Its actual arithmetic ancestry is the Strict Horizons
source and retained factorial-free C222 calibration; the Pooled Powers packet
supplies the reusable pooling lemma, not a substitute calibration ancestor.
All 154 principal residuals are printed in the report. Actual complete
coefficient arrays are supplied for all three quartics.

| Ten STRICTLY POSITIVE integers | Exact degree | Binary operations |
|---|---:|---:|
| Free quotient and linear trace | 240 | 82 |
| Inverse correction and linear trace | 232 | 85 |
| Combined free quotient, trace and correction | 214 | 87 |

The 214/87 point lowers the incoming 232-degree result at unchanged operation
count. These are not unrestricted-ten-integer equations. They retain the
complete coherent four-port native coefficient tuple.

For eleven UNRESTRICTED integers, degree/operation pairs are 298/146 and
300/144, saving one operation each over the delivered Round20 controls.
These retain their separate six-port tuple. Their earlier restricted
fixed-frame degree bounds remain unchanged; no new universal lower bound
is inferred from the evaluator simplifications.

| Quartics with coefficients only plus or minus one | Variables | Terms |
|---|---:|---:|
| minimum503 | 503 | 24183 |
| compact505 | 505 | 20405 |
| compact512 | 512 | 18184 |
| balanced557 | 557 | 11991 |
| sparse617 | 617 | 8314 |
| sparser713 | 713 | 7172 |

All six have exact degree four, coefficient height one and constant one.
Their variable counts are unchanged from Round20; every support improves.
The new operations use anchored-unit equality cycles and shared multiplicative
coefficient factors, with exact source pullbacks and full coefficient checks.
The attempted pooled-source height-one transfers were not improvements and
are not presented as selected endpoints.

## New mechanisms

A pair of quadratic equations certifies every requested power at the same
nonzero base simultaneously. Signed Pell congruences and the original square
frame force each bounded error to vanish, including the appropriate unit-base
cases. The exact signed bootstrap excludes zero bases before applying it.

A cofinal odd beta multiplier removes a redundant witness. Common quadratic
Hessian-kernel directions and unit-slope rows then allow polynomial integer
restorations without increasing residual degree. Every source edit, shear,
projection and collected coefficient is independently checked.

The positive-variable branch combines a free quotient scale, an unsquared
strong Pell trace and inverse Lucas correction. Full denominator cancellation
waits until the exponential projection establishes its required prime support.
All negative intermediate cases and positive witness choices are proved.

## Reproduce the complete release

After extracting BOTH parts, change to the common release root. Python 3.10
or later with its standard library suffices:

    python3 -B verify_release.py

The verifier authenticates the exact combined inventory, copies the tree to
a disposable directory and runs all 15 steps in `VERIFY_PLAN.json`. Deep
optimized steps set PYTHONOPTIMIZE=1 so nested processes inherit optimization.
The checks reconstruct sources, maps and literal polynomials, verify both
coherent numeral tuples and all live DAG gates, check exact degrees, reject
corruptions, reproduce historical controls and independently parse the printed
principal equation. The original sealed extraction is left unchanged.

Save a new receipt OUTSIDE the sealed folder:

    python3 -B verify_release.py --output ../new_verification.json

Check inventory alone:

    python3 -B verify_release.py --integrity-only

The complete rebuild and mutation audits can take several minutes. To rebuild
the PDF in a working copy with an ordinary TeX Live installation:

    sh report/build_report.sh

Use a fresh extraction for strict manifest verification after generating TeX
auxiliary files or changing the PDF. TeX metadata can differ without changing
the mathematical pages.

## Scope and attribution

The comparison is pinned to ProveIt commit
`231a9cc9351bec9b70e334826058ed5d449c9460`. Seven new input packets were
inspected, with immutable Git or owned Library identities and full source
inventories. `provenance/`, `CLOSURE_MAP.md`, the component ledgers and retained
licenses document this boundary.

These are ordinary proofs of the stated ZFC equivalences. Finite checks do
not prove unbounded lemmas or consistency, and no new end-to-end Lean/Rocq
certificate, global minimum or literature-wide priority claim is made.
No remote repository was changed in preparing this contribution.

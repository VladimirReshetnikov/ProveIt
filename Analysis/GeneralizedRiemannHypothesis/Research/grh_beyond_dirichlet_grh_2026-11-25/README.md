# Beyond Dirichlet GRH

Research report prepared for Vladimir Reshetnikov, 25 November 2026 (Pacific date).

Start with **report.pdf**. The complete editable manuscript is **report.tex** plus the three files in **sections/**.

## Principal results

1. **Sharp bounded torsion nonvanishing.** Integral formal power series with interior reference points of valuation at least r and aggregate reference-value valuation at most B have a common nonvanishing torsion specialization of depth H = h_*(r) + floor(B). The bound is independent of the number of variables and polynomial degree, and sharp for one exponent with the stated radial restriction. A first-m-powers version has H = h_*(r/m) + floor(mB).
2. **The same upstream bound for analytic valuation control.** The polynomial selection theorem extends to integral formal series over completed C_p with its original torsion-order bound. This controls selected determinantal/Fitting valuations and inverse denominators.
3. **An exact odd-cocycle comparison.** For odd ell and e > 0, the direct limit of the source's shaOdd modules is the natural complex-conjugation eigenspace (-1)^(e+1) of the standard all-places locally trivial H^1 group with coefficients (F/O)(-e). The source's uniform finite-level length bound therefore transfers to that standard group.

These results have complete mathematical proofs in the report. The new results are **not Lean-compiled**. No named major open conjecture, including nonabelian GRH, Vandiver, or BSD, is asserted to have been resolved. The report identifies the remaining arithmetic work and distinguishes character order from conductor norm.

## Contents

- `report.tex`, `report.pdf`, `sections/`: manuscript and proofs.
- `artifacts/source_audit.py`, `source_audit.json`: static source and import-closure checks against the exact upstream revision.
- `artifacts/exact_checks.py`, `exact_checks.json`: exact cyclotomic examples, eighteen finite sharpness checks, a three-power matrix-rank example, and interpretation counterexamples.
- `artifacts/provenance.json`: repository revisions and identity/hash checks for all five earlier report archives.
- `artifacts/validation.json`: final PDF, computation, source-integrity, and proof-review status.
- `review/`: comparative prior-report audit and independent mathematical proof reviews.
- `formalization/new_results.md`: detailed implementation plan and outstanding formal proof obligations.
- `upstream/project/`: 216 unchanged upstream Lean source modules, comprising the complete local import closure of three selected reusable interfaces; original dependency pins; added existing-theorem audit entry point; build instructions. This extraction was **not built here**. Mathlib dependencies are pinned, not bundled.
- `SHA256SUMS`: archive-member integrity hashes.

## Reproduce

Compile the manuscript, with either Tectonic or a working TeX Live installation:

```sh
./build.sh
```

Run the exact examples (Python 3 and SymPy):

```sh
python3 artifacts/exact_checks.py artifacts/exact_checks.json
```

Audit the original repository (git and Python 3):

```sh
git clone https://github.com/lsernau/grh-lean.git /path/to/grh-lean
git -C /path/to/grh-lean checkout 72fead102f663d5c7a407964a13dc0cf9d977207
python3 artifacts/source_audit.py /path/to/grh-lean artifacts/source_audit.json
```

See `upstream/project/README.md` for commands to build and audit the existing extracted Lean theorems. Those commands do not formalize the new theorems in this report.

## Provenance and related work

Upstream: `lsernau/grh-lean` at `72fead102f663d5c7a407964a13dc0cf9d977207`.
Prior reports: `VladimirReshetnikov/ProveIt` at `a92443f00663b1b8b3c233d17df0ad49dc4f2b2c`, `docs/incoming`.

The torsion and comparison directions are not developed in those five reports. This is not a claim of literature priority. The manuscript discusses related work of Serban, Kriz–Nordentoft, and Kurihara and records what is newly proved here versus already present upstream.

Upstream source is Apache-2.0, with its LICENSE, NOTICE, and ATTRIBUTION retained. Newly added report and analysis artifacts are separate from the upstream proof; no upstream file is represented as modified or newly authored here.

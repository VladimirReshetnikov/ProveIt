# Transition tables and their status

All state counts below exclude a separate halt state. Benchmark conventions
use a binary alphabet, a single two-way infinite tape and an all-zero start.

| File | Working states | Format and status |
|---|---:|---|
| `zfc_254.tm` | 254 | Exact attributed upstream normalized benchmark; 508 rows |
| `zfc_253.tm` | 253 | Exact upstream PR 20 head table; 506 rows; externally proved endpoints |
| `existing_raw_CG_252_uncalibrated.tm` | 252 | Exact normalized ProveIt experimental CP/GIC table; 504 rows; calibration unproved |
| `raw_point_PSC_276_control.tm` | 276 | Newly measured named partial compiler control; no consistency-machine theorem |
| `raw_subset_PSC_280_control.tm` | 280 | Newly measured named partial compiler control; no consistency-machine theorem |

The named PSC controls have the backend's one undefined `1.inc/read1`
terminal transition. Filling this edge with a tape-preserving move to a fresh
halt label totalizes the table without adding a working state, under the
specified undefined-step halting convention. No compiler simulation or
blank-start consistency equivalence for either control is asserted.

The current 252-state CP/GIC candidate is **not** the different 252-state
prepared runtime core discussed in incoming reports. No uncalibrated prepared
tape is presented here as a blank initializer.

The exact table hashes and the full 253 bootstrap audit appear in
`../results/benchmark_audit.json`, `../results/psc_measurements.json` and the
package integrity manifest. See `../ATTRIBUTION.md` and the report for source
pins and authorship.

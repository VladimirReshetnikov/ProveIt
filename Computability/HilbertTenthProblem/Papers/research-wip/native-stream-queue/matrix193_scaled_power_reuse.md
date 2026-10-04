# Reuse a paid scaled power in the matrix coefficient component

The complete matrix sources cost **1,509 / 1,506 / 1,506 / 1,503 operations**. One multiplication disappears from each [terminal-carry/power parent](matrix193_terminal_power_composition.md), while the entire polynomial, supplied coordinates, positive zero tuples and exact degree remain unchanged. The coefficient component shrinks from 553 to **552 = 304M + 248A** rows. The separate universal bound remains 84 operations.

The [fresh helper](matrix193_scaled_power_reuse.py) emits all four complete arrays and exact certificates in the [receipt](matrix193_scaled_power_reuse.json). Frozen helpers are authenticated as inert bytes only. No predecessor program is executed or imported.

## Paid identity and deletion

The baseline source has the following actual computed values:

    cp317 = Q^150,
    cp344 = Q^162,
    cp345 = -20 * cp344,
    cp400 = -2 * cp333 = -20 * Q^12.

The coefficient circuit already pays for cp400 for a different consumer. Replace only the cp345 definition by

    cp345 = cp317 * cp400.

The identity Q^150 * (-20 Q^12) = -20 Q^162 holds over every commutative ring, including at Q = 0. The now-unused cp344 producer is deleted. Thus two old multiplications become one, using a negative multiple of a power already paid elsewhere. No free scalar multiplication, variable power or division is assumed.

The later producer cp400 and its dependencies are moved before their new use. A dependency traversal checks acyclicity, and the emitted source is independently audited for sequential operand availability. The other retained row definitions remain literal, and all non-pure-Q rows retain their relative order. The three controller variants use the frozen entry-controller register maps for this same edit. Backward liveness deletes exactly one producer in each complete array; every remaining producer and supplied port is live.

## Complete polynomial and boundary checks

The helper freshly expands each immediate parent's actual pure-Q subcircuits. It checks the old target and both new operands exactly, re-expands the rescheduled source and compares every retained pure-Q polynomial. A formal congruence interpreter then binds the proved target polynomial to the complete input-bearing Q expression and compares every retained register, including the final output. This proves

    F_new = F_immediate_parent

on identical supplied coordinates over every commutative ring.

All sixteen full coefficient polynomials are expanded and checked against their 2,704 coefficient entries. The complete 552-row coefficient components are present in the saved arrays; cp345 is the sole changed definition, and cp344 is the sole removed one. All 63 native rows and 97 group/population rows remain literal.

Both finalizers are traced backward from their actual outputs. Each trace checks the final subtraction, native product, one-plus-SOS, every retained residual square exactly once, all SOS additions and the private consumer boundary. The complete traced rows are unchanged. Their counts remain 50 / 47 / 47 / 44, with 16 / 15 / 15 / 14 residuals. No assumption about a contiguous source suffix is used.

## Full ledgers and scope

| Controller chart | M | A | Operations | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| None | 731 | 778 | 1,509 | 141 | 35,587 |
| Flow | 730 | 776 | 1,506 | 140 | 53,345 |
| Population | 730 | 776 | 1,506 | 140 | 53,347 |
| Both | 729 | 774 | 1,503 | 139 | 71,105 |

The four arrays contain 6,024 paid binary rows. The ordinary input, positive witnesses, eight fixed coefficient ports, illustrative fixed bindings, output and 137 distinct integer literals are unchanged. Fresh syntactic degree upper bounds are recorded separately from the inherited exact degrees.

Identical full polynomials on identical variables transfer the immediate parent's exact-degree theorem and full positive integer zero sets on every valid fixed-program slice. The predecessor terminal-carry and IDLE transformations still have only their established ordinary-input equivalence; this edit does not supply a stronger inverse across them. No arbitrary fixed-numeral assignment is certified as a universal program.

This is one concrete arithmetic identity, not an exhaustive coefficient-circuit optimum. A preliminary finite fingerprint search suggested it, but the saved evidence uses exact polynomial coefficients and full source reconstruction; the search's negative results are not claimed as a theorem. No new accepting trajectory or giant native Pell tuple is materialized.

## Evidence and replay

The helper pins the entire immediate parent trio and the entry-controller map receipt. Its receipt binds to its own source bytes. Fresh evidence covers all four complete arrays, four whole-output identities, all retained pure-Q values, sixteen coefficient words, eight actual finalizer traces, interfaces, topology, liveness and counts. There is no numerical trajectory argument or modular substitute for the exact identity.

```sh
scaled_wip=/absolute/path/to/native-stream-queue
python3 "$scaled_wip/matrix193_scaled_power_reuse.py" \
  --root "$scaled_wip" --expect "$scaled_wip/matrix193_scaled_power_reuse.json"
python3 -O "$scaled_wip/matrix193_scaled_power_reuse.py" \
  --root "$scaled_wip" --expect "$scaled_wip/matrix193_scaled_power_reuse.json"
```

Generation uses mutually exclusive `--output`. Duplicate and nonfinite JSON is rejected, receipt comparison is recursively type-exact, and explicit guards remain active under optimized Python. Fresh normal and optimized replays from `/` pass. Frozen predecessor files are unchanged.

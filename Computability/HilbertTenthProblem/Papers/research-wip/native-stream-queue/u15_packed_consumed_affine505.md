# One controller addition removed from every complete U15 source

The complete ordinary-input U15 polynomial now costs **505 = 209M + 296A**.
Its four inherited operation/degree representatives are **505/4881,
507/3120, 509/2116 and 511/1936**, all with the same 87 positive witnesses.
The two raw-input schedules also lose one addition. The complete polynomials,
comparison operands, supplied coordinates and computational relation are unchanged.
This improves the U15 route, not the separate 87-operation universal polynomial.

## Optimize the forms the complete circuit consumes

The pinned [506 parent](u15_packed_loader_offset506.py) exposes nine affine
ports from a 91-operation controller closure. Seven are consumed by the rest
of the circuit; two additional named forms describe the same intermediate
write projections and are retained. The old closure costs 6M+85A. The new
literal closure costs **6M+84A**.

Let `h_i=edge_i` denote the 29 existing positive shifted transition selectors.
Write a transition row as `(source, read, target, direction, write)`, and use
state center 7. The seven consumed forms are

| Source port | Exact affine form |
|---|---|
| `binary75` | `sum h_i − 29` |
| `binary76` | `sum read_i*h_i − 14` |
| `binary77` | `sum direction_i*h_i − 15` |
| `v131` | `2 sum direction_i*write_i*h_i − 18` |
| `v140` | `2 sum (1−direction_i)*write_i*h_i − 16` |
| `v156` | `sum (source_i−7)*h_i + 1` |
| `binary89` | `sum (target_i−7)*h_i + 17` |

The two retained intermediate ports are
`binary79=sum direction_i*write_i*h_i−9` and
`cross_write_only=sum (1−direction_i)*write_i*h_i−8`.
Doubling those ports computes `v131` and `v140`; no division is emitted.

Earlier controller schedules optimized a different collection of projections,
including the write sum and separate centered state. The new schedule shares
additions and subtractions among the actual consumed affine forms. In particular,
it includes the already-paid state offset in the target `v156`; no subsequently
restored intermediate is treated as free. All 90 rows are published literally
in the [compiler](u15_packed_consumed_affine505.py) and its full receipt.

A bounded greedy common-subexpression search tried 500 deterministic seeds for
each of binary coefficient expansion, signed-digit expansion and direct
coefficients. Their best closure costs were 90, 98 and 99. The selected binary
schedule came from seed 72; its two doubled-write offsets were reassociated at
unchanged cost to retain the historical intermediate ports. These are search
observations, not a proof that 90 is minimal. Receipt replay verifies the literal
selected schedule independently of the search and does not rerun all 1,500 trials.
The optional [search helper](u15_consumed_affine_search.py) authenticates the
same parent receipt, checks each emitted candidate's full affine coefficient
vectors, and reproduces the bounded search with `--start 0 --stop 500`.
Its outputs are controller candidates; they are not complete Diophantine sources.
A further 3,000 binary seeds (500 through 3499) found nine more 90-gate
schedules and none below 90; the [separate search receipt](u15_consumed_affine_extended_search.json)
records that finite distribution. This observation does not strengthen the
claim to an optimality theorem.

To reproduce the initial search or its extension from the WIP directory:

```sh
python3 u15_consumed_affine_search.py --output /tmp/u15-initial-search.json
python3 u15_consumed_affine_search.py --modes binary --start 500 --stop 3500 \
  --output /tmp/u15-extended-search.json
```

The search helper's output includes its best literal rows; compare the operation
count distribution with the recorded receipts. It independently verifies each
candidate's seven exact coefficient vectors before recording it.

## Complete polynomial proof

The wrapper authenticates the live parent and all eight canonical packet hashes.
It reconstructs the ancestral closure of the nine ports and requires its literal
91 rows to match the recorded source. No private removed register may escape into
another source row or comparison. Replacement names must be disjoint from all
supplied inputs and every retained source register.

For each port it expands both actual closures as exact sparse polynomials in the
29 independent selectors and compares all coefficients, including the constant.
After these nine identities are established, it compares the complete expression
DAGs beyond the cuts: every comparison operand, each active semantic register,
each loader/tag field, each native unit factor and the final polynomial output.
The finalizer rows remain literal. Every paid new gate is live in the final output.

Thus equality holds on all integer and rational assignments in the **same
coordinates**, without assuming that any other equation has vanished. The
parent's positive/natural domain, ordinary input loader, fixed valid program
slices, unbounded duration and first-halt semantics transfer unchanged. There
is no witness elimination or new domain argument.

The complete polynomial identities also transfer the parent's exact degrees,
including their validity uniformly over admissible fixed program slices. A
separately computed syntactic degree upper bound is kept distinct from those
exact-degree certificates. This is not a new leading-coefficient calculation.

## Fully paid ledger

Every emitted binary addition, subtraction and multiplication costs one;
nontrivial fixed-coefficient multiplications are paid. The counts include the
loader, packed history, native kernels and complete finalizer.

| Complete form | Parent | New M | New A | New total | Witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|---:|
| Raw ungrouped |321|116|204|320|51|11|1936|
| Raw grouped |319|116|202|318|51|10|3464|
| Ordinary ungrouped |518|209|308|517|87|31|1936|
| Ordinary grouped |506|209|296|505|87|25|4881|
| Frontier 0 |506|209|296|505|87|25|4881|
| Frontier 1 |508|209|298|507|87|26|3120|
| Frontier 2 |510|209|300|509|87|27|2116|
| Frontier 3 |512|209|302|511|87|28|1936|

Only these eight complete forms are emitted and audited. Ordinary grouped and
frontier 0 retain their distinct packet provenance even though their operation
counts agree. The earlier partition enumeration is not rerun and no global
circuit optimality is asserted.

## Replay and public boundary

Parent SHA256:
`b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a`.
The exact authenticated source bytes are compiled, canonical packet descriptors
use type-sensitive hashes, and warm calls recheck the full historical lineage.
Supplied packets must match the canonical packet recursively with exact types.
Source/parent accessors return defensive copies. Old rewrite descriptions are
archived explicitly as provenance rather than asserted to describe the new rows.
The module rejects optimized Python because historical parents use assertions.

The [saved receipt](u15_packed_consumed_affine505.json) records every full source
and all nine coefficient identities for each form. Verification includes 128
complete integer identities (64 signed), 2,928 comparison residual identities,
16 rational evaluations, 488 malformed-call rejections, two raw zero-tape checks
and 24 defensive-copy checks. Numeric checks supplement the algebraic proofs.

From the WIP directory, with SymPy installed through the research environment:

```sh
/tmp/diophantine-research-venv/bin/python u15_packed_consumed_affine505.py
```

A scratch copy accepts `--root /absolute/path/to/native-stream-queue`.
Default execution regenerates and compares the whole receipt with exact types;
only `--write` updates it. The [independent review](review_u15_consumed_affine505.md)
checks the literal transition table, complete emitted sources and API boundaries
separately.

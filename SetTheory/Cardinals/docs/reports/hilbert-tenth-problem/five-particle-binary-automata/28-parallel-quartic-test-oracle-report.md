# Certificate test oracle and recommended binding tests

The generated `fixtures.json` contains eight schema-valid small sources, 411
targeted snapshots, four exhaustive fixed-mass domains (122 snapshots), and 32
finite-horizon endpoint cases. Every ordinary snapshot was checked against both
the pinned sparse and eager **new parallel** evaluators for raw maps, eligibility,
each block output, block involution, both whole-step directions, and inversion.
No frozen packet was edited. Python used `-B` and disabled bytecode writes. The
one old ordered execution is explicitly labeled as a semantic separator.

`prepare_test_oracle.py` regenerates the fixture and prints the validation receipt.
`test-oracle-receipt.json` records its SHA-256 and the nonzero event counts.

## Small, nonvacuous exhaustive domains

Compile one circuit per source/mass, and reuse it on every listed support. The
fixture stores every exact expected answer, rather than only an aggregate hash.

| Source | Mass | Universe | Supports | E selected events | P selected events |
|---|---:|---|---:|---:|---:|
| `empty` | 3 | 0,6,7,8,11 | 10 | 0 | 2 |
| `direct` | 3 | 0,10,11,12,13,14 | 20 | 2 | 4 |
| `increment_right` | 2 | 0 through 8 | 36 | 10 | 10 |
| `increment_right` | 3 | -18,-13,-10,0,18,19,23,24 | 56 | 23 | 23 |

Here `empty` means an empty branch list, **not** an identity whole rule. Its
home-phase P template remains and flips the two indicated supports. This is a
useful p=0/a=0 edge case. The other sources include both counter directions,
both nonzero updates, a guarded direct branch, and an increment whose domain and
image guards differ. Empty and singleton supports are included for all sources.

## Highest-priority regressions

1. `malformed_cascade`: increment-right source and
   X={-118,-112,0,18,23}. New E, new P, forward, and inverse all fix X.
   The old ordered full step yields {-119,-113,0,19,24}.
   - E raw map is {(0,-119):1}. Its hypothetical swap produces
     {-119,-114,0,18,23}, retains (0,-119) at orientation 0, and births (1,0).
   - P raw map is {(47,-118):1}. Its hypothetical swap produces
     {-118,-113,0,18,23}, retains (47,-118) at orientation 0, and births (59,0).
   - Each raw map has exactly one isolated key; eligibility is empty because
     prospectivity fails. Merely comparing to initially discovered IDs is wrong.
2. `reverse_free_*`: both O and I modes, left/right and increment/decrement.
   Each uses reverse orientation and anchor -103. The fixture records h and w;
   the required anchor is h-w, not the current lower pair particle h.
3. `reverse_endpoint_*`: reverse endpoint interactions at anchor 79. The marker
   is z=79+v*delta, so the key anchor is z-v*delta. All four sign combinations are
   present; using the marker itself breaks half or all of these cases.
4. `fixed_guard_*`: an increment-right source guarded by c1=0 has image c1=1.
   Dispatch accepts class 0 and rejects class 1 in **both** orientations;
   commit does the opposite in **both** orientations. Table choice is template
   fixed, not determined by the current orientation.
5. `guard_bands_*`: 162 cases enumerate each exact class 0..3, the absent/high
   class, multiple detectors in a band, and immediately outside offsets -1/4
   on each side, for both orientations. Outside particles do not turn into a
   detector. Two in-band particles invalidate the raw guard.
6. `exactness_*`: adding one particle at either closed exactness endpoint kills
   the focused raw key; moving it one site outside restores that raw key. The
   tested free pair radius is 28 and the direct triple radius is 64. Selection
   can still depend on prospectivity; use the explicit `own_raw_expected` flag.
7. `isolation_*`: two plus pairs have two raw keys in the focused block. At H-1
   and H, neither is eligible; at H+1, both are selected simultaneously. E uses
   H=834 and P uses H=298 for this source.
8. `all_types_*`: both orientations of every one of the 95 arithmetic type IDs
   of the minimal moving source, including every travel endpoint. Test-time
   enumeration is an oracle convenience; it is not permitted as compiler
   construction when claiming source-sized syntax.

## Certificate-specific checks to add

- Use all `horizon_cases`: T=0,1,2,3 in both directions, with the exact target
  accepted and the same-mass sorted `rejected_target` rejected. Forward uses
  E then P; inverse uses P then E at each full step.
- Check input sorting/domain constraints directly. Do not turn duplicate or
  unsorted coordinate lists into sets before testing rejection: doing so hides
  the intended malformed certificate input.
- For every accepted assignment, evaluate every quadratic residual and the
  quartic sum of squares. Then mutate each witness coordinate upward by one;
  mutate every positive coordinate downward by one. Every mutation must make
  the score positive. Include inactive slots, rejected prospective lanes, and
  lane padding, not only output wires.
- Mutating one coordinate is useful binding coverage, not a uniqueness proof.
  The proof must still use total topologically deterministic gates and canonical
  signed pairs. For bounded tiny arithmetic primitives, exhaustive natural-fiber
  checks can provide an additional independent sanity check.
- If the implementation exposes raw descriptors, compare their complete
  `(global_ID, anchor, orientation)` rows to the fixture before comparing only
  block outputs. Key-set comparisons themselves omit orientation.
- Verify large positive and negative translation covariance with the same
  circuit: it tests signed canonicalization and comparator slacks without
  altering circuit size. Translating every support and expected anchor by the
  same integer must preserve raw IDs and orientations.
- A corpus of endpoint and finite-domain tests cannot establish arbitrary-input
  raw completeness or degree/resource claims. Keep those claims tied to the
  construction and audit proof; report actual measured gate/residual counts.

## File semantics

Raw and eligible rows are `[global_type_ID, invariant_anchor, orientation]`.
`blocks.E` and `blocks.P` each refer to the original input independently.
`forward_output` is P(E(X)); `inverse_output` is E(P(X)). Guard/noise cases may
have unrelated raw events, so their focused-key flags should be checked in
addition to the full expected maps. All source data is ordinary JSON accepted
through the frozen `SparseParallelCompiler` and `ParallelCompiler` constructors.

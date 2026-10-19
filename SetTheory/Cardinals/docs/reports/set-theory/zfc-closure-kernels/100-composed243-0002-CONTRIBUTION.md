# Proposed ProveIt contribution: composed243

## Why this change

The maintained compensated244 machine has 244 working states. The independently
delivered loop-rotation244 machine releases a different state from the common
Routing245 ancestor. Their literal edits can be combined, but compatibility of
their correctness proofs requires rechecking all entry contexts and local paths.

## What this contribution supplies

An exact **243-working-state** table with all blank initialization included,
canonical labels 0–242, initial state 0, separate halt 243, binary alphabet,
and mandatory left/right moves. Relative to inherited Routing245 labels it
deletes 26 and 122 and changes seven retained rows.

The independent local proof compares rotated244 directly with composed243 on
every binary tape/head from old start 95. It checks an inductive local bit
condition, 480 ordinary rows, and seven positive finite blocks with equal whole
tape endpoints. A separate full fresh runtime replay checks the actual243 table
against the universally equivalent rotated source and the exact blank initializer.

The ordinary resulting theorem is:

```text
ZFC ⊢ (¬Halt(composed243, blank) ↔ Con(ZFC)).
```

## Validation

- Exact total table, renumbering and all 243 states graph-reachable.
- All 8,385 surrounding source control edges and both unbounded loop cases.
- Exact 407,967-transition blank startup with sparse/dense full-tape agreement.
- All 8,389 nonhalting frame successors and all 8,390 affine/runtime guards.
- Expanded runtime: 2,314,868 symbolic rules; minimum positive lower bound 13.
- One retained unused completion row `(27,1)`; it is kept and its state is counted.
- Offline driver and preserved ancestor inputs provided.

## Suggested integration

Preserve this entire package as an incoming research archive. A maintained
`Computability/BusyBeaver/Research/ZFC/candidate-composed243` directory can promote
`machine/machine.tm`, `machine/machine_old.tm`, `machine/renumbering.json`,
`machine/construction.json`, the local checker, and its proof/evidence references.
The full source/runtime evidence remains recoverable from this package.

The closed existing Routing245 external Lean endpoint is a predecessor result.
A complete new 243-state proof-assistant endpoint and object-language PA calibration
are separate remaining work; this contribution does not label them complete.

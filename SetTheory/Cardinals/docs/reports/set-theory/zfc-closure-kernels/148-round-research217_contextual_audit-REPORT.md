# Independent audit of the contextual 218-state substrate

This audit concerns the contextual alternative under
`research217_review/contextual/selected/machine`, not the other published
218-state machine and not a 217-state candidate. Received programs were not
executed. The finite machine and source files were treated as inert data.

**Result: PASS as an alternative 218-state blank-start consistency-search
substrate, at the ordinary mathematical proof boundary described below. The
current 217-state target is not met.**

## Exact bytes and labels

| File | SHA-256 |
|---|---|
| `k218.native.tm` | `3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1` |
| `k218.normalized.tm` | `4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651` |
| `k218.tm` | `7ca993f2c7f2cbdbca5b69756712d0fac17ff81e81e260190a599115c0643acb` |
| `sites218.json` | `1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe` |

The native table has exactly 218 working states, 436 rows, start 0, dispatcher
84, and separate halt 254. Every working state is graph-reachable. A fresh
zero-edge-first breadth-first labeling reproduces the complete canonical table
with working states 0 through 217, dispatcher 23, and halt 218. Replacing native
301 by normalized 102 and native 302 by normalized 120, including all targets,
reproduces the normalized table exactly. These are labelings of one machine.

Against the accepted native K219 table, the literal change census is: states
96 and 190 removed, state 79 added, and 57 retained rows changed. The fresh
runtime map extends the pinned historical map injectively with fresh labels
for the new native states; the complete map is saved, rather than silently
identifying the normalized labels with historical labels of different states.

## Complete blank initialization

The owned sparse-native and separately implemented dense-canonical
interpreters both execute exactly 312,701 transitions from a fully blank,
two-way infinite tape. They agree on the complete final tape support and every
transition-use count after transport by the freshly derived bijection. No
earlier halt occurs. The first complete root frame is:

- Native state 84, canonical state 23, head -5, header 139, extra gap 80.
- Logical registers `[3,0,0,0,3,0,0,0,0]` under permutation
  `(6,2,0,4,3,7,8,5,1)`.
- Nine primary registers and 130 spare registers, each spare equal to 1.
- Exactly 277 specified one cells, and every other tape cell zero.

The earlier complete dispatcher frame at step 92,828 is **not root** and is
not used as the initialization endpoint. Both interpreters independently
identify the same 268 complete frames among 1,258 dispatcher visits, with only
the final frame a root frame. Visited head positions range from -15 to 553.
`BOOT_RESULT.json` records the full endpoint, row counts, and literal delta;
`CLEAN_BOOT_FRAMES.json` records all complete frames.

## Universal initialized runtime

The driver freshly applies the previously owned symbolic kernel to these
exact native table bytes and all source occurrences. The only induction rules
are literal transitions, natural-length unary self-loop scans, and finite-list
traversal using four freshly derived one-block lemmas on the exact table.
All assertions remain enabled. No producer runtime certificates are used as
proof rules, and no source guards exclude any generic case.

The theorem quantifies over nine independent arbitrary natural primary
register values, arbitrary natural extra gap and first spare value, and an
arbitrary finite remaining spare tail. A decrement has separate zero and
positive branches. Each nonhalting primitive ends at its exact successor
program-counter frame, including head position, register updates, spare-list
append behavior, and whole-tape exterior. Halting and every nonhalting
primitive have positive finite affine duration. This does not mean arbitrary
dirty formula/cache contents are sound consistency-search seeds: that is a
separate source invariant.

The full fresh result is recorded in `RUNTIME_RESULT.json` and `CASES.json`.
`COMPOSED_RESULT.json` binds the runtime, blank initialization, and independent
source correspondence to the exact hashes above.

The fresh run proves all **6,167 generic cases**, with **1,514,325 symbolic rule
applications**, **436 of 436 literal rows** covered, and minimum affine-duration
constant **13**. The source has 4,744 leaves, 205 distinct DAG nodes, maximum
address depth 38, and maximum zero run 6. The ordered regenerated case receipt
has SHA-256
`977a141212bceaa379aa90797777a1764acc01b8d8d860aa175f9d89fee53ff6`, exactly
matching the received case pin. This equality was checked only after the full
fresh proof finished. The independent composition check also rechecks complete
zero/positive case coverage and every duration's integer nonnegativity and
strictly positive constant.

Owned execution dependencies are the existing symbolic kernel
`k223_merged_runtime_audit/runtime/symbolic_runtime.py` (SHA-256
`7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f`) and its
owned helper `independent_runtime.py` (SHA-256
`0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346`). Full input,
driver, and dependency hashes are recorded in the JSON receipts and
`SHA256SUMS`.

## Proof boundary and target

Source correspondence is a separately checked prerequisite, not a consequence
of the state count or a finite blank simulation. With exact source-word and
guarded-control-flow identity to the already accepted source, the fresh
runtime and complete clean blank initialization transport the accepted K219
finite-refutation calibration to this contextual table. The resulting
ordinary mathematical theorem is that ZFC proves blank halting of this table
if and only if ZFC has a finite refutation, equivalently blank nonhalting if
and only if Con(ZFC).

The source link is independently recorded in
`research217_encoding/CONTEXTUAL_ALTERNATE_COMPARISON.json`: all 4,744 ordered
primitive operations and arguments agree with the already audited published
218 source, and both binary-address and continuation-stack resolvers agree
on all 6,166 nonhalting guarded successor edges. Both exact source and table
hashes are pinned. The previous independent published-source audit connects
that same source to accepted K219. This supplies step-for-step ordinal/store
transport for arbitrary registers, rather than an inference from a similar
source tree or a finite test run.

This is not a proof of Con(ZFC), unconditional nonhalting, minimality, or a
new Lean/Rocq/internal-PA endpoint for the exact bytes. No ancestor rebuild was
performed. This audit validates a **218-state search platform only**. The
current user target of 217 states remains unachieved by this artifact.

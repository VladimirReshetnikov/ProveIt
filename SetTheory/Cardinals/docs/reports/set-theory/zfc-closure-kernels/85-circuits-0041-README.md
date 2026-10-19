# Removing two transfer loops proved empty by the product invariant

The three delivered register programs have independently checked halting
equivalence to the pinned source for roots with logical `T=W=H=0`, with the
other six registers arbitrary. They **do not yield a smaller binary Turing
machine** through the current fingerprint emitter.

| Transformation | Deleted original leaf indices | Remaining source leaves | Emitted graph states | Exact state-bisimulation quotient |
| --- | --- | ---: | ---: | ---: |
| X loop | 6316, 6317, 6318 | 6,457 | 253 | 253 |
| T loop | 6434, 6435, 6436 | 6,457 | 247 | 247 |
| Both | all six above | 6,454 | 254 | 254 |

The prototype `.tm` files contain exactly the stated graph-reachable working
states, with old labels, start state 95, and separate halt 254. They are emitter
outputs for examining code sharing. **Their binary instruction contracts and
blank initializers have not been certified.** The established result here is a
source-language optimization, together with a measured state-cost obstruction
for this particular emitter and these finite layout families.

## Why the source rewrite is sound

At original leaf 6316, address `111010010110001100`, the product invariant
proves logical register X is zero. The decrement therefore preserves all
registers and goes directly to leaf 6319. Its positive-branch increment and
continue, leaves 6317 and 6318, have empty invariant masks. Replace the single
occurrence of the enclosing subtree at prefix `1110100101100011` by its right
child, `CI5`. Other occurrences of shared decoder subtrees are preserved.

At original leaf 6434, address `111111000`, logical T is zero. The analogous
transfer loop's increment and continue, leaves 6435 and 6436, are unreachable.
Replace the subtree at prefix `1111110` by its right child. This preserves the
subsequent transfer code; it removes only the proved empty loop.

The transformation pairs surviving leaves in order. An old edge entering an
erased decrement is normalized through that one register-preserving step.
All feasible edges from all surviving source leaves, including external
breaks and continues entering either region, must then commute with the new
source graph. Existing break/continue instructions are retargeted when needed.
The independent checker also proves that normalization cannot cycle, that
retained register effects and halt tags match, and that the initial leaf is
preserved. These obligations give a halting equivalence on the invariant
through finite stuttering. Each erased nonempty-mask segment has length one.

The product invariant and the two forced-zero tests are prior research
information. This contribution applies them as occurrence-specific source
specializations and measures their interaction with the 246-state runtime's
decoder sharing. Deleting a source region can introduce distinct ancestor
subtrees and increase the emitted table size; that is what happens here.

## Completed layout searches

After each collapse, every one-step closed move produced by the accompanying
`rotate_search.options` function was checked against the invariant-conditioned
source graph. There are 238 proposals for X, 240 for T, and 240 for both:
718 proposals in total. Exact state bisimulation was then computed for every
emitted table, including those above the earlier heuristic's 249-state cutoff.
The respective minima remain 253, 247, and 254.

The closest case, T-only, was also screened under **all 333 one-step global
left/right binary reassociations** of its compact DAG, allowing existing
break/continue encodings to repair the control flow. Of these, 257 passed the
invariant-conditioned source-edge check and 76 failed it. The minimum exact
state-bisimulation quotient remained 247. These are exhaustive results for
the stated finite proposal generators, not a bound on alternative compilers,
longer sequences of layout changes, or arbitrary binary machines.

The archived source and result files are in
`../../../verification/fusion/zero_specialization/`. `exact-cost-summary.json`
is the authoritative exact partition-refinement record for the closed moves;
`summary.json` retains the initial source-checked cost scan, whose large-table
cost gate was subsequently strengthened. `control-scan-summary.json` records
the complete 333-proposal control-aware scan. `portable-regeneration.json`
binds the three programs and trimmed prototype tables to their hashes.

## Reproduction

Run from the archive root, using Python 3 without `-O`. To regenerate the three
programs and their emitter tables quickly:

```sh
python3 code/fusion/zero_specialization/specialize.py --base-only --output /tmp/zfc-zero-collapse
```

To repeat all 718 closed proposals and exact state partitions, omit
`--base-only`. To repeat the additional T-only control-aware scan:

```sh
python3 code/fusion/zero_specialization/control_scan.py --output /tmp/zfc-zero-control
```

The independent source theorem checks are separate from the generator:

```sh
python3 code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseX.sites.json --deleted 6316 6317 6318 --output /tmp/collapseX-independent.json
python3 code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseT.sites.json --deleted 6434 6435 6436 --output /tmp/collapseT-independent.json
python3 code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseXT.sites.json --output /tmp/collapseXT-independent.json
```

The supplied independent results are
`../../../verification/proof/collapseX-independent.json`,
`../../../verification/proof/collapseT-independent.json`, and
`../../../verification/proof/collapseXT-independent.json`.
The three source JSONs preserve the exact bytes used in those audits.

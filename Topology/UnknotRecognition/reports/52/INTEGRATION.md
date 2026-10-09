# Integration without silently changing the recognizer contract

## Proposed additive destination

`Topology/UnknotRecognition/research/sparse_incidence_20261008/`

No files in the remote repository were written. This delivery does not reserve a
numbered synthesis-report slot or assume that the default branch remains at the
inspected commit.

## Pinned sources

Repository: `VladimirReshetnikov/ProveIt`  
Inspected ref: `7518823550fbc8c217bc8be0113fe52002e77465`

The executable kernels are unchanged upstream files. Their Git blob hashes are:

```
interval_orbits.py        e86050aadbcef6f17fdddff9cbd1abc0e7ca18e8
interval_orbit_verify.py  0ccb56a0e8b5f1255384121d7417441314727720
```

`integration/probe_checkout.py --kernel-dir PATH` compares a local directory
containing those two modules against the identities. The included probe was run
against the delivered `vendor` directory, not against an independently cloned
full checkout. A future version mismatch requires review, not automatic acceptance.

## Suggested production changes after review

Introduce a separately named sparse observer; do not silently replace the dense
histogram shape expected by existing callers. Convert maintained IntervalPairing
objects to the public inclusive rows `[p.a,p.b,p.c,p.d,-1 if p.reverse else 1]`.
Port intervals remain half-open. The mathematical masks use bit zero for the
first supplied port, with a positive mask-zero row for unmarked components.

Preserve the existing local orbit producer and verifier. The research oracle
explicitly uses the classical periodic rule to keep the asymptotic argument
on the classical AHT scheduler. Evaluating the sharper default is a separate,
controlled experiment, not a prerequisite for the sparse method.

Use a distinct sparse certificate schema. Do not translate it through a dense
`2^r` proof-index array. Carry a complete input binding, baseline proof, sparse
entries, and exactly the required coned-union proofs. Recompute actual unions
and coning rows in the verifier; never use equality of count values as a cache key.

Maintain one allowance for baseline, discovery, extra proof queries, and (where
applicable) both cover computations. Resource interruption must not produce a
negative knot certificate. AHT cycle limits are not wall-time or bit-operation
limits; retain cooperative cancellation and outer serialized-size caps.

## Required review before promotion

Run the full maintained suite on the intended checkout; this was not done here.
Run native normal-arc and orientation-character fixtures, including independent
geometric provenance checks. Compare dense and sparse results on identical native
inputs before enabling any caller. Keep component-observer timing separate from
whole-recognition timing, and report proof/replay overhead explicitly.

The current histogram cannot replace a boundary state for arbitrary continuations.
The paper's four-point example has identical incidence but different connectivity
after the same pointwise attachments. A production hierarchy must retain the
attachment maps, ordering, labels, slopes, and provenance needed by its actual
operations, or prove a suitable restricted congruence theorem.

## Intentional limitations

The package does not construct a triangulation, a normal surface, a cut-open
manifold, a hierarchy candidate, or an unknot verdict. It supplies an exact,
polynomial compressed incidence query. Whole-hierarchy node counts, encoding
sizes, candidate production, and terminal recognition remain separate obligations.

# Proposed fixed-tuple native endpoint for the 85 graph

This is a **source-only composition**, not an elaborated Lean proof, verified
existence of an iPRA proof, or an equivalence established for the displayed
PDF. The final declaration has no explicit graph-cut premise in its written
statement, but every new and imported proof, model interpretation, cast,
tactic, provider and axiom in the transitive chain remains to be checked.
Its `#print axioms` line has not been executed.

`Fixed85Endpoint.lean.src` applies the previously drafted fixed-K native
client to three source-level arguments:

* the positive 81↔83 `CrossRootCut` from the proposed two first-root
  constructions;
* the 83→84 gamma cut from the proposed same-witness positive-83 calibration;
* the 84→83 q-divisibility cut from the proposed direct 84 first/main,
  strong/auxiliary, exact-index and power chain.

The parent 84 polynomial bridge comes from the previously drafted
84→87→88 fixed symbolic tuple chain. The two 84 graph structures are
separately generated from the same 84-row JSON and the intermediate source
proposes their output equality by `rfl`. The checker compares every witness,
port and graph row in both sources; it does not validate `rfl` in Lean. The
fixed parameter is `paramKernel rho`, with the tuple specified by the
imported compact symbolic source. This does not authenticate the coefficient
bytes, polynomial expansion, domain translation, variable names, or semantics
of any existing equation or PDF.

## Lexical import audit

`manifest.json` records the dependency-first lexical import order and SHA-256
of each reachable repository-local source selected by `scan.py`. At this
snapshot the scan covers 1,354 local modules and has 94 unresolved/external
frontier module names. It found no cycle among the resolved local lexical
imports. For a bare module name it rejects differing candidate source bytes;
identical-byte copies are counted, with a preferred non-overlay path recorded.
The check fails if the recorded local inventory changes.

This is a bounded **source** audit. It does not resolve the external frontier,
check package-specific source roots or build order, prove that Lean's parser
interprets every lexically detected import the same way, check compiled object
search paths or collisions, authenticate transitive providers, detect proof
escapes, execute Lean, or inspect axioms. A cycle or incompatibility could
still exist in the unresolved frontier or selected build environment. The
import graph has no observed local cycle, but that is not evidence that the
formal proof compiles or that an iPRA derivation exists.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-fixed85-native-composition-draft/check.py
```

The deterministic checker rescans the local import graph, verifies the pinned
manifest and source-level theorem wiring, and checks both 84 row transcripts.
It performs no Lean build, staging, or external synchronization.

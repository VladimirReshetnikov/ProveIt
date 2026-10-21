# Composed normalized and balanced source certificate

The new files are `BalancedNormalized.v` and `Source215BalancedNormalized.v`.
They refine the existing normalized checker through exact tree flattening,
then reuse its semantic soundness theorem. The checked conclusion is

```
forall R, rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R)
```

There is no restriction on the initial register file. This is the source
layer, not a newly rebuilt binary-machine/ZFC endpoint.

## Replay

With Coq 8.18.0 and `coqchk` on PATH, use a fresh output directory:

```sh
python3 reproduce.py --out /tmp/k215-balanced-normalized-fresh --recursive --baseline
python3 lookup_metrics.py --check
```

The recorded complete run is `verification/result.json`; all 15 Coq modules
were freshly compiled and the concrete result passed recursive `coqchk`.
The new theorem reports are closed under the global context. Logs are in
`verification/logs/`. Compiler locations in the receipt are historical;
the replay driver finds the installed compiler on PATH.

Inherited sources use the Rocq 9.1 style. Coq 8.18 replay adds the documented
`Compat818` import to `RMEquiv.rocq91.v` in the fresh build tree only. The
receipt distinguishes delivered and compiled hashes. The wrapper's 9.1
branch retains the original source; this packet's fresh run used 8.18.
The minimal numerical source definitions match the pinned repository
exactly; `source_bindings.json` records both Git object and SHA256 hashes.

## Origin and trust boundary

`NormalizedBisim.v`, `NormalizedCert215.v`, `PathCodec.v`, `BisimMirror.v`,
minimal dependencies, and the compatibility shim come from the incoming
`K215_Checked_Simplifications_2026-10-21` packet. `BalancedBisim.v` comes
from `K215_Certificate_Refinements_2026-10-21`. The top-level provenance
folder records both archive hashes and notices. All inherited licenses
are included in `licenses/`.

The tree-building computation is untrusted: exact flattening, validity,
size 1,426, height 12 and the passing check are separately proved in Coq.
The new refinement lemma proves equality with the normalized list
checker; it does not reprove semantics or weaken a hypothesis.

## Counts and timing

`lookup_metrics.py` parses the delivered 1,426-entry certificate and both
source programs, independently confirms the sole halt entry 19 and that
other entries address matching register tests, and counts the 2,851
lookups. It reproduces 2,033,059 visited list cells versus 32,961 tree nodes
(maximum depth 12). This is a data audit, not a replacement proof kernel.

The count ratio is about 61.7. It is not a measured wall-clock speedup:
concrete balanced proof compilation took 15.741 s in this run; the normalized
list baseline took 9.238 s. The balanced module also constructs and verifies
the tree. Recursive coqchk took 313.451 s, and the complete run 374.868 s.
Keep this as an optional representation refinement until production
benchmarking justifies adoption.

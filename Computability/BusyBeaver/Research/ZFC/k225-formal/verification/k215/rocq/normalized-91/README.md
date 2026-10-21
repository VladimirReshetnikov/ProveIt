# Rocq K215 with the normalized source certificate and the decode-based enumerator

**Status: `PASS_CLOSED_COMPILE`** (2026-10-21), all 44 modules of the K215 closure compiled from
scratch with Rocq 9.1.0 / rocq-stdlib 9.0.0 against the K230 reference rebuilt from its pinned
sources, by the maintained driver:

```sh
python3 rocq/rocq-extension/build.py --states 215 --compile-only \
  --reference /path/to/k230-rocq --jeff-reference /path/to/busy-beaver --coqc /path/to/coqc
```

[verification.json](verification.json) is that run's own record: the per-module source and object
hashes, timings and outputs, the toolchain, and `closed_reports: 2` for the endpoint
`CorrectDense215` (the sparse `Correct215` likewise prints two closed reports, and no `Axioms:`
report appears). [compilation.txt](compilation.txt) is its compilation log. Every compiled source
is byte-identical to the committed `coq/215/` tree. The run took 499 s; the closure before these
changes took 607 s on the same machine.

What the closure now contains, against the recursively checked 237-module baseline of
[`../README.md`](../README.md):

* **Source layer.** `Source215.p215_dagPerm` (unchanged statement) is proved by one check of the
  normalized certificate (`inputs/215/NormalizedCert215.v`, 1,426 entries compared modulo the
  implicit false suffix of pointers) and the mirror lemma, instead of two checks of the 2,240-entry
  offset certificate. `OffsetBisim230.v` and `Cert215Offsets.v` leave the closure; the source layer
  drops from 1,507,824 to 122,314 bytes. Adopted from the batch-208/209 proposals.
* **Enumerator layer.** `rocqperm/` mirrors the Lean `EnumPerm`: one step decodes the next command
  and runs `xstep`; soundness is `xstep_inv`/`xstep_none`; one `halts_from_iff` covers every start
  state between candidates, and `seedPerm_iff_thm` is a corollary.

Recursive `coqchk` was **not** rerun for this closure; the baseline's recursive check covers the
previous sources only.

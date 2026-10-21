# Rocq K215 with the normalized source certificate and the decode-based enumerator

**Status: `PASS_CLOSED_KERNEL`** (2026-10-21). All 44 modules of the K215 closure were compiled
from scratch with Rocq 9.1.0 / rocq-stdlib 9.0.0 against the K230 reference rebuilt from its
pinned sources, and `coqchk` then rechecked `K215F.CorrectDense215` recursively, by the
maintained driver:

```sh
python3 rocq/rocq-extension/build.py --states 215 \
  --reference /path/to/k230-rocq --jeff-reference /path/to/busy-beaver --coqc /path/to/coqc
```

[verification.json](verification.json) is that run's own record: per-module source and object
hashes, timings and outputs, the toolchain, `closed_reports: 2` for the endpoint `CorrectDense215`
(the sparse `Correct215` likewise prints two closed reports; no `Axioms:` report appears), and the
`coqchk` result (exit code 0, 1,121 s). [compilation.txt](compilation.txt) is the compilation log
and [coqchk.txt](coqchk.txt) the recursive checker's context summary. Its global context lists
`BusyCoq.LibTactics.inj_pair2`, `Stdlib.Logic.ProofIrrelevance.proof_irrelevance` and
`Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`, exactly as for the baseline; the endpoint statements
depend on none of them (their closed reports), and no constant relies on type-in-type, unsafe
fixpoints or assumed positivity. Every compiled source is byte-identical to the committed
`coq/215/` tree of `b8802a9772` (the origin merge `f46b58faf8` brought back the older offset-
certificate sources, retained there as the last checked boundary; they were re-landed byte for byte
once this kernel record existed). Compilation took 504 s (the closure before these changes: 607 s on the same
machine).

What the closure now contains, against the 237-module baseline of [`../README.md`](../README.md):

* **Source layer.** `Source215.p215_dagPerm` (unchanged statement) is proved by one check of the
  normalized certificate (`inputs/215/NormalizedCert215.v`, 1,426 entries compared modulo the
  implicit false suffix of pointers) and the mirror lemma, instead of two checks of the 2,240-entry
  offset certificate. `OffsetBisim230.v` and `Cert215Offsets.v` leave the closure; the source layer
  drops from 1,507,824 to 122,314 bytes. Adopted from the batch-208/209 proposals.
* **Enumerator layer.** `rocqperm/` mirrors the Lean `EnumPerm`: one step decodes the next command
  and runs `xstep`; soundness is `xstep_inv`/`xstep_none`, with formula codes kept opaque
  (`L1_SoundPerm` 24.5 s -> 1.5 s); one `halts_from_iff` covers every start state between
  candidates, and `seedPerm_iff_thm` is a corollary.

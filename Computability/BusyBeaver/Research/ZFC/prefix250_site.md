# Exact prefix250 per-site soundness

`SitePrefix250.lean` connects successful individual instruction checks to positive runs of the exact 250 table. Its source is adapted from the maintained SitePerm252 framework, preserving the original physical register permutation, path semantics, minimum distance 40 and computational fuel 4000.

The target gap includes two independent changes: an overflowing PC moves its marker left one cell, and positive decrement moves the register origin right one cell. Thus positive decrement adds one cell beyond the overflow contribution; every other branch adds zero. Increment's target box already appends a value-one spare, while both decrement branches retain the suffix. The checked symbolic predecessor supplies the ten-block validity condition and the actual old 112 zero-return continuation.

Each theorem is conditional on its Boolean site check succeeding. `runTo_sound` yields a positive runtime and whole-tape target representation for every natural gap and arbitrary valid file; `runHalt_sound` yields an actual positive-time halt. This unit does not yet show acceptance of all 8,391 original instruction cases or preservation of the recurrent nonempty-spare dispatch frame.

The root's sole attempt passed the 142-line source and 71-line audit with 12 named axiom probes, 13 typed callers and no warnings. All probes depend only on `propext` and `Quot.sound`. The executed source, audit, guard, result and raw output remain in the full single-attempt history. The fresh object was recorded before the audit and remained unchanged afterward.

Successful record SHA256: `ce8af0a401b5db1a39ab19933d9920c44778684a488432d49cab868bf2f5cc6a`.
Source SHA256: `5e3e06d6818f9e94459a9b94b9311424259b2b9b69654c9cd2fa5f49008d7723`.
Audit SHA256: `c80c97fc9e2c15b4b1054fc307af5cf21ef988629f424db0e689bbf374eda668`.
Fresh object SHA256: `d4d76241935c3160ec3ceb3e7771ae9db6ed72506ca4990f9af92ef25676423d`.

The guard pins the successful Symbolic record, verifies 17 exact project providers and all 51 current inputs, and checks the import closure and first-provider resolution. Init/Omega are the only toolchain boundaries; there is no external project-library boundary. Historical 252/253 providers supply generic list/frame infrastructure, not execution assumptions about the 250 machine.

Only this source and audit compile, serially with one thread, 4096 MiB and a shared 120-second budget under default elaboration limits. Maintained publication changes only source/audit default paths. A root can prepare those defaults without compiling or querying a compiler version:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix250_site.py \
  --repo "$PWD" \
  --symbolic-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-symbolic-verification.json \
  --output /tmp/prefix250-site-fresh-preparation --prepare-only
```

The pinned provider objects must be available; the command performs no dependency build. Final review is by the author and root, with no independent child evidence review claimed. All-program acceptance, frame transport, complete instruction composition, blank bootstrap, exact 250 consistency calibration and PA-internal equivalence remain separate work.

The original machine, verification framework and compiler retain Mira-Cult, Jeff Ketchersid and Andrew James Wade's attribution. The shared-carry construction is the ProveIt contribution preserved from incoming source 58 (`126d12e470`).

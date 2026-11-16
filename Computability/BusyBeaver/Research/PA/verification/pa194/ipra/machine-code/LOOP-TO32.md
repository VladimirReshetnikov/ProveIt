# Model-level matched loop and increment to site 32

`PA194MatchedLoopTo32.matched` composes the model-length site-27 loop, its zero exit to site 31, and the matched site-31 increment to site 32. In every PRA model, the source controller iterates the actual four-instruction loop `r 0` times, then takes two further controller steps, reaching site 32 with register 0 incremented from the loop's zero value. In parallel, there is a physical loop-and-exit time after which the explicit site-31 physical run reaches the corresponding site-32 frame. The input register vector, controller tail, gap, spare count and spare value are arbitrary model elements. The physical suffix is the same model-valued sequence of one-valued spares followed by blank tape used in the established physical-loop invariant.

The source and physical sides refer to the same explicit final source-register file. This theorem gives an existential physical time for the loop/exit part followed by explicit nested clocks for the site-31 segment. It is an all-model Lean theorem; it is not yet a native iPRA sentence, a proof of the complete machine's simulation, or a consistency implication.

`PA194Site31PhysicalClock.frameStep` names the first-phase site-31 physical clock and restates the separately checked source-frame step. `PA194PhysicalLoopTo32.reaches32` composes that physical step with the previously checked physical loop/exit theorem. `PA194SourceLoopTo32.reaches32` separately composes the source-controller loop iteration, zero exit and site-31 increment. The final theorem conjoins them.

To rebuild the machine-specific closure over the passed site-31 matched stage, from the repository root choose a new nonexistent output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-loop-to32.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-loop-to32-coherent
```

The builder finds the machine-source import closure of the final theorem, rebuilds missing modules in dependency order in one fresh output, rejects conflicting overlaps among the supplied machine roots, and does not put the fetch machine-object root on `LEAN_PATH`. It checks any used fetch-manifest source against that manifest and records all used source and baseline-object SHA-256 hashes before and after in `loop-to32-receipt.json`; it also records the fetch manifest and matched-stage receipt hashes. It rejects missing machine-specific sources, `sorryAx` in Lean output, and a missing final axiom audit.

The prior matched stage, two physical tail stages, physical machine baseline, fetch `foundation-view`, and general foundations remain prebuilt. The recorded hashes detect changes during this run; they do not independently authenticate all prebuilt transitive imports. The fetch root supplies its documented general graph foundation view and source manifest, not a competing machine `PA194SourceProgram` object.

The observed staged run was performed in two sequential phases: the physical-loop closure was rebuilt first with the same algorithm, then `append-matched-loop.py` rebuilt the source-side and conjunction modules into that same retained output. The second phase verifies and records the completed physical-loop receipt and its direct inputs in `matched-loop-extension-receipt.json`. The current `check-loop-to32.py` includes those two modules as final targets so a fresh replay performs both phases in one run.

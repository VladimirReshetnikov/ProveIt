# Two PA194 source-header root passes

`PA194TwoHeaderPasses.twoPasses` composes two all-model, model-time
literal-dense-machine runs. Its input is the state-24 root with left half 1
and the same arbitrary physical source file and zero header as
`PA194SeedHeaderPass.sourceHeaderPass`. The eleven source-file arguments and
header length may be arbitrary elements of any candidate PRA model. The
conclusion gives the exact state-24 root, left half 1, transformed right half
`v7+1`, and the exact sum of the two model-valued clocks; the definitions in
the theorem retain the complete tail.

The second pass runs through states 93, 17, and 22. Its exact scan uses
`PA194NinetyThreeReturnTwoWithTail.ninetyThreeReturnTwoWithTailExact`. The
synthetic file `Fin.cases (k+1) (physicalArgs args)` prepends one block to the
entire original physical file. `PA194SecondHeaderFile.sourceFirstPassShape`
proves this representation and proves that the first pass's output has the
required next-entry shape. Neither result assumes a blank file suffix. In
particular, it retains the startup file's 25 further one-valued spare blocks.
The separately named `secondHeaderPass` exposes the exact result for any
well-shaped file, and its `scanClock` and `backClock` preserve model lengths.
The [third-pass entry and scan](TWO-PASSES-SCAN.md) continue this trace to the
next controller scan while retaining the same source-file suffix.

`check-two-header-passes.sh` recompiles the six new modules in a fresh
temporary overlay, pins the directly imported project objects and reports the
axioms of the final results. It expects a previously checked first-pass and
arbitrary-tail-scan overlay as `PA194_PARENT_OVERLAY`, the physical project
object overlay as `PA194_PROJECT_OVERLAY`, parent-startup and dense-startup
overlays as `PA194_STARTUP_OVERLAY` and `PA194_DENSE_OVERLAY`, and the
Foundation overlay as `IPRA_FOUNDATION_OVERLAY`. `PA194_TWO_PASSES_SOURCE_DIR` can point at sources
outside the repository. **Pinning direct object hashes does not audit their
transitive imported object closure**; use an independently audited coherent
closure for these inputs. A successful suffix replay is not a clean rebuild of
the whole development.

This proves only two physical header passes. It does not identify the final
source-instruction endpoint, establish the all-model source-machine simulation,
or prove either direction of a consistency equivalence in iPRA.

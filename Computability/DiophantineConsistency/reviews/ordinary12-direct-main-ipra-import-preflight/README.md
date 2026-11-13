# Direct 90 model import preflight

The captured header traversal finds 765 selected-project ancestors of `DirectMainHalt`, 44 imports outside that selected graph, and no intersection with the 425-module candidate rebuild cone. Twenty-five headers were read in the retained batches; earlier inventory and scans supplied the rest. These are serialized-object findings, not a complete package, dynamic dependency, source-to-object, or final iPRA proof audit.

The live overlay comparison in `observations/overlay01/result.json` found 700 matching objects, 65 absent objects and no differing overlapping object hashes. The source provider, object SHA-256 and companion records for each selected module are captured in `observations/manifest01/result.json` (SHA-256 `ab58436c4bffc287dad9d77d357c4b2f7cd6fc512cf65ec5cbbf0b98402e8ae3`). This is an active-build snapshot: 24 of the 425 cone objects were absent at capture. An earlier double snapshot detected ongoing writes. Do not use this snapshot as a final provider.

The absent modules and where their first-resolved selected providers were found are:

## XQ91 halt library (40)

`CompactBytePortsModelIff`, `CompactFourPortByteAssembly2`, `CompactKernelByteRecipe`, `CompactLowByteAssembly`, `CompactLowByteBound`, `CompactLowByteBoundary01`, `CompactLowByteBoundary02`, `CompactLowByteBoundary03`, `CompactLowByteBoundary04`, `CompactLowByteBoundary05`, `CompactLowByteBoundary06`, `CompactLowByteBoundary07`, `CompactLowByteBoundary08`, `CompactLowByteBoundary09`, `CompactLowByteBoundary10`, `CompactLowByteBoundary11`, `CompactLowByteBoundary12`, `CompactLowByteDense`, `CompactLowByteDenseExtra`, `CompactLowByteGaps`, `CompactLowBytePrefix`, `CompactLowByteRecipeData`, `CompactLowByteTail`, `CompactLowByteWindow`, `CompactShiftedHighBound`, `CompactShiftedHighByteAssembly`, `CompactShiftedHighByteWindow`, `CompactShiftedHighDigits`, `FreeJRetainedDirectExpression`, `FreeJRetainedShiftModel`, `FreeJSumSquares`, `GenericFourBytePorts`, `QCube92`, `QCube92Halt`, `QCube92Model`, `QCube92NamespacedExistence`, `RadixShiftedDigits`, `RadixWindowReconstruction`, `RetainedBetaBytes`, `XQ91Model`

## Direct graph objects (23)

`DirectMainComparison`, `DirectMainEarly`, `DirectMainEquivalence`, `DirectMainFirst`, `DirectMainFirstQuotient`, `DirectMainForward`, `DirectMainGap`, `DirectMainGapBalance`, `DirectMainGraph`, `DirectMainGrowthAlgebra`, `DirectMainHalt`, `DirectMainIndices`, `DirectMainMain`, `DirectMainNorm`, `DirectMainOriented`, `DirectMainPell`, `DirectMainPellGrowth`, `DirectMainProjection`, `DirectMainRank`, `DirectMainRestricted`, `DirectMainTransport`, `DirectMainWindow`, `DirectPortBounds`

## XQ91 and halt roots (2)

`XQ91`, `XQ91Halt`

The first group was selected from `/tmp/xq91-halt-umk96cx0/lib`; the second from individually selected `/tmp/direct-main-projection-*` outputs; the last from `/tmp/free-j-qcube92-ye71qcst` and `/tmp/xq91-halt-umk96cx0`. These are temporary paths and are not a reproducibility guarantee. The manifest gives each exact path and all observed companions; any eventual provider must also respect the full selected import order and object coherence.

`python3 manifest.py check` compares the current direct and cone paths and companions with the active-build snapshot, rejecting drift, missing cone objects, or differing overlaps. After the worker confirms the rebuild has finished and writes have stopped, `python3 manifest.py final` can record a fresh guarded comparison in `observations/final01/`: it requires two identical snapshots, all 425 cone objects present, and no different overlapping direct object. It can still report absent direct objects: those need a coherent selected provider, and this check alone does not establish the final join. Check for subsequent provider changes immediately before use.

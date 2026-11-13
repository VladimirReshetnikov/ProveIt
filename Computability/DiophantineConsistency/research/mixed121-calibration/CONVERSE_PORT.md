# Converse port map: Compact44 halt-to-witness layer to 121x8801

Generated on 2026-11-06 from the import closure of
`Compact44.CompactHaltFirstGamma` minus that of `Mixed121.Mixed121Halt`.
That leaves 147 modules. Each has a class and a dependency level (level 0
imports no other module in the set), and the port runs bottom-up by level.

| Class | Meaning | Port action |
| --- | --- | --- |
| `T` | mentions 67x8807 constants (`8807`, `590069`, `581197`, `342946332593`, …) | hand port |
| `W` | mentions only the widths `67/66/65` | `tools/width_port.py`, or hand port where a constant is incidental |
| `g` | generic, but imports a `T`/`W` module | retarget the imports |
| `G` | generic all the way down | reuse unchanged |

The controller (`ArithmeticControllerDataCompact44`, `…ChoiceCompact44Triangle`)
is already the arbitrary-odd-factor construction of recipe §4. Its port
changes `p = 581197 → λ = 2341`, `p − 1 = 581196 → 2340`,
`d = 590069 → 1064921`, and the residue of `g = B^(p−1)` modulo `C0·p`.

## Progress

Ported and building, with axioms `propext`, `Classical.choice`, `Quot.sound`:

| Compact44 | 121x8801 |
| --- | --- |
| `ArithmeticControllerDataCompact44` | `Mixed121ControllerData` (transcribed) |
| `ArithmeticControllerChoiceCompact44Triangle` | `Mixed121ControllerChoice` (transcribed) |
| `ArithmeticConstructionUnitCompact44` | `Mixed121ConstructionUnit` (`Γ` order `5070`, not `p − 1`) |
| `SymbolicKernelResidue` | `Mixed121KernelResidue` (`K ≡ 510020909 mod C0`) |
| `KernelAliasExplicit`, `AliasResidueNumeral`, `AliasUnitGivenResidue`, `AliasUnitDischarged`, `AliasRankCalibration`, `ActualRankCalibration`, `ChosenControllerCalibration` | `Mixed121Calibration` (one module, same theorem names) |
| `CompactHighPhaseReduction` | `Mixed121HighPhase` (active phases `1065..1074`, tail `8792..8799`) |
| `CompactPulseBitSafety`, `CompactLowModFour` | `Mixed121PulseBit` |
| `CompactKernelFiniteCert` | `Mixed121KernelFiniteCert` |
| `CompactConstructedRank`, `CompactPackingOriginResidue` | `Mixed121ConstructedRank` |
| `ConcreteSparseKernel` … `KernelDigitsBounded`, `TopDigitClean` | `Mixed121SparseKernel` (`2^1070003 ≤ K < 2^1070004`) |
| `CompactKernelSplit`, `CompactLowerKernelMass`, `CompactKernelDivFour` | `Mixed121KernelSplit` |
| `CompactCellCopyCode` … `CompactCellProductBound` (13 modules) | `Mixed121Cell` (44 extra digits = `Mixed121Digits.digit`) |

Not needed: `CompactSymbolicMaskData` (only `low_eq`), and the byte-window modules
`SymbolicKernelBytes`, `ByteWindow`, `RadixBitWindow` (their only consumer is outside the closure).

| Level | Module | Class | Lines |
| ---: | --- | :---: | ---: |
| 0 | `ArithmeticAdaptiveConstructionCorrection2011` | G | 33 |
| 0 | `ArithmeticControllerLift` | G | 244 |
| 0 | `ArithmeticOuterSeed` | G | 195 |
| 0 | `ArithmeticPacking` | G | 282 |
| 0 | `ArithmeticPellOrdinateCompat` | G | 20 |
| 0 | `ArithmeticPellSquaredSeed` | G | 100 |
| 0 | `ArithmeticRankForcing` | G | 151 |
| 0 | `ArithmeticRunTrace` | G | 267 |
| 0 | `Compact44.CompactBooleanZeroCarry` | G | 49 |
| 0 | `Compact44.CompactControllerTriangle` | G | 43 |
| 0 | `Compact44.CompactFirstPositive` | G | 65 |
| 0 | `Compact44.CompactForwardCellInputs` | G | 111 |
| 0 | `Compact44.CompactGenericStride` | G | 78 |
| 0 | `Compact44.CompactHighOriginTransfer` | G | 33 |
| 0 | `Compact44.CompactHighPhaseReduction` | T | 90 |
| 0 | `Compact44.CompactKernelFiniteCert` | T | 73 |
| 0 | `Compact44.CompactLowModFour` | W | 36 |
| 0 | `Compact44.CompactPellOrdinateCompat` | G | 23 |
| 0 | `Compact44.CompactPulseBitSafety` | T | 80 |
| 0 | `Compact44.CompactSymbolicMaskData` | T | 39 |
| 0 | `Compact44.SparseRadix` | G | 97 |
| 0 | `Compact44.SymbolicKernelResidue` | T | 109 |
| 1 | `ArithmeticAdaptiveConstructionCorrectionPositive2011` | G | 79 |
| 1 | `ArithmeticPellAuxiliarySeed` | G | 216 |
| 1 | `ArithmeticTilingTable` | G | 258 |
| 1 | `Compact44.AbstractSparseFamily` | G | 26 |
| 1 | `Compact44.ArithmeticControllerDataCompact44` | T | 229 |
| 1 | `Compact44.CompactConstructedRank` | T | 102 |
| 1 | `Compact44.CompactHighOriginResidue` | G | 39 |
| 1 | `Compact44.CompactPackingOriginResidue` | T | 42 |
| 1 | `Compact44.CompactPartialPackingTransport` | G | 110 |
| 1 | `Compact44.CompactSeedOrdinate` | G | 61 |
| 1 | `Compact44.CompactStencilZeroCarry` | W | 67 |
| 1 | `Compact44.CompactWordCellClient` | G | 92 |
| 1 | `Compact44.GenericWindow` | G | 17 |
| 1 | `Compact44.KernelAliasExplicit` | g | 24 |
| 1 | `Compact44.PaddedRadixDigits` | G | 18 |
| 1 | `Compact44.SparseCountBound` | G | 23 |
| 2 | `ArithmeticAdaptiveConstructionCorrectionSeed2011` | G | 40 |
| 2 | `ArithmeticTilingRows` | G | 396 |
| 2 | `Compact44.AliasResidueNumeral` | T | 15 |
| 2 | `Compact44.ArithmeticConstructionUnitCompact44` | T | 182 |
| 2 | `Compact44.ArithmeticControllerChoiceCompact44Triangle` | T | 459 |
| 2 | `Compact44.CompactAuxPositiveCoordinates` | G | 46 |
| 2 | `Compact44.CompactCellCopyCode` | G | 96 |
| 2 | `Compact44.CompactConstructedCarryInput` | T | 99 |
| 2 | `Compact44.CompactFirstSeed` | G | 54 |
| 2 | `Compact44.CompactWordAnchorBits` | G | 74 |
| 2 | `Compact44.CompactWordColorBits` | G | 56 |
| 2 | `Compact44.CompactWordProductColumn` | T | 110 |
| 2 | `Compact44.CompactWordTargetNoCarry` | T | 156 |
| 2 | `Compact44.ConcreteSparseKernel` | T | 32 |
| 2 | `Compact44.RadixBitWindow` | W | 16 |
| 3 | `ArithmeticTilingBand` | G | 204 |
| 3 | `Compact44.AliasUnitGivenResidue` | T | 24 |
| 3 | `Compact44.ArithmeticConstructionVariationCompact44` | g | 169 |
| 3 | `Compact44.ByteWindow` | W | 29 |
| 3 | `Compact44.CompactCellDigit` | G | 58 |
| 3 | `Compact44.CompactTemporalConstructedCarry` | W | 40 |
| 3 | `Compact44.ConcreteSparsePositions` | g | 52 |
| 4 | `ArithmeticTilingWord` | G | 358 |
| 4 | `Compact44.AliasUnitDischarged` | T | 23 |
| 4 | `Compact44.CompactCellDigitDef` | G | 35 |
| 4 | `Compact44.CompactCellSupport` | T | 55 |
| 4 | `Compact44.CompactRankVariationRetry` | T | 58 |
| 4 | `Compact44.ConcreteSparseDigits` | g | 29 |
| 4 | `Compact44.KernelTermBounds` | g | 46 |
| 5 | `Compact44.AliasRankCalibration` | T | 35 |
| 5 | `Compact44.CompactCellDigitSupported` | T | 43 |
| 5 | `Compact44.CompactCellDigitUniform` | G | 35 |
| 5 | `Compact44.CompactHaltWord` | G | 24 |
| 5 | `Compact44.CompactPackedCell` | T | 69 |
| 5 | `Compact44.CompactRankResidueJoin` | T | 32 |
| 5 | `Compact44.KernelCoefficientBound` | W | 17 |
| 6 | `Compact44.ActualRankCalibration` | T | 39 |
| 6 | `Compact44.CompactBaseLowNoCarry` | T | 78 |
| 6 | `Compact44.CompactCellSizeBound` | T | 61 |
| 6 | `Compact44.CompactFirstTransportSeed` | T | 61 |
| 6 | `Compact44.CompactHaltDimensions` | T | 61 |
| 6 | `Compact44.CompactOriginPredecessor` | W | 61 |
| 6 | `Compact44.CompactOuterPellSeed` | T | 52 |
| 6 | `Compact44.CompactPositiveGammaSeed` | T | 33 |
| 6 | `Compact44.CompactPositiveTransport` | T | 72 |
| 6 | `Compact44.KernelDigitsBounded` | W | 34 |
| 6 | `Compact44.SymbolicKernelBytes` | W | 30 |
| 6 | `Compact44.UniformBlocks` | G | 30 |
| 7 | `Compact44.ChosenControllerCalibration` | T | 56 |
| 7 | `Compact44.CompactCalibratedTransport` | T | 30 |
| 7 | `Compact44.CompactCellSharpSize` | W | 47 |
| 7 | `Compact44.CompactOriginLowNoCarry` | W | 60 |
| 7 | `Compact44.CompactUniformPackedCell` | T | 50 |
| 7 | `Compact44.TopDigitClean` | g | 89 |
| 8 | `Compact44.CompactCanonicalPerturbation` | T | 61 |
| 8 | `Compact44.CompactCellProductBound` | T | 62 |
| 8 | `Compact44.CompactCellPulseEquality` | W | 92 |
| 8 | `Compact44.CompactConstructedWord` | T | 79 |
| 8 | `Compact44.CompactKernelSplit` | W | 44 |
| 8 | `Compact44.CompactPackingGeometry` | T | 26 |
| 8 | `Compact44.CompactPackingMaskAlgebra` | g | 25 |
| 8 | `Compact44.CompactPulsePackedCell` | T | 50 |
| 9 | `Compact44.CompactKernelLowProduct` | T | 72 |
| 9 | `Compact44.CompactLowerKernelMass` | g | 64 |
| 9 | `Compact44.CompactPulsePreservationRetry` | W | 47 |
| 9 | `Compact44.CompactSymbolicMaskFields` | T | 23 |
| 9 | `Compact44.CompactWordCleanSupport` | T | 40 |
| 9 | `Compact44.CompactWordFieldDigits` | T | 73 |
| 9 | `Compact44.CompactWordLowFields` | W | 63 |
| 9 | `Compact44.CompactWordProperties` | T | 41 |
| 9 | `Compact44.CompactWordPulseEquality` | T | 35 |
| 10 | `Compact44.CompactAlignedTemporalBoolean` | T | 36 |
| 10 | `Compact44.CompactHaltPackedWord` | T | 57 |
| 10 | `Compact44.CompactKernelBlockSize` | T | 85 |
| 10 | `Compact44.CompactPulseChosenRankRetry` | T | 54 |
| 10 | `Compact44.CompactWordFieldCyclic` | T | 67 |
| 10 | `Compact44.CompactWordLowSlot` | T | 57 |
| 10 | `Compact44.CompactWordPackingFields` | g | 46 |
| 11 | `Compact44.CompactAlignedStencilZeroCarry` | T | 74 |
| 11 | `Compact44.CompactHighPaddingSize` | T | 91 |
| 11 | `Compact44.CompactKernelDivFour` | W | 64 |
| 11 | `Compact44.CompactMarkedCellSum` | T | 41 |
| 11 | `Compact44.CompactWordBlockPositivity` | W | 48 |
| 11 | `Compact44.CompactWordChosenRank` | T | 72 |
| 12 | `Compact44.CompactMarkedHighPadding` | T | 58 |
| 12 | `Compact44.CompactMarkedPhysicalColumn` | T | 94 |
| 12 | `Compact44.CompactOriginBlockResidue` | T | 68 |
| 12 | `Compact44.CompactWordPhaseZeroHigh` | T | 111 |
| 12 | `Compact44.CompactWordRankFourFields` | T | 74 |
| 13 | `Compact44.CompactHighOriginMarked` | T | 69 |
| 13 | `Compact44.CompactMarkedTargetColumn` | T | 82 |
| 13 | `Compact44.CompactWordHorizontalParity` | T | 73 |
| 13 | `Compact44.CompactWordMarkerParity` | T | 121 |
| 13 | `Compact44.CompactWordPhysicalFieldParity` | T | 66 |
| 13 | `Compact44.CompactWordRankStaticFields` | T | 49 |
| 14 | `Compact44.CompactHaltRankStaticFields` | T | 49 |
| 14 | `Compact44.CompactMarkedTargetHighNoCarry` | T | 35 |
| 14 | `Compact44.CompactWordAnchorParity` | T | 94 |
| 14 | `Compact44.CompactWordFieldHigh` | T | 72 |
| 15 | `Compact44.CompactHaltRankThreeFields` | T | 65 |
| 15 | `Compact44.CompactWordAnchorHigh` | T | 38 |
| 16 | `Compact44.CompactHaltRankHighFields` | T | 65 |
| 16 | `Compact44.CompactMarkedAllHigh` | T | 59 |
| 17 | `Compact44.CompactHaltRankNoHigh` | T | 70 |
| 18 | `Compact44.CompactHaltPellSeed` | T | 80 |
| 19 | `Compact44.CompactHaltPellTransport` | T | 54 |
| 20 | `Compact44.CompactHaltFirstSeed` | T | 89 |
| 21 | `Compact44.CompactHaltFirstPositive` | T | 87 |
| 22 | `Compact44.CompactHaltFirstGamma` | T | 65 |

import GowersSzemeredi.Proofs01Headline
import GowersSzemeredi.Proofs01_03
import GowersSzemeredi.Proofs02DensityIncrement
import GowersSzemeredi.Proofs02Partition
import GowersSzemeredi.Proofs02PhasePartition
import GowersSzemeredi.Proofs02Roth
import GowersSzemeredi.Proofs02Uniformity
import GowersSzemeredi.Proofs03Basic
import GowersSzemeredi.Proofs03CubeUpper
import GowersSzemeredi.Proofs03Cubes
import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs03GowersCS
import GowersSzemeredi.Proofs03Interval
import GowersSzemeredi.Proofs03Minkowski
import GowersSzemeredi.Proofs03ProgressionAverage
import GowersSzemeredi.Proofs03ProgressionCount
import GowersSzemeredi.Proofs03ProgressionExistence
import GowersSzemeredi.Proofs05FourierInterval
import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05MissingInterval
import GowersSzemeredi.Proofs05MultilinearIteration
import GowersSzemeredi.Proofs05MultilinearPartition
import GowersSzemeredi.Proofs05PolynomialPartition
import GowersSzemeredi.Proofs05Progressions
import GowersSzemeredi.Proofs05ThresholdFreeLocalization
import GowersSzemeredi.Proofs05Weyl
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Proofs07AffineRestriction
import GowersSzemeredi.Proofs07BalogSzemeredi
import GowersSzemeredi.Proofs07BohrHom
import GowersSzemeredi.Proofs07DRC
import GowersSzemeredi.Proofs07FreimanClosure
import GowersSzemeredi.Proofs07FreimanRestriction
import GowersSzemeredi.Proofs07ProgressionLinearity
import GowersSzemeredi.Proofs07SimultaneousLinearity
import GowersSzemeredi.Proofs08FourTermColoring
import GowersSzemeredi.Proofs08FourTermTheorem
import GowersSzemeredi.Proofs08QuadraticBias
import GowersSzemeredi.Proofs09Moments
import GowersSzemeredi.Proofs09Restriction
import GowersSzemeredi.Proofs10Bohr
import GowersSzemeredi.Proofs10Counting
import GowersSzemeredi.Proofs10Error
import GowersSzemeredi.Proofs10Extraction
import GowersSzemeredi.Proofs10Induced
import GowersSzemeredi.Proofs10Main
import GowersSzemeredi.Proofs10ProgressionLinearity
import GowersSzemeredi.Proofs10Regular
import GowersSzemeredi.Proofs10Selection
import GowersSzemeredi.Proofs10Shift
import GowersSzemeredi.Proofs12
import GowersSzemeredi.Proofs12Amplification
import GowersSzemeredi.Proofs12Combination
import GowersSzemeredi.Proofs12HigherArrangements
import GowersSzemeredi.Proofs12Parallelograms
import GowersSzemeredi.Proofs12Restriction
import GowersSzemeredi.Proofs13AllScalesStepSpan
import GowersSzemeredi.Proofs13Basic
import GowersSzemeredi.Proofs13CoefficientExtraction
import GowersSzemeredi.Proofs13ConstructedChain
import GowersSzemeredi.Proofs13ContextExtraction
import GowersSzemeredi.Proofs13EndpointPrintedTheorem
import GowersSzemeredi.Proofs13FiniteRecurrence
import GowersSzemeredi.Proofs13FiniteRowExtraction
import GowersSzemeredi.Proofs13InitialProgression
import GowersSzemeredi.Proofs13LargeSpectrumCover
import GowersSzemeredi.Proofs14Arrangements
import GowersSzemeredi.Proofs14Configurations
import GowersSzemeredi.Proofs14Fourier
import GowersSzemeredi.Proofs14HigherArrangements
import GowersSzemeredi.Proofs14Product
import GowersSzemeredi.Proofs14ProductToArrangements
import GowersSzemeredi.Proofs15DegenerateArrangements
import GowersSzemeredi.Proofs15LevelSets
import GowersSzemeredi.Proofs15ProductToRestriction
import GowersSzemeredi.Proofs15Restriction
import GowersSzemeredi.Proofs15Walsh
import GowersSzemeredi.Proofs15Walsh2
import GowersSzemeredi.Proofs16AllDimensionsExplicit
import GowersSzemeredi.Proofs16BaseCaseEndpoint
import GowersSzemeredi.Proofs16CommonBase
import GowersSzemeredi.Proofs16Lemma1
import GowersSzemeredi.Proofs16Lemma10
import GowersSzemeredi.Proofs16Lemma5
import GowersSzemeredi.Proofs16Lemma6
import GowersSzemeredi.Proofs16Lemma9
import GowersSzemeredi.Proofs16StructuredExtraction
import GowersSzemeredi.Proofs16Union
import GowersSzemeredi.Proofs17FinitePatterns
import GowersSzemeredi.Proofs17LocalizedPhaseRemoval
import GowersSzemeredi.Proofs17Phase
import GowersSzemeredi.Proofs17PhaseRemoval
import GowersSzemeredi.Proofs17Regions
import GowersSzemeredi.Proofs18CoverExplicit
import Lean.Util.CollectAxioms
import GowersSzemeredi.Proofs16Lemma1Side
import GowersSzemeredi.Proofs05_10Side
import GowersSzemeredi.Proofs05PolynomialPartitionSide
import GowersSzemeredi.Proofs17PhaseRemovalSide

/-! Production audit of every numbered statement in the source catalogue.
Each selected declaration must be a theorem of precisely the corresponding
Prop-valued definition. Its transitive axiom set may contain only the three
standard approved axioms. This checks the existing catalogue, whose repairs
and differences from the printed source are documented separately. -/
set_option autoImplicit false

open Lean Elab Command

private def numberedCompanions : Array (Name × Name) := #[
  (``LeanProofs.GowersSzemeredi.theorem_1_1, ``LeanProofs.GowersSzemeredi.theorem_1_1_holds),
  (``LeanProofs.GowersSzemeredi.theorem_1_2, ``LeanProofs.GowersSzemeredi.theorem_1_2_explicit),
  (``LeanProofs.GowersSzemeredi.theorem_1_3, ``LeanProofs.GowersSzemeredi.theorem_1_3_explicit),
  (``LeanProofs.GowersSzemeredi.lemma_2_1, ``LeanProofs.GowersSzemeredi.lemma_2_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_2_2, ``LeanProofs.GowersSzemeredi.lemma_2_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_2_3, ``LeanProofs.GowersSzemeredi.lemma_2_3_holds),
  (``LeanProofs.GowersSzemeredi.corollary_2_4, ``LeanProofs.GowersSzemeredi.corollary_2_4_holds),
  (``LeanProofs.GowersSzemeredi.corollary_2_5, ``LeanProofs.GowersSzemeredi.corollary_2_5_holds),
  (``LeanProofs.GowersSzemeredi.theorem_2_6, ``LeanProofs.GowersSzemeredi.theorem_2_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_1, ``LeanProofs.GowersSzemeredi.lemma_3_1_holds),
  (``LeanProofs.GowersSzemeredi.theorem_3_2, ``LeanProofs.GowersSzemeredi.theorem_3_2_holds),
  (``LeanProofs.GowersSzemeredi.corollary_3_3, ``LeanProofs.GowersSzemeredi.corollary_3_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_4, ``LeanProofs.GowersSzemeredi.lemma_3_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_5, ``LeanProofs.GowersSzemeredi.lemma_3_5_holds),
  (``LeanProofs.GowersSzemeredi.corollary_3_6, ``LeanProofs.GowersSzemeredi.corollary_3_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_7, ``LeanProofs.GowersSzemeredi.lemma_3_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_8, ``LeanProofs.GowersSzemeredi.lemma_3_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_9, ``LeanProofs.GowersSzemeredi.lemma_3_9_holds),
  (``LeanProofs.GowersSzemeredi.lemma_3_10, ``LeanProofs.GowersSzemeredi.lemma_3_10_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_1, ``LeanProofs.GowersSzemeredi.lemma_5_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_2, ``LeanProofs.GowersSzemeredi.lemma_5_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_3, ``LeanProofs.GowersSzemeredi.lemma_5_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_4, ``LeanProofs.GowersSzemeredi.lemma_5_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_5, ``LeanProofs.GowersSzemeredi.lemma_5_5_holds),
  (``LeanProofs.GowersSzemeredi.corollary_5_6, ``LeanProofs.GowersSzemeredi.corollary_5_6_holds),
  (``LeanProofs.GowersSzemeredi.corollary_5_7, ``LeanProofs.GowersSzemeredi.corollary_5_7_holds),
  (``LeanProofs.GowersSzemeredi.corollary_5_8, ``LeanProofs.GowersSzemeredi.corollary_5_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_9, ``LeanProofs.GowersSzemeredi.lemma_5_9_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_10, ``LeanProofs.GowersSzemeredi.lemma_5_10_holds),
  (``LeanProofs.GowersSzemeredi.corollary_5_11, ``LeanProofs.GowersSzemeredi.corollary_5_11_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_12, ``LeanProofs.GowersSzemeredi.lemma_5_12_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_13, ``LeanProofs.GowersSzemeredi.lemma_5_13_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_14, ``LeanProofs.GowersSzemeredi.lemma_5_14_holds),
  (``LeanProofs.GowersSzemeredi.lemma_5_15, ``LeanProofs.GowersSzemeredi.lemma_5_15_holds),
  (``LeanProofs.GowersSzemeredi.proposition_6_1, ``LeanProofs.GowersSzemeredi.proposition_6_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_6_2, ``LeanProofs.GowersSzemeredi.lemma_6_2_holds),
  (``LeanProofs.GowersSzemeredi.theorem_7_1, ``LeanProofs.GowersSzemeredi.theorem_7_1_holds),
  (``LeanProofs.GowersSzemeredi.theorem_7_2, ``LeanProofs.GowersSzemeredi.theorem_7_2_holds),
  (``LeanProofs.GowersSzemeredi.proposition_7_3, ``LeanProofs.GowersSzemeredi.proposition_7_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_7_4, ``LeanProofs.GowersSzemeredi.lemma_7_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_7_5, ``LeanProofs.GowersSzemeredi.lemma_7_5_holds),
  (``LeanProofs.GowersSzemeredi.corollary_7_6, ``LeanProofs.GowersSzemeredi.corollary_7_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_7_7, ``LeanProofs.GowersSzemeredi.lemma_7_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_7_8, ``LeanProofs.GowersSzemeredi.lemma_7_8_holds),
  (``LeanProofs.GowersSzemeredi.corollary_7_9, ``LeanProofs.GowersSzemeredi.corollary_7_9_holds),
  (``LeanProofs.GowersSzemeredi.corollary_7_10, ``LeanProofs.GowersSzemeredi.corollary_7_10_holds),
  (``LeanProofs.GowersSzemeredi.corollary_7_11, ``LeanProofs.GowersSzemeredi.corollary_7_11_holds),
  (``LeanProofs.GowersSzemeredi.proposition_8_1, ``LeanProofs.GowersSzemeredi.proposition_8_1_holds),
  (``LeanProofs.GowersSzemeredi.theorem_8_2, ``LeanProofs.GowersSzemeredi.theorem_8_2_holds),
  (``LeanProofs.GowersSzemeredi.corollary_8_3, ``LeanProofs.GowersSzemeredi.corollary_8_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_9_1, ``LeanProofs.GowersSzemeredi.lemma_9_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_9_2, ``LeanProofs.GowersSzemeredi.lemma_9_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_9_3, ``LeanProofs.GowersSzemeredi.lemma_9_3_holds),
  (``LeanProofs.GowersSzemeredi.corollary_9_4, ``LeanProofs.GowersSzemeredi.corollary_9_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_1, ``LeanProofs.GowersSzemeredi.lemma_10_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_2, ``LeanProofs.GowersSzemeredi.lemma_10_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_3, ``LeanProofs.GowersSzemeredi.lemma_10_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_4, ``LeanProofs.GowersSzemeredi.lemma_10_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_5, ``LeanProofs.GowersSzemeredi.lemma_10_5_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_6, ``LeanProofs.GowersSzemeredi.lemma_10_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_7, ``LeanProofs.GowersSzemeredi.lemma_10_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_8, ``LeanProofs.GowersSzemeredi.lemma_10_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_9, ``LeanProofs.GowersSzemeredi.lemma_10_9_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_10, ``LeanProofs.GowersSzemeredi.lemma_10_10_holds),
  (``LeanProofs.GowersSzemeredi.corollary_10_11, ``LeanProofs.GowersSzemeredi.corollary_10_11_holds),
  (``LeanProofs.GowersSzemeredi.lemma_10_12, ``LeanProofs.GowersSzemeredi.lemma_10_12_holds),
  (``LeanProofs.GowersSzemeredi.theorem_10_13, ``LeanProofs.GowersSzemeredi.theorem_10_13_holds),
  (``LeanProofs.GowersSzemeredi.corollary_10_14, ``LeanProofs.GowersSzemeredi.corollary_10_14_holds),
  (``LeanProofs.GowersSzemeredi.proposition_12_1, ``LeanProofs.GowersSzemeredi.proposition_12_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_12_2, ``LeanProofs.GowersSzemeredi.lemma_12_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_12_3, ``LeanProofs.GowersSzemeredi.lemma_12_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_12_4, ``LeanProofs.GowersSzemeredi.lemma_12_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_12_5, ``LeanProofs.GowersSzemeredi.lemma_12_5_holds),
  (``LeanProofs.GowersSzemeredi.lemma_12_6, ``LeanProofs.GowersSzemeredi.lemma_12_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_1, ``LeanProofs.GowersSzemeredi.lemma_13_1_holds),
  (``LeanProofs.GowersSzemeredi.corollary_13_2, ``LeanProofs.GowersSzemeredi.corollary_13_2_holds),
  (``LeanProofs.GowersSzemeredi.corollary_13_3, ``LeanProofs.GowersSzemeredi.corollary_13_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_4, ``LeanProofs.GowersSzemeredi.lemma_13_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_5, ``LeanProofs.GowersSzemeredi.lemma_13_5_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_6, ``LeanProofs.GowersSzemeredi.lemma_13_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_7, ``LeanProofs.GowersSzemeredi.lemma_13_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_8, ``LeanProofs.GowersSzemeredi.lemma_13_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_9, ``LeanProofs.GowersSzemeredi.lemma_13_9_holds),
  (``LeanProofs.GowersSzemeredi.corollary_13_10, ``LeanProofs.GowersSzemeredi.corollary_13_10_holds),
  (``LeanProofs.GowersSzemeredi.lemma_13_11, ``LeanProofs.GowersSzemeredi.lemma_13_11_holds),
  (``LeanProofs.GowersSzemeredi.theorem_13_12, ``LeanProofs.GowersSzemeredi.theorem_13_12_holds),
  (``LeanProofs.GowersSzemeredi.proposition_14_1, ``LeanProofs.GowersSzemeredi.proposition_14_1_holds),
  (``LeanProofs.GowersSzemeredi.lemma_14_2, ``LeanProofs.GowersSzemeredi.lemma_14_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_14_3, ``LeanProofs.GowersSzemeredi.lemma_14_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_14_4, ``LeanProofs.GowersSzemeredi.lemma_14_4_holds),
  (``LeanProofs.GowersSzemeredi.corollary_14_5, ``LeanProofs.GowersSzemeredi.corollary_14_5_holds),
  (``LeanProofs.GowersSzemeredi.corollary_14_6, ``LeanProofs.GowersSzemeredi.corollary_14_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_14_7, ``LeanProofs.GowersSzemeredi.lemma_14_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_14_8, ``LeanProofs.GowersSzemeredi.lemma_14_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_15_1, ``LeanProofs.GowersSzemeredi.lemma_15_1_holds),
  (``LeanProofs.GowersSzemeredi.corollary_15_2, ``LeanProofs.GowersSzemeredi.corollary_15_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_15_3, ``LeanProofs.GowersSzemeredi.lemma_15_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_15_4, ``LeanProofs.GowersSzemeredi.lemma_15_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_15_5, ``LeanProofs.GowersSzemeredi.lemma_15_5_holds),
  (``LeanProofs.GowersSzemeredi.lemma_15_6, ``LeanProofs.GowersSzemeredi.lemma_15_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_1, ``LeanProofs.GowersSzemeredi.lemma_16_1_holds),
  (``LeanProofs.GowersSzemeredi.theorem_16_2, ``LeanProofs.GowersSzemeredi.theorem_16_2_explicit),
  (``LeanProofs.GowersSzemeredi.lemma_16_3, ``LeanProofs.GowersSzemeredi.lemma_16_3_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_4, ``LeanProofs.GowersSzemeredi.lemma_16_4_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_5, ``LeanProofs.GowersSzemeredi.lemma_16_5_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_6, ``LeanProofs.GowersSzemeredi.lemma_16_6_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_7, ``LeanProofs.GowersSzemeredi.lemma_16_7_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_8, ``LeanProofs.GowersSzemeredi.lemma_16_8_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_9, ``LeanProofs.GowersSzemeredi.lemma_16_9_holds),
  (``LeanProofs.GowersSzemeredi.lemma_16_10, ``LeanProofs.GowersSzemeredi.lemma_16_10_holds),
  (``LeanProofs.GowersSzemeredi.corollary_16_11, ``LeanProofs.GowersSzemeredi.corollary_16_11_explicit),
  (``LeanProofs.GowersSzemeredi.lemma_17_1, ``LeanProofs.GowersSzemeredi.lemma_17_1_holds),
  (``LeanProofs.GowersSzemeredi.proposition_17_2, ``LeanProofs.GowersSzemeredi.proposition_17_2_holds),
  (``LeanProofs.GowersSzemeredi.lemma_17_4, ``LeanProofs.GowersSzemeredi.lemma_17_4_holds),
  (``LeanProofs.GowersSzemeredi.corollary_17_5, ``LeanProofs.GowersSzemeredi.corollary_17_5_holds),
  (``LeanProofs.GowersSzemeredi.corollary_17_6, ``LeanProofs.GowersSzemeredi.corollary_17_6_holds),
  (``LeanProofs.GowersSzemeredi.proposition_17_7, ``LeanProofs.GowersSzemeredi.proposition_17_7_holds),
  (``LeanProofs.GowersSzemeredi.theorem_18_1, ``LeanProofs.GowersSzemeredi.theorem_18_1_explicit),
  (``LeanProofs.GowersSzemeredi.theorem_18_2, ``LeanProofs.GowersSzemeredi.theorem_18_2_explicit),
  (``LeanProofs.GowersSzemeredi.corollary_18_7, ``LeanProofs.GowersSzemeredi.corollary_18_7_explicit)
]

run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  unless numberedCompanions.size == 120 do
    throwError "Expected all 120 numbered statements"
  let mut targets : NameSet := {}
  for (target, proof) in numberedCompanions do
    if targets.contains target then
      throwError "Duplicate numbered statement {target}"
    targets := targets.insert target
    let targetInfo ← getConstInfo target
    unless targetInfo.isDefinition do
      throwError "{target} is not a catalogue definition"
    let proofInfo ← getConstInfo proof
    unless proofInfo.isTheorem do
      throwError "{proof} is not a theorem"
    unless proofInfo.levelParams.length == targetInfo.levelParams.length do
      throwError "{proof} restricts the universe parameters of {target}"
    unless proofInfo.type == mkConst target (proofInfo.levelParams.map Level.param) do
      throwError "{proof} does not prove exactly {target}"
    for axiomName in (← collectAxioms proof) do
      unless allowed.contains axiomName do
        throwError "{proof} depends on unapproved axiom {axiomName}"
  logInfo "Checked exact proofs of all 120 numbered catalogue statements; only approved axioms."

import GowersSzemeredi.Proofs07ModularPartition
import GowersSzemeredi.Proofs13PartitionSelection

/-!
# The large-scale case of Lemma 13.7

This module keeps `stage137_partition_exponent`; the rest of the development,
with its description, is in `Proofs13LargeScaleExtractionSide`, outside the
final route. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- The corrected density gives precisely the exponent in Stage 13.7. -/
theorem stage137_partition_exponent (alpha : Real) :
    cor711Exponent ((2 : Real) ^ (-(43 : Int)) * alpha ^ 224) 1 =
      (2 : Real) ^ (-(100 : Int)) * alpha ^ 448 := by
  unfold cor711Exponent
  norm_num [Real.rpow_neg, zpow_neg]
  ring

end LeanProofs.GowersSzemeredi

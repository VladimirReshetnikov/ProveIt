/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def alternating0CheckpointCodes : Finset ℕ :=
  [298, 366, 446, 542, 558, 586, 698, 714, 742, 978,
   1022, 1054, 1202, 1346, 1398, 1454, 1766, 1778, 1830, 1934,
   1986, 2014, 2102, 2146, 2154, 2230, 2566, 2642, 2678, 2710,
   2790, 2886, 2902, 2930].toFinset

def alternating0Checkpoint : Finset S5 :=
  elementsWithCodes alternating0CheckpointCodes

def alternating0Stage4Codes : Finset ℕ :=
  [222, 298, 334, 366, 414, 446, 482, 542, 558, 586,
   698, 714, 742, 894, 978, 1022, 1054, 1110, 1138, 1190,
   1202, 1346, 1358, 1398, 1454, 1490, 1634, 1670, 1766, 1778,
   1830, 1922, 1934, 1986, 2014, 2070, 2102, 2146, 2154, 2230,
   2410, 2566, 2582, 2642, 2678, 2710, 2758, 2790, 2886, 2902,
   2930].toFinset

def alternating0Stage4 : Finset S5 :=
  elementsWithCodes alternating0Stage4Codes

def alternating0Stage5Codes : Finset ℕ :=
  [194, 222, 238, 298, 334, 366, 414, 446, 482, 542,
   558, 586, 698, 714, 742, 894, 970, 978, 1022, 1054,
   1110, 1138, 1190, 1202, 1294, 1346, 1358, 1398, 1454, 1490,
   1634, 1670, 1766, 1778, 1830, 1922, 1934, 1986, 2014, 2070,
   2102, 2146, 2154, 2230, 2382, 2410, 2426, 2538, 2566, 2582,
   2642, 2678, 2710, 2758, 2790, 2826, 2886, 2902, 2930].toFinset

def alternating0Stage5 : Finset S5 :=
  elementsWithCodes alternating0Stage5Codes




set_option maxRecDepth 100000 in
theorem alternating0_checkpoint_certificate :
    generatedStage (representative 4) 3 =
      alternating0Checkpoint := by
  decide


set_option maxRecDepth 100000 in
theorem alternating0_step_3_certificate :
    generationStep (representative 4) alternating0Checkpoint =
      alternating0Stage4 := by
  decide

set_option maxRecDepth 100000 in
theorem alternating0_step_4_certificate :
    generationStep (representative 4) alternating0Stage4 =
      alternating0Stage5 := by
  decide

set_option maxRecDepth 100000 in
theorem alternating0_step_5_certificate :
    generationStep (representative 4) alternating0Stage5 =
      classElements (representativeClass 4) := by
  decide


theorem alternating0_finish_certificate :
    iterateGenerationStep (representative 4)
      alternating0Checkpoint 3 =
        classElements (representativeClass 4) := by
  change generationStep (representative 4) (generationStep (representative 4) (generationStep (representative 4) (alternating0Checkpoint))) = classElements (representativeClass 4)
  rw [alternating0_step_3_certificate, alternating0_step_4_certificate, alternating0_step_5_certificate]

theorem alternating0_generation_certificate :
    generatedStage (representative 4) (representativeDepth 4) =
      classElements (representativeClass 4) := by
  change generatedStage (representative 4) 6 =
    classElements (representativeClass 4)
  calc
    generatedStage (representative 4) 6 =
        iterateGenerationStep (representative 4)
          (generatedStage (representative 4) 3)
          3 := by
      simpa using generatedStage_add (representative 4)
        3 3
    _ = iterateGenerationStep (representative 4)
          alternating0Checkpoint 3 := by
      rw [alternating0_checkpoint_certificate]
    _ = classElements (representativeClass 4) :=
      alternating0_finish_certificate

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationGenerationCore

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

def alternating1CheckpointCodes : Finset ℕ :=
  [222, 238, 334, 366, 414, 482, 586, 698, 742, 894,
   978, 1022, 1110, 1138, 1190, 1294, 1346, 1398, 1454, 1634,
   1670, 1766, 1830, 1922, 2070, 2102, 2154, 2230, 2410, 2426,
   2566, 2582, 2678, 2710, 2758, 2790, 2826, 2930].toFinset

def alternating1Checkpoint : Finset S5 :=
  elementsWithCodes alternating1CheckpointCodes

def alternating1Stage6Codes : Finset ℕ :=
  [222, 238, 334, 366, 414, 446, 482, 542, 558, 586,
   698, 742, 894, 978, 1022, 1054, 1110, 1138, 1190, 1294,
   1346, 1398, 1454, 1634, 1670, 1766, 1778, 1830, 1922, 1934,
   1986, 2014, 2070, 2102, 2154, 2230, 2410, 2426, 2566, 2582,
   2678, 2710, 2758, 2790, 2826, 2886, 2902, 2930].toFinset

def alternating1Stage6 : Finset S5 :=
  elementsWithCodes alternating1Stage6Codes

def alternating1Stage7Codes : Finset ℕ :=
  [222, 238, 298, 334, 366, 414, 446, 482, 542, 558,
   586, 698, 714, 742, 894, 978, 1022, 1054, 1110, 1138,
   1190, 1202, 1294, 1346, 1358, 1398, 1454, 1634, 1670, 1766,
   1778, 1830, 1922, 1934, 1986, 2014, 2070, 2102, 2146, 2154,
   2230, 2382, 2410, 2426, 2538, 2566, 2582, 2642, 2678, 2710,
   2758, 2790, 2826, 2886, 2902, 2930].toFinset

def alternating1Stage7 : Finset S5 :=
  elementsWithCodes alternating1Stage7Codes

def alternating1Stage8Codes : Finset ℕ :=
  [194, 222, 238, 298, 334, 366, 414, 446, 482, 542,
   558, 586, 698, 714, 742, 894, 978, 1022, 1054, 1110,
   1138, 1190, 1202, 1294, 1346, 1358, 1398, 1454, 1490, 1634,
   1670, 1726, 1766, 1778, 1830, 1922, 1934, 1986, 2014, 2070,
   2102, 2146, 2154, 2230, 2382, 2410, 2426, 2538, 2566, 2582,
   2642, 2678, 2710, 2758, 2790, 2826, 2886, 2902, 2930].toFinset

def alternating1Stage8 : Finset S5 :=
  elementsWithCodes alternating1Stage8Codes




set_option maxRecDepth 100000 in
theorem alternating1_checkpoint_certificate :
    generatedStage (representative 5) 5 =
      alternating1Checkpoint := by
  decide


set_option maxRecDepth 100000 in
theorem alternating1_step_5_certificate :
    generationStep (representative 5) alternating1Checkpoint =
      alternating1Stage6 := by
  decide

set_option maxRecDepth 100000 in
theorem alternating1_step_6_certificate :
    generationStep (representative 5) alternating1Stage6 =
      alternating1Stage7 := by
  decide

set_option maxRecDepth 100000 in
theorem alternating1_step_7_certificate :
    generationStep (representative 5) alternating1Stage7 =
      alternating1Stage8 := by
  decide

set_option maxRecDepth 100000 in
theorem alternating1_step_8_certificate :
    generationStep (representative 5) alternating1Stage8 =
      classElements (representativeClass 5) := by
  decide


theorem alternating1_finish_certificate :
    iterateGenerationStep (representative 5)
      alternating1Checkpoint 4 =
        classElements (representativeClass 5) := by
  change generationStep (representative 5) (generationStep (representative 5) (generationStep (representative 5) (generationStep (representative 5) (alternating1Checkpoint)))) = classElements (representativeClass 5)
  rw [alternating1_step_5_certificate, alternating1_step_6_certificate, alternating1_step_7_certificate, alternating1_step_8_certificate]

theorem alternating1_generation_certificate :
    generatedStage (representative 5) (representativeDepth 5) =
      classElements (representativeClass 5) := by
  change generatedStage (representative 5) 9 =
    classElements (representativeClass 5)
  calc
    generatedStage (representative 5) 9 =
        iterateGenerationStep (representative 5)
          (generatedStage (representative 5) 5)
          4 := by
      simpa using generatedStage_add (representative 5)
        5 4
    _ = iterateGenerationStep (representative 5)
          alternating1Checkpoint 4 := by
      rw [alternating1_checkpoint_certificate]
    _ = classElements (representativeClass 5) :=
      alternating1_finish_certificate

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

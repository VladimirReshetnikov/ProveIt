import DiophantineConsistency.GapCircuitSteps66
import DiophantineConsistency.NearSquareFinalizer

/-! # Public local tail identities for the literal H2082 evaluator
These bundle only the few needed gate equations. Fixed leaves stay arbitrary,
and no source correctness, positivity or coefficient calibration is used. -/
namespace DiophantineConsistency.GapCircuitTail66
open GapCircuitSteps66
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
variable {R : Type*} [CommRing R]

theorem natural_pell_D (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 415 = (naturalRegister p x 397^2-1)*naturalRegister p x 15^2+1 := by
  simp only [natural_step_415,natural_step_9,natural_step_414,natural_step_412,natural_step_411,natural_step_413]
  ring

theorem natural_pell_E (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 419 = naturalRegister p x 417*naturalRegister p x 415*naturalRegister p x 15 := by
  simp only [natural_step_419,natural_step_418]
  ring

theorem natural_pell_F (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 422 = (naturalRegister p x 397^2-1)*naturalRegister p x 419^2+1 := by
  simp only [natural_step_422,natural_step_9,natural_step_421,natural_step_412,natural_step_411,natural_step_420]
  ring

theorem natural_pell_I (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 436 = (naturalRegister p x 427^2-1)*naturalRegister p x 431^2+1 := by
  simp only [natural_step_436,natural_step_9,natural_step_435,natural_step_433,natural_step_432,natural_step_434]
  ring

theorem natural_tail_output (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 483 = NearSquareFinalizer.norm (naturalRegister p x 469) (naturalRegister p x 462) (naturalRegister p x 441) 8 (naturalRegister p x 443) := by
  simp only [natural_step_483,natural_step_477,natural_step_476,natural_step_470,natural_step_475,natural_step_471,natural_step_474,natural_step_473,natural_step_472,natural_step_482,natural_step_481,natural_step_480,natural_step_478,natural_step_479,NearSquareFinalizer.norm]
  ring

theorem natural_pell_DF (p : Fin 11 → R) (x : Fin 9 → R) :
    naturalRegister p x 415*naturalRegister p x 422 =
      naturalRegister p x 417^2*naturalRegister p x 415^3*(naturalRegister p x 415-1)+naturalRegister p x 415 :=
  NearSquareFinalizer.pell_product_identity _ _ _ _ _ _
    (natural_pell_D p x) (natural_pell_E p x) (natural_pell_F p x)

end DiophantineConsistency.GapCircuitTail66

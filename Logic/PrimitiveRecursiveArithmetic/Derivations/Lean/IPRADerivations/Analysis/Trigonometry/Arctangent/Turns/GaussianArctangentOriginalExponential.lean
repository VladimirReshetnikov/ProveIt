import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.GaussianArctangentCayleyBudget
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.GaussianArctangentCayleyTelescope
import IPRADerivations.Analysis.Trigonometry.Arctangent.Turns.GaussianArctangentExponentialPeriod

/-!
# The exponential quarter turn and period at the original arctangent name

The finite Cayley estimate at the actual π mesh supplies the endpoint
bound for the named exponential. The resulting quarter turn yields the
full period and its translation law.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace LeanProofs.IPRA.Analysis.GaussianArctangentOriginalExponential

open_ipra
open GaussianArctangentCayleyBudget (mesh_two mesh_budget)
open GaussianArctangentCayleyExponentialStep (sample)
open GaussianArctangentCayleyTelescope (error denominator endpoint_distance denominator_positive)
open GaussianArctangentCayleyValues (imaginaryPoint)
open GaussianArctangentExponentialPeriod (twiceF twiceData twiceRadius minusOne
  double_exponential_constant imaginary_square fullTurnF fullTurnData fullTurnRadius translationRadius)
open GaussianArctangentExponentialPrefix (prefixValue original_mesh_source at_pi_observation)
open GaussianArctangentQuarterExponential (argument finiteValue finiteEstimate exponentialF exponentialData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRadiusExponentialName (input nameF data)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem finite_endpoint (p z : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (finiteValue p z) imaginaryPoint (num 129) (unit p) := by
  let M := meshAt p
  let L := clearing p
  let s := GaussianArctangentCayleyBudget.stage p M
  have hM := mesh_two (Γ := Γ) p
  have hs := original_mesh_source (Γ := Γ) p
  have native := endpoint_distance M L s hs hM
  have hden := denominator_positive M s hs.andE₁
  have e : Γ ⊢[PRAAx] sample (prefixValue M M L) s ≐ finiteValue p z := by
    have harg : Γ ⊢[PRAAx] prefixValue M M L ≐ argument p z := at_pi_observation p z
    have h := Prf.eqCongr (sample (var 0) (var 1) : PTm 2)
      (σ := ![prefixValue M M L,s]) (σ' := ![argument p z,s])
      (fun j => by fin_cases j; exact harg; exact .eqRefl s)
    simpa [sample,finiteValue,GaussianArctangentQuarterExponential.radius,GaussianArctangentQuarterExponential.stage,
      GaussianArctangentCayleyBudget.stage,GaussianScalarExponentialProductTail.rectangleCutoff,
      GaussianScalarExponentialProductTail.reserve,GaussianScalarExponentialProductTail.growthExponent,M,s] using h
  exact distance_congr e (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ (M*error M s) (denominator M s) (num 129) (unit p) hden
      (unit_positive p) (mesh_budget p) native)

theorem original_finite_estimate (z : PTm n) : Γ ⊢[PRAAx] finiteEstimate z (num 129) := by
  refine .allI ?_
  simpa only [Syn.shift,PTm.subst_num] using
    finite_endpoint (Γ := Γ.map Fm.shift) (var 0) (Syn.shift z)

theorem quarter_cross (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent exponentialF constantF (exponentialData z) imaginaryPoint :=
  GaussianArctangentQuarterExponential.original_quarter_cross z (num 129) (original_finite_estimate z)

theorem half_turn_cross (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (nameF twiceF) constantF (data twiceRadius (twiceData z)) minusOne := by
  open GaussianArctangentQuarterExponential in
  exact double_exponential_constant quarterF radius z imaginaryPoint minusOne (le_succ_self one)
    (quarter_input z (original_bounded_arguments z)) (quarter_cross z) imaginary_square

theorem full_turn_cross (z : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (nameF fullTurnF) constantF (data fullTurnRadius (fullTurnData z)) qone :=
  GaussianArctangentExponentialPeriod.original_full_turn_cross z (num 129) (original_finite_estimate z)

theorem full_turn_translation (f : PR 2) (R x z : PTm n) (hx : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (addF f fullTurnF)) (nameF f)
      (data (translationRadius R) (addData x (fullTurnData z))) (data R x) :=
  GaussianArctangentExponentialPeriod.full_turn_translation f R x z (num 129) hx (original_finite_estimate z)

theorem actual_original_arctangent_quarter_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent exponentialF constantF (exponentialData (var 0)) imaginaryPoint) :=
  closeUniv 1 (quarter_cross _)

theorem actual_original_arctangent_half_turn_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent (nameF twiceF) constantF (data twiceRadius (twiceData (var 0))) minusOne) :=
  closeUniv 1 (half_turn_cross _)

theorem actual_original_arctangent_period_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent (nameF fullTurnF) constantF (data fullTurnRadius (fullTurnData (var 0))) qone) :=
  closeUniv 1 (full_turn_cross _)

theorem actual_original_arctangent_exponential_translation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (input f (var 0) (var 1) ⟶
        crossEquivalent (nameF (addF f fullTurnF)) (nameF f)
          (data (translationRadius (var 0)) (addData (var 1) (fullTurnData (var 2))))
          (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (full_turn_translation f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentOriginalExponential

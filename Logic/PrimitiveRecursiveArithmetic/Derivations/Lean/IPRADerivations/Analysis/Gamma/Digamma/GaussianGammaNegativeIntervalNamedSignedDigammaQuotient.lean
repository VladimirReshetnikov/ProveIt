import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaNegativeIntervalNamedDigammaQuotient
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaNegativeIntervalSignedDigammaQuotient

/-!
# Cofinal original signed Gamma quotients at named offsets

The literal normalized signed quotient at a rational freeze of a named
offset has the original shifted digamma as its limit. One additional
precision step pays for comparison with the unsigned quotient program,
while preserving the independent requested observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedSignedDigammaQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeIntervalDigammaRate (quotientF quotientData)
open GaussianGammaNegativeIntervalNamedDigamma (source data)
open GaussianGammaNegativeIntervalNamedDigammaQuotient
  (stage argumentNumerator argumentDenominator step base_guard step_inside sample_at)
open GaussianGammaNegativeIntervalSignedDigammaQuotient (nameF nameData original_cross)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "DF" => GaussianGammaNegativeIntervalNamedDigamma.nameF
local notation "raw" => GaussianGammaNegativeIntervalNamedDigammaQuotient.value

def value (f : PR 2) (p x E N : PTm n) : PTm n :=
  ap2 nameF (stage (succ p)) (nameData (argumentNumerator f (succ p) x E N)
    (argumentDenominator f (succ p) x E N) N (step f (succ p) x E N))

theorem original_observations (f : PR 2) (p q x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] distanceBounded (value f p x E N) (ap2 (DF f) q (data x E N))
      (unit p+unit q) (unit p*unit q) := by
  let r := succ p
  let s := stage r
  let P := unit p
  let U := unit q
  let V := unit r
  let T := unit s
  let a := argumentNumerator f r x E N
  let b := argumentDenominator f r x E N
  let D := step f r x E N
  have hp := unit_positive (Γ := Γ) p
  have hu := unit_positive (Γ := Γ) q
  have hv := unit_positive (Γ := Γ) r
  have ht := unit_positive (Γ := Γ) s
  have htu := positive_product _ _ ht ht
  have hvu := positive_product _ _ hv hu
  have compatible := original_cross a b N D (base_guard f r x E N h) (step_inside f r x E N h)
  have sign : Γ ⊢[PRAAx] distanceBounded (value f p x E N) (raw f r x E N) two T :=
    distance_radius_mono _ _ _ _ _ _ htu ht (by ipra_le 0)
      (cross_at nameF quotientF (nameData a b N D) (quotientData a b N D) s s compatible)
  have compare := distance_congr (sample_at f r x E N) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianGammaNegativeIntervalNamedDigammaQuotient.original_observations f r q x E N h)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ ht hvu sign compare
  have e : Γ ⊢[PRAAx] V ≐ two*P := (pw_succ two p).eqTrans (mul_comm _ _)
  have es := natEq e
  have t4 : Γ ⊢[PRAAx] unit (succ r) ≐ num 4*P :=
    (pw_succ two r).eqTrans ((congrMul e (.eqRefl _)).eqTrans (by ipra_ring))
  have room : Γ ⊢[PRAAx] le (num 4*P) T := le_congr t4 (.eqRefl _)
    (GaussianExponentialReference.unit_monotone (le_trans (le_succ_self (succ r)) (le_succ_self (succ (succ r)))))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht hvu) (positive_product _ _ hp hu)
    (by change Γ ⊢[PRAAx] le ((two*(V*U)+(V+U)*T)*(P*U)) ((P+U)*(T*(V*U)))
        ipra_le 𝔞(P)*𝔞(U)^2*sl room using rw [es]; ring) joined

theorem actual_original_negative_interval_named_signed_unit_quotients_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 2) (var 3) ⟶
        distanceBounded (value f (var 0) (var 2) (var 3) (var 4)) (ap2 (DF f) (var 1) (data (var 2) (var 3) (var 4)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (original_observations f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedSignedDigammaQuotient

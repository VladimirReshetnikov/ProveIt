import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyBudget
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyTelescope

/-!
# Cayley estimates at rational partial arctangent endpoints

The Gaussian rational endpoint depends only on the fraction A/B.
Refining the grid by N multiplies both integer coordinates and their
denominator by the same N². The partial telescope therefore compares
the native arctangent prefix exponential to a fixed rational point.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (numerator denominator value denominator_positive)
open GaussianArctangentCayleyExponentialStep (sample)
open GaussianArctangentCayleyBudget (stage budget)
open GaussianArctangentExponentialPrefix (prefixValue source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner
  (ofGaussian_canonical ofGaussian_represents positive_product canonical_unique represents_congr represents_rescale)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRootAlgebra (equal equal_of_values re_scale im_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem refined_value (A B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] value (B*N) (A*N) ≐ value B A := by
  let D := denominator B A
  let E := denominator (B*N) (A*N)
  let X := numerator B A
  have hD := denominator_positive B A hB
  have hE := denominator_positive (B*N) (A*N) (positive_product _ _ hB hN)
  have eD : Γ ⊢[PRAAx] D*(N*N) ≐ E := by
    unfold D E denominator
    ipra_ring
  have eX : Γ ⊢[PRAAx] equal (numerator (B*N) (A*N)) (scale (N*N) X) := by
    dsimp only [X]
    apply equal_of_values <;>
      simp only [numerator,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,re_scale,im_scale] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ E (ofGaussian_canonical _ _ hE) (ofGaussian_canonical _ _ hD) hE
    (represents_congr (.eqRefl _) eX (.eqRefl _) (ofGaussian_represents _ _ hE))
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) eD
      (represents_rescale _ X D (N*N) (ofGaussian_represents _ _ hD)))

theorem rational_endpoint_estimate (A B N p : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hN : Γ ⊢[PRAAx] le two N) (hprecision : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded
      (sample (prefixValue (A*N) (B*N) (two*((B*N)*(B*N)))) (stage p (B*N)))
        (value B A) (num 129) (unit p) := by
  let M := B*N
  let K := A*N
  let L := two*(M*M)
  let s := stage p M
  let E := GaussianArctangentCayleyTelescope.error M s
  let D := GaussianArctangentCayleyTelescope.denominator M s
  have nM : Γ ⊢[PRAAx] le N M := le_congr (one_mul N) (.eqRefl _) (le_mul_mono hB (le_refl _))
  have mTwo := le_trans hN nM
  have mOne := le_trans (le_succ_self one) mTwo
  have kM : Γ ⊢[PRAAx] le K M := le_mul_mono hA (le_refl N)
  have hs : Γ ⊢[PRAAx] source M L := .andI mOne (le_refl L)
  have hD := GaussianArctangentCayleyTelescope.denominator_positive M s mOne
  have hbudget : Γ ⊢[PRAAx] le ((M*E)*unit p) (num 129*D) :=
    le_congr (.eqRefl _) (by unfold D GaussianArctangentCayleyTelescope.denominator; ipra_ring)
      (budget (num 128) p M (le_trans hprecision nM))
  have hcost := le_trans (le_mul_mono (le_mul_mono kM (le_refl E)) (le_refl (unit p))) hbudget
  have hnative := GaussianArctangentCayleyTelescope.partial_distance K M L s hs mTwo kM
  have hvalue := refined_value A B N hB (le_trans (le_succ_self one) hN)
  exact distance_congr (.eqRefl _) hvalue (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hD (unit_positive p) hcost hnative)

theorem actual_rational_partial_arctangent_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ le two (var 2) ⟶ le (unit (var 3)) (var 2) ⟶
      distanceBounded (sample (prefixValue (var 0*var 2) (var 1*var 2)
        (two*((var 1*var 2)*(var 1*var 2)))) (stage (var 3) (var 1*var 2)))
        (value (var 1) (var 0)) (num 129) (unit (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (rational_endpoint_estimate _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyRefinement

import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicDyadicUpper

/-!
# Dyadic bound for the literal Barnes head correction

Collect the quadratic terms before estimating the exponential. The
harmonic sum gives an exponent bound in terms of the dyadic size of the
number of terms.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicHeadCorrection

open_ipra
open ComplexLogarithmRemainder (bounded_mono)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalHeadCorrectionDerivative (halfSquare total_formula)
open GaussianBarnesCanonicalHead (source)
open GaussianGammaCanonicalExponent (harmonic harmonicPoint harmonic_represents)
open GaussianGammaCanonicalExponentBound (scalar_representation_bound)
open GaussianGammaEulerHead (fraction_disk)
open GaussianNamedNaturalScale (natural_point_bound)
open GaussianRationalHorner (ofGaussian qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (bound_congr bounded_difference bounded_product)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem harmonic_bound (N j : PTm n) (hN : Γ ⊢[PRAAx] le N (pw two j)) :
    Γ ⊢[PRAAx] bounded (harmonicPoint N) (one+j) one := by
  let F := fact N
  let H := S N F
  refine scalar_representation_bound (harmonic N) (one+j) F (ZT.ofNat H)
    (GammaEulerMesh.factorial_positive N) (harmonic_represents N) ?_ ?_
  · apply zle_of_toZ H
    simp only [ZT.toZ_ofNat, Q.mk_zero, map_zero, _root_.zero_add]
  · have h := RationalHarmonicDyadicUpper.upper N j F hN
    apply zle_of_toZ (monus ((one+j)*F) H)
    simpa only [ZT.toZ_ofNat, Q.mk_add, map_add] using (natEq (eq_add_of_le h)).symm

def radius (R N j : PTm n) : PTm n := R*R*(one+j)+N*R

theorem correction_bound (z R B N j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hN : Γ ⊢[PRAAx] le N (pw two j)) : Γ ⊢[PRAAx] bounded (total z B N) (radius R N j) one := by
  let x := ofGaussian z B
  let y := ofGaussian z (two*B)
  let H := harmonicPoint N
  let L := one+j
  have onePos : Γ ⊢[PRAAx] le one one := le_refl one
  have hx := fraction_disk z R B hz.andE₁ hz.andE₂
  have larger : Γ ⊢[PRAAx] le B (two*B) :=
    le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B (le_succ_self one))
  have hy := fraction_disk z R (two*B) (le_trans hz.andE₁ larger)
    (bounded_mono hz.andE₂ (mul_le_mul_left R larger))
  have square : Γ ⊢[PRAAx] bounded (halfSquare z B) (R*R) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one) (bounded_product x y R one R one onePos onePos hx hy)
  have quadratic : Γ ⊢[PRAAx] bounded (qmul (halfSquare z B) H) (R*R*L) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
      (bounded_product _ _ (R*R) one L one onePos onePos square (harmonic_bound N j hN))
  have linear : Γ ⊢[PRAAx] bounded (qmul (naturalPoint N) x) (N*R) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
      (bounded_product _ _ N one R one onePos onePos (natural_point_bound N) hx)
  exact bound_congr (total_formula z B N hz.andE₁).eqSymm
    (by dsimp [radius,L]; ipra_ring) (one_mul one)
    (bounded_difference _ _ _ one _ one onePos onePos quadratic linear)

theorem actual_Barnes_dyadic_head_correction_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let R := var 1
     let B := var 2
     let N := var 3
     let j := var 4
     source z R B ⟶ le N (pw two j) ⟶ bounded (total z B N) (radius R N j) one) :=
  closeUniv 5 (.impI (.impI (correction_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicHeadCorrection

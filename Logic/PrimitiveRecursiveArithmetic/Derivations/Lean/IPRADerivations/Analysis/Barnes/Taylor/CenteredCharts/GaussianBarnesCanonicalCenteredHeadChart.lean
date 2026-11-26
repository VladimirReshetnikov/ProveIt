import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProduct
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling

/-!
# Chart independence of the original centered Barnes head

Equality of the canonical center fraction preserves every stored linear
factor and the entire recursive polynomial buffer, for any common cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHeadChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalCenteredHead (advance linear factor polynomial polynomial_zero polynomial_succ)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalHeadPolynomial (degree)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial)
open GaussianGammaEncodingRescaling (fraction_rescale)
open GaussianGammaExponentStep (reciprocal_times_point)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianGammaLinearCoefficient (monomial)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMonicReduction (singleton)
open GaussianRationalPolynomialBuffers (added leftPad)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem base_proper (z w B D i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] base z B (succ i) ≐ base w D (succ i) :=
  qadd_congr (.eqRefl _) ((reciprocal_times_point z B i hB).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) hq).eqTrans (reciprocal_times_point w D i hD)))

theorem linear_proper (z w B D i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] linear z B i ≐ linear w D i := by
  ipra_congr (added (monomial (reciprocalPoint (var 0))) (leftPad (singleton (var 1)) one) two : PTm 2) with
    [.eqRefl i, base_proper z w B D i hB hD hq] using [linear]

theorem factor_proper (z w B D i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] factor z B i ≐ factor w D i := by
  ipra_congr (GaussianRationalPolynomialPowers.power (var 0) one (succ (var 1)) : PTm 2) with
    [linear_proper z w B D i hB hD hq, .eqRefl i] using [factor]

private theorem advance_proper (z w B D i C C' : PTm n)
    (hC : Γ ⊢[PRAAx] C ≐ C') (hf : Γ ⊢[PRAAx] factor z B i ≐ factor w D i) :
    Γ ⊢[PRAAx] advance z B i C ≐ advance w D i C' := by
  ipra_congr (product (var 0) (var 1) (degree (var 2)) (succ (var 2)) : PTm 3) with
    [hC, hf, .eqRefl i] using [advance]

theorem polynomial_proper (z w B D N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] polynomial z B N ≐ polynomial w D N := by
  let Δ := Γ.map Fm.shift
  have bs : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Δ,Fm.shift,Syn.shift] using hB.shift
  have ds : Δ ⊢[PRAAx] le one (Syn.shift D) := by simpa [Δ,Fm.shift,Syn.shift] using hD.shift
  have qs : Δ ⊢[PRAAx] ofGaussian (Syn.shift z) (Syn.shift B) ≐ ofGaussian (Syn.shift w) (Syn.shift D) := by
    simpa [Δ,Fm.shift,Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all
      (polynomial (Syn.shift z) (Syn.shift B) (var 0) ≐ polynomial (Syn.shift w) (Syn.shift D) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (polynomial_zero z B).eqTrans (polynomial_zero w D).eqSymm
    · simp only [Fm.subst_eq,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (polynomial_succ _ _ _).eqTrans
        ((advance_proper _ _ _ _ (var 0) _ _ Prf.hyp0 (factor_proper _ _ _ _ _ bs.wk ds.wk qs.wk)).eqTrans
          (polynomial_succ _ _ _).eqSymm)
  simpa only [Fm.subst_eq,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem head_proper (z w R B D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] headPolynomial z R B ≐ headPolynomial w R D :=
  polynomial_proper z w B D _ hB hD hq

theorem head_rescale (z R B E : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] headPolynomial (scale E z) R (E*B) ≐ headPolynomial z R B :=
  head_proper _ _ R _ _ (positive_product E B hE hB) hB (fraction_rescale z B E hB hE)

theorem actual_Barnes_centered_head_chart_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     le one B ⟶ le one D ⟶ ofGaussian z B ≐ ofGaussian w D ⟶ headPolynomial z R B ≐ headPolynomial w R D) :=
  closeUniv 5 (.impI (.impI (.impI (head_proper (var 0) (var 1) (var 2) (var 3) (var 4)
    (Prf.hyp0.wk.wk) Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredHeadChart

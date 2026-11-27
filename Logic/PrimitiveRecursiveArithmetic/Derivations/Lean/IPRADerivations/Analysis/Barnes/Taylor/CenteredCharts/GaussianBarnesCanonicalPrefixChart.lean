import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.FiniteApproximants.GaussianBarnesCanonicalFiniteCentralExponential
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaExponentStep

/-!
# Chart independence of the retained Barnes exponent

The original prefactor exponent and the original finite sum of head
corrections have identical data at equivalent rational inputs. This
also identifies the data sent to the prefix exponential sampler.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixChart

open_ipra
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalCorrectionShift (body body_at parameters total)
open GaussianBarnesCanonicalFactor (correction)
open GaussianBarnesCanonicalFiniteCentralExponential (prefixExpData)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf square)
open GaussianBarnesCanonicalSingleExponential (prefactorExponentData prefixData prefixF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameArithmetic (addData)
open GaussianRationalHorner (ofGaussian positive_product qmul)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Dividing two equivalent rational points by one positive integer
preserves exact equality of their canonical rational codes. -/
theorem divided_point_proper (z w B D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] ofGaussian z (B*k) ≐ ofGaussian w (D*k) := by
  let i := pred k
  have h : Γ ⊢[PRAAx] succ i ≐ k := (Common.pos_of_one_le hk).eqSymm
  have code (x b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
      qmul (GaussianGammaHarmonicIncrement.reciprocalPoint i) (ofGaussian x b) ≐ ofGaussian x (b*k) :=
    (GaussianGammaExponentStep.reciprocal_times_point x b i hb).eqTrans (by
      ipra_congr (ofGaussian (var 0) ((var 1)*(var 2)) : PTm 3) with [.eqRefl x, .eqRefl b, h])
  exact (code z B hB).eqSymm.eqTrans ((qmul_congr (.eqRefl _) he).eqTrans (code w D hD))

theorem row_proper (z w B D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] correction z B k ≐ correction w D k := by
  have denom (b : PTm n) : Γ ⊢[PRAAx] two*(b*k) ≐ b*(two*k) := by ipra_ring
  have rebase (x b : PTm n) : Γ ⊢[PRAAx] ofGaussian x (two*(b*k)) ≐ ofGaussian x (b*(two*k)) := by
    ipra_congr (ofGaussian (var 0) (var 1) : PTm 2) with [.eqRefl x, denom b]
  have h := divided_point_proper z w B D (two*k) hB hD (positive_product _ _ (le_succ_self one) hk) he
  exact qsub_congr (qmul_congr he ((rebase z B).eqTrans (h.eqTrans (rebase w D).eqSymm))) he

theorem total_proper (z w B D N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] total z B N ≐ total w D N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded body body N (parameters z B) (parameters w D)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  have hB' : Δ ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,Δ,one] using hB.shift.wk
  have hD' : Δ ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,Δ,one] using hD.shift.wk
  have he' : Δ ⊢[PRAAx] ofGaussian (Syn.shift z) (Syn.shift B) ≐ ofGaussian (Syn.shift w) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift,Δ] using he.shift.wk
  have left := body_at (Γ := Δ) j (Syn.shift z) (Syn.shift B)
  have right := body_at (Γ := Δ) j (Syn.shift w) (Syn.shift D)
  have rows := row_proper (Syn.shift z) (Syn.shift w) (Syn.shift B) (Syn.shift D) (succ j)
    hB' hD' (zero_lt_succ j) he'
  simpa only [Syn.shift,GaussianBarnesCanonicalCorrectionShift.subst_parameters,j,Δ] using
    left.eqTrans (rows.eqTrans right.eqSymm)

theorem prefactor_data_proper (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] prefactorExponentData z B ≐ prefactorExponentData w D := by
  have hs : Γ ⊢[PRAAx] square z B ≐ square w D := qmul_congr he he
  ipra_congr (exponentOf (var 0) (var 1) : PTm 2) with [he, hs] using [prefactorExponentData]

theorem prefix_data_proper (z w R B D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] prefixData z R B ≐ prefixData w R D := by
  ipra_congr (addData (var 0) (var 1) : PTm 2) with
    [prefactor_data_proper z w B D he, total_proper z w B D _ hB hD he] using [prefixData]

theorem prefix_exponential_data_proper (z w R B D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] prefixExpData z R B ≐ prefixExpData w R D := by
  ipra_congr (exponentialInputData prefixF (var 0) : PTm 1) with
    [prefix_data_proper z w R B D hB hD he] using [prefixExpData,exponentialInputData]

theorem actual_Barnes_prefix_exponent_chart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 4) ⟶ ofGaussian (var 0) (var 3) ≐ ofGaussian (var 1) (var 4) ⟶
      prefixExpData (var 0) (var 2) (var 3) ≐ prefixExpData (var 1) (var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (prefix_exponential_data_proper _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_Barnes_prefix_exponent_rescale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶
      prefixExpData (scale (var 3) (var 0)) (var 1) ((var 3)*(var 2)) ≐ prefixExpData (var 0) (var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (prefix_exponential_data_proper _ _ _ _ _
    (positive_product _ _ Prf.hyp0 Prf.hyp1) Prf.hyp1
    (GaussianGammaEncodingRescaling.fraction_rescale _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixChart

import IPRADerivations.Analysis.Gamma.Taylor.FinitePolynomials.GaussianGammaPolynomialConstantLinear

/-!
# Literal low-coefficient coherence of the original Gamma exponent

The actual exponent buffer has its original sampled gamma-H_N linear
coefficient and its original reciprocal-power tail at every higher
exponent. Its actual zero-extended exponent reader is independent of
the degree horizon whenever the requested exponent fits both horizons.
Only buffer lookups and original padding are used. This removes the
first degree-horizon dependence needed for all-degree C19; stability
of actual powers and names for their finite expressions remain separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExponentCoefficientStability

open_ipra
open GaussianRationalHorner (qzero qmul)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianGammaExponentCoefficientPolynomial (polynomial)
open GaussianGammaReciprocalDegreeCells (degree)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialExponentialStability (exponent_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem linear_buffer_high (q N L j : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaExponentCoefficientPolynomial.linear q N L) (monus (degree L) (degree j)) ≐ qzero := by
  have idx : Γ ⊢[PRAAx] monus (degree L) (degree j) ≐ monus L j :=
    (succ_monus_succ (succ L) (succ j)).eqTrans (succ_monus_succ L j)
  exact (entry_congr (.eqRefl _) idx).eqTrans
    (GaussianRationalPolynomialBuffers.pad_leading _ (succ L) _
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left L j)))

theorem original_input_high (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    entry (polynomial q N L) (monus (degree L) (degree j)) ≐
      qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j))
        (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.tailSample q (degree j) N)) :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _
    ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))).eqTrans
      ((qadd_congr (linear_buffer_high q N L j) (GaussianGammaZetaCoefficientPolynomial.polynomial_high q N L j hj)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem high_reader (q N L j : PTm n) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) (degree j) ≐
      qmul (GaussianFiniteLogarithmPolynomial.coefficient (succ j))
        (RationalGaussianEmbedding.embed (RationalReciprocalPowerName.tailSample q (degree j) N)) :=
  (exponent_inside _ _ _ (le_congr (by unfold degree; ipra_ring) (by unfold degree; ipra_ring)
    (add_le_add_right two hj))).eqTrans (original_input_high q N L j hj)

theorem zero_reader (q N L : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) zero ≐ qzero :=
  (GaussianGammaPolynomialConstantLinear.constant_reader _ _).eqTrans
    (GaussianGammaPolynomialConstantLinear.input_constant q N L)

theorem linear_reader (q N L : PTm n) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) one ≐ GaussianGammaLinearCoefficient.coefficient q N :=
  (exponent_inside _ _ _ (le_trans (le_succ_self one) (GaussianGammaZetaDegreeName.degree_positive L))).eqTrans
    (GaussianGammaPolynomialConstantLinear.input_linear q N L)

theorem high_horizon_coherence (q N L M j : PTm n) (hjL : Γ ⊢[PRAAx] le j L)
    (hjM : Γ ⊢[PRAAx] le j M) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) (degree j) ≐
      exponentCoefficient (polynomial q N M) (degree M) (degree j) :=
  (high_reader q N L j hjL).eqTrans (high_reader q N M j hjM).eqSymm

theorem input_horizon_coherence (q N L M e : PTm n) (heL : Γ ⊢[PRAAx] le e (degree L))
    (heM : Γ ⊢[PRAAx] le e (degree M)) : Γ ⊢[PRAAx]
    exponentCoefficient (polynomial q N L) (degree L) e ≐ exponentCoefficient (polynomial q N M) (degree M) e := by
  refine .orE (zero_or_succ e) ?_ ?_
  · exact (exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      ((zero_reader q N L).eqTrans ((zero_reader q N M).eqSymm.eqTrans
        (exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm)))
  · refine .orE (zero_or_succ (pred e)) ?_ ?_
    · have form : ((pred e ≐ zero) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact (exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans
        ((linear_reader q N L).eqTrans ((linear_reader q N M).eqSymm.eqTrans
          (exponent_congr (.eqRefl _) (.eqRefl _) form.eqSymm)))
    · have form : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ degree (pred (pred e)) :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hl := le_congr form (.eqRefl _) heL.wk.wk
      have hm := le_congr form (.eqRefl _) heM.wk.wk
      have jl : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (pred (pred e)) L :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans hl)
      have jm : ((pred e ≐ succ (pred (pred e))) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (pred (pred e)) M :=
        (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans hm)
      exact (exponent_congr (.eqRefl _) (.eqRefl _) form).eqTrans
        ((high_horizon_coherence q N L M _ jl jm).eqTrans
          (exponent_congr (.eqRefl _) (.eqRefl _) form.eqSymm))

theorem original_Gamma_exponent_degree_horizon_coherence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (degree (var 2)) ⟶ le (var 4) (degree (var 3)) ⟶
      exponentCoefficient (polynomial (var 0) (var 1) (var 2)) (degree (var 2)) (var 4) ≐
        exponentCoefficient (polynomial (var 0) (var 1) (var 3)) (degree (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (input_horizon_coherence _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaExponentCoefficientStability

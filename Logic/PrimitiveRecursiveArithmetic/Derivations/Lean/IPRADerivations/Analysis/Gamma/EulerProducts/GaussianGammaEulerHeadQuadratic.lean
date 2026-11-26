import IPRADerivations.Analysis.Polynomials.GaussianPolynomialLinearFactorCoefficients
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaPolynomialConstantLinear
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalFiniteRoots
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual original Euler head quadratic coefficient

Original degree-one-factor convolution and genuine numerical induction
show that the coefficient of X² in X product(k=1..N)(1+X/k) is the
unchanged original harmonicPoint N. The theorem starts at positive N,
so its literal buffer index never aliases the leading linear coefficient
at N=0. No coefficient recurrence or value law is an input contract.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadQuadratic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qadd_congr qmul_congr)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem reciprocal_canonical (N : PTm n) : Γ ⊢[PRAAx] canonical (reciprocalPoint N) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (zero_lt_succ N)

theorem factor_leading (N : PTm n) : Γ ⊢[PRAAx]
    entry (GaussianGammaEulerFactorPolynomial.polynomial N) zero ≐ reciprocalPoint N :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (zero_lt_succ one)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_leading _)
      (GaussianRationalPolynomialBuffers.pad_leading _ one zero (le_refl one))).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (reciprocal_canonical N)))

theorem harmonic_zero : Γ ⊢[PRAAx] harmonicPoint (zero : PTm n) ≐ qzero := by
  let h := harmonicPoint (zero : PTm n)
  have hn := GaussianRationalMetric.bounded_zero_norm (Γ := Γ) h _ _ one
    (GaussianRationalL1.raw_den_positive h) (le_refl one)
    (GaussianRationalL1.raw_represents h) (GaussianGammaCanonicalExponentBound.harmonic_point_bound zero)
  exact GaussianRationalFiniteRoots.canonical_zero_of_norm_zero h
    (RationalGaussianEmbedding.embed_canonical _) hn

theorem head_quadratic_zero : Γ ⊢[PRAAx]
    entry (polynomial (one : PTm n)) zero ≐ harmonicPoint one := by
  have head : Γ ⊢[PRAAx] entry (polynomial (one : PTm n)) zero ≐ reciprocalPoint zero :=
    (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ zero) (.eqRefl zero)).eqTrans
    ((GaussianPolynomialLinearFactorCoefficients.bilinear_leading _ _).eqTrans
      ((qmul_congr
        ((entry_congr GaussianGammaEulerHeadPolynomial.polynomial_zero (.eqRefl zero)).eqTrans
          (GaussianGammaLinearCoefficient.monomial_leading qone))
        (factor_leading zero)).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (reciprocal_canonical zero))))
  have harmonic := (harmonic_point_increment (Γ := Γ) zero).eqTrans
    ((qadd_congr harmonic_zero (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (reciprocal_canonical zero)))
  exact head.eqTrans harmonic.eqSymm

def quadraticLaw (r : PTm n) : Fm PTm n :=
  entry (polynomial (succ r)) r ≐ harmonicPoint (succ r)
@[simp] theorem subst_quadraticLaw {m : ℕ} (σ : Fin n → PTm m) (r : PTm n) :
    (quadraticLaw r).subst σ = quadraticLaw (Syn.subst σ r) := by simp [quadraticLaw]

theorem head_quadratic_step (r : PTm n) (ih : Γ ⊢[PRAAx] quadraticLaw r) : Γ ⊢[PRAAx]
    quadraticLaw (succ r) := by
  have linear : Γ ⊢[PRAAx] entry (polynomial (succ r)) (succ r) ≐ qone :=
    (entry_congr (.eqRefl _) ((succ_monus_succ (succ r) zero).eqTrans (monus_zero (succ r))).eqSymm).eqTrans
      (GaussianGammaPolynomialConstantLinear.head_low (succ r)).andE₂
  exact (entry_congr (GaussianGammaEulerHeadPolynomial.polynomial_succ (succ r)) (.eqRefl _)).eqTrans
    ((GaussianPolynomialLinearFactorCoefficients.quadratic_value _ _ r).eqTrans
      ((qadd_congr
        ((qmul_congr ih (GaussianGammaPolynomialConstantLinear.factor_constant (succ r))).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (RationalGaussianEmbedding.embed_canonical _)))
        ((qmul_congr linear (factor_leading (succ r))).eqTrans
          (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (reciprocal_canonical (succ r))))).eqTrans
            (harmonic_point_increment (succ r)).eqSymm))

theorem head_quadratic_positive (r : PTm n) : Γ ⊢[PRAAx] quadraticLaw r := by
  have all : Γ ⊢[PRAAx] .all (quadraticLaw (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_quadraticLaw,Syn.subst_var,Syn.inst_zero]
      exact head_quadratic_zero
    · simp only [subst_quadraticLaw,Syn.subst_var,Syn.repl_zero]
      exact head_quadratic_step _ Prf.hyp0
  simpa only [subst_quadraticLaw,Syn.subst_var,Syn.inst_zero] using all.allE r

theorem head_quadratic (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    entry (polynomial N) (LeanProofs.IPRA.PTm.monus (succ N) two) ≐ harmonicPoint N := by
  have form := RationalIntegerNormalization.positive_form (Γ := Γ) hN
  have idx : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus (succ N) two ≐ LeanProofs.IPRA.PTm.pred N :=
    (congrMonus (congrSucc form) (.eqRefl two)).eqTrans
      ((succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _)))
  have harmonic : Γ ⊢[PRAAx] harmonicPoint N ≐ harmonicPoint (succ (LeanProofs.IPRA.PTm.pred N)) := by
    ipra_congr (harmonicPoint (var 0) : PTm 1) with [form]
  exact (entry_congr (congrAp2 GaussianGammaEulerHeadPolynomial.headF form (.eqRefl zero)) idx).eqTrans
    ((head_quadratic_positive _).eqTrans harmonic.eqSymm)

theorem original_positive_Euler_head_quadratic_is_harmonic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (entry (polynomial (succ (var 0))) (var 0) ≐ harmonicPoint (succ (var 0))) :=
  closeUniv 1 (head_quadratic_positive _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadQuadratic

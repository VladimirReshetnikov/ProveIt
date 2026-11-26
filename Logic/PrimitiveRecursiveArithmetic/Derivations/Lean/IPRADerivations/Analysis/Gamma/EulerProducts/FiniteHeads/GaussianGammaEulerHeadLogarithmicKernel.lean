import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadHarmonicNewton
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialFirstCoefficients

/-!
# The actual harmonic-power kernel multiplies the original head Euler buffer

A real coefficient sequence stores K_0=1 and
K_m=(-1)^(m-1) H_N^(m) for m>0, using the SAME original finite harmonic
power prefixes. The actual product(kernel, original head) has exactly
the original head's Euler coefficients through both declared degree
bounds. Genuine original Cauchy lookup, first-term splitting and the
proved original Newton sum establish the identity. The raw coefficient
at the constant kernel cell is handled through actual recode transport;
no arbitrary input code is assumed canonical.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadLogarithmicKernel

open_ipra
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside cauchySum term termBody data)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalEulerCoefficients (euler parityPoint)
open GaussianGammaEulerHeadExponentStep (reader)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaHarmonicPowerPoints (point)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sourceCoefficient (N m : PTm n) : PTm n := RationalArithmetic.select (Signum.sg m) qone
  (qmul (parityPoint (pred m)) (point m N))
def rowBody : PTm 2 := sourceCoefficient (fstT (var 1)) (monus (sndT (var 1)) (var 0))
def kernel (N D : PTm n) : PTm n := sequence rowBody (succ D) (pairT N D)
ipra_subst sourceCoefficient [Signum.sg]
ipra_subst kernel

theorem coefficient_congr {N M m k : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M) (hm : Γ ⊢[PRAAx] m ≐ k) :
    Γ ⊢[PRAAx] sourceCoefficient N m ≐ sourceCoefficient M k := by
  ipra_congr (sourceCoefficient (var 0) (var 1) : PTm 2) with [hN, hm]

theorem parity_congr {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] parityPoint j ≐ parityPoint k := by
  ipra_congr (parityPoint (var 0) : PTm 1) with [h]

theorem coefficient_zero (N : PTm n) : Γ ⊢[PRAAx] sourceCoefficient N zero ≐ qone :=
  RationalArithmetic.select_zero _ _ _ Signum.sg_zero

theorem coefficient_succ (N j : PTm n) : Γ ⊢[PRAAx]
    sourceCoefficient N (succ j) ≐ qmul (parityPoint j) (point (succ j) N) :=
  (RationalArithmetic.select_one _ _ _ (Signum.sg_succ j)).eqTrans (qmul_congr (parity_congr (pred_succ j)) (.eqRefl _))

theorem kernel_length (N D : PTm n) : Γ ⊢[PRAAx] length (kernel N D) ≐ succ D := sequence_length _ _ _

theorem row_at (N D i : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (pairT N D) ≐ sourceCoefficient N (monus D i) := by
  simp only [rowBody,inst2,subst_sourceCoefficient,PTm.subst_monus,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact coefficient_congr (fst_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _))

theorem kernel_lookup (N D i : PTm n) (hi : Γ ⊢[PRAAx] le i D) : Γ ⊢[PRAAx]
    entry (kernel N D) i ≐ sourceCoefficient N (monus D i) :=
  (sequence_decode rowBody (x := pairT N D) ((succ_monus_succ _ _).eqTrans hi)).eqTrans (row_at N D i)

theorem kernel_constant (N D : PTm n) : Γ ⊢[PRAAx] entry (kernel N D) D ≐ qone :=
  (kernel_lookup N D D (le_refl D)).eqTrans ((coefficient_congr (.eqRefl N) (monus_self D)).eqTrans (coefficient_zero N))

theorem kernel_positive (N D j : PTm n) (hj : Γ ⊢[PRAAx] le (succ j) D) : Γ ⊢[PRAAx]
    entry (kernel N D) (monus D (succ j)) ≐ qmul (parityPoint j) (point (succ j) N) :=
  (kernel_lookup N D _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
    ((coefficient_congr (.eqRefl N) (GaussianRationalMonicReconstruction.complement D (succ j) hj)).eqTrans (coefficient_succ N j))

theorem first_cauchy (N D e : PTm n) (he : Γ ⊢[PRAAx] le e (succ N)) : Γ ⊢[PRAAx]
    term (kernel N D) (polynomial N) D (succ N) e zero ≐ GaussianTranslatedNonconstant.recode (reader N e) :=
  (qmul_congr ((entry_congr (.eqRefl _) (monus_zero D)).eqTrans (kernel_constant N D))
    ((entry_congr (.eqRefl _) (congrMonus (.eqRefl _) (monus_zero e))).eqTrans (exponent_inside _ _ _ he).eqSymm)).eqTrans
      (GaussianRationalFiniteProduct.raw_one_left _)

theorem positive_cauchy (N D s j : PTm n) (hs : Γ ⊢[PRAAx] le (succ s) D)
    (hN : Γ ⊢[PRAAx] le (succ s) (succ N)) (hj : Γ ⊢[PRAAx] le j s) : Γ ⊢[PRAAx]
    term (kernel N D) (polynomial N) D (succ N) (succ s) (succ j) ≐
      GaussianGammaEulerHeadHarmonicNewton.powerTerm N s j :=
  qmul_congr (kernel_positive N D j (le_trans ((succ_monus_succ _ _).eqTrans hj) hs))
    ((entry_congr (.eqRefl _) (congrMonus (.eqRefl _) (succ_monus_succ s j))).eqTrans
      (exponent_inside _ _ _ (le_trans (GaussianRationalMonicReconstruction.monus_le_left _ _)
        (le_trans (le_succ_self s) hN))).eqSymm)

theorem shifted_cauchy_sum (N D s : PTm n) (hs : Γ ⊢[PRAAx] le (succ s) D)
    (hN : Γ ⊢[PRAAx] le (succ s) (succ N)) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum (shiftBody termBody) (succ s)
      (data (kernel N D) (polynomial N) D (succ N) (succ s)) ≐ GaussianGammaEulerHeadHarmonicNewton.powerSum N s := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift s)) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift s)) (succ (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hN.shift
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  rw [inst2_shiftBody]
  let Δ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift s) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h := (GaussianRationalLowCoefficientConvolution.term_at (Γ := Δ) (kernel (Syn.shift N) (Syn.shift D))
    (polynomial (Syn.shift N)) (Syn.shift D) (succ (Syn.shift N)) (succ (Syn.shift s)) (succ (var 0))).eqTrans
      ((positive_cauchy _ _ _ _ ds.wk ns.wk hi).eqTrans (GaussianGammaEulerHeadHarmonicNewton.power_term_at _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,subst_kernel,
    GaussianGammaEulerHeadPolynomial.subst_polynomial,GaussianGammaEulerHeadHarmonicNewton.subst_data,PTm.subst_succ] using h

theorem cauchy_split (N D s : PTm n) (hs : Γ ⊢[PRAAx] le (succ s) D)
    (hN : Γ ⊢[PRAAx] le (succ s) (succ N)) : Γ ⊢[PRAAx]
    cauchySum (kernel N D) (polynomial N) D (succ N) (succ s) ≐
      qadd (GaussianTranslatedNonconstant.recode (reader N (succ s))) (GaussianGammaEulerHeadHarmonicNewton.powerSum N s) :=
  (GaussianRationalFiniteSum.sum_shift_first termBody (succ s) _).eqTrans
    (qadd_congr ((GaussianRationalLowCoefficientConvolution.term_at _ _ _ _ _ _).eqTrans (first_cauchy _ _ _ hN))
      (shifted_cauchy_sum N D s hs hN))

theorem original_positive_Euler_product (N D s : PTm n) (hs : Γ ⊢[PRAAx] le (succ s) D)
    (hN : Γ ⊢[PRAAx] le (succ s) (succ N)) : Γ ⊢[PRAAx]
    exponentCoefficient (product (kernel N D) (polynomial N) D (succ N)) (D+succ N) (succ s) ≐
      exponentCoefficient (euler (polynomial N) (succ N)) (succ N) (succ s) :=
  (GaussianRationalLowCoefficientConvolution.product_exponent _ _ _ _ _ hs hN).eqTrans
    ((cauchy_split N D s hs hN).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianGammaEulerHeadHarmonicNewton.original_harmonic_Newton N s)).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
          ((GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _).eqTrans
            ((GaussianGammaEulerHeadNewton.scale_succ s _).eqSymm.eqTrans
              (GaussianRationalEulerCoefficients.euler_exponent _ _ _ hN).eqSymm)))))

theorem original_Euler_head_positive_logarithmic_kernel_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (succ (var 2)) (var 1) ⟶ le (succ (var 2)) (succ (var 0)) ⟶
      exponentCoefficient (product (kernel (var 0) (var 1)) (polynomial (var 0)) (var 1) (succ (var 0)))
        (var 1+succ (var 0)) (succ (var 2)) ≐
      exponentCoefficient (euler (polynomial (var 0)) (succ (var 0))) (succ (var 0)) (succ (var 2))) :=
  closeUniv 3 (.impI (.impI (original_positive_Euler_product _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadLogarithmicKernel

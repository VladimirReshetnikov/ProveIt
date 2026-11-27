import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianLagrangeInterpolation
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianInitialCoefficientBound
import IPRADerivations.Analysis.FiniteOperations.FiniteSums.GaussianFiniteSumL1Variation
import IPRADerivations.Analysis.Exponential.Polynomials.Coefficients.GaussianFiniteExponentialWeightedNorm

/-!
# A computed finite-grid gain for original polynomial coefficients

The gain is computed from the actual finite Lagrange inverse row, using
the existing numerator maximum. Actual finite-grid errors therefore bound
each original coefficient error with an explicit positive natural factor.
Both polynomials and every index remain internal; no inverse norm or
coefficient sensitivity estimate is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLagrangeCoefficientSensitivity

open_ipra
open GaussianLagrangeInterpolation (data observation cell cellBody coefficient original_coefficient cell_body_at)
open GaussianRationalLagrangeCardinals (inverseCoefficient)
open GaussianRationalFiniteGridIdentity (grid)
open GaussianRationalMetric (qsub)
open GaussianRationalL1 (qL1)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticBounds (natCode)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBody : PTm 2 := inverseCoefficient (grid (fstT (var 1))) (sndT (var 1)) (var 0)
def row (N e : PTm n) : PTm n := sequence rowBody (succ N) (pairT N e)
def rowBound (N e : PTm n) : PTm n := GaussianInitialCoefficientBound.initialBound (row N e) (succ N)
def gain (N e : PTm n) : PTm n := succ N*rowBound N e
def observationsClose (C D N E : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ rationalLE
    (qL1 (qsub (observation (Syn.shift C) (var 0)) (observation (Syn.shift D) (var 0)))) (Syn.shift E))

ipra_subst row
ipra_subst rowBound
ipra_subst gain
ipra_subst observationsClose [Syn.subst_shift, Syn.shift_subst]

theorem row_body_at (N e s : PTm n) : Γ ⊢[PRAAx] inst2 rowBody s (pairT N e) ≐ inverseCoefficient (grid N) e s := by
  simp only [rowBody,inst2,GaussianRationalLagrangeCardinals.subst_inverseCoefficient,
    GaussianRationalFiniteGridIdentity.subst_grid,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have gridEq : Γ ⊢[PRAAx] grid (fstT (pairT N e)) ≐ grid N := by
    ipra_congr (grid (var 0) : PTm 1) with [fst_pair N e]
  exact GaussianRationalLagrangeCardinals.inverse_coefficient_congr
    gridEq (snd_pair _ _) (.eqRefl _)

theorem row_lookup (N e s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ N)) : Γ ⊢[PRAAx]
    entry (row N e) s ≐ inverseCoefficient (grid N) e s :=
  (sequence_decode rowBody hs).eqTrans (row_body_at N e s)

theorem row_bound (N e s : PTm n) (hs : Γ ⊢[PRAAx] le s N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (inverseCoefficient (grid N) e s)) (natCode (rowBound N e)) :=
  RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr (row_lookup N e s ((succ_monus_succ _ _).eqTrans hs)))
    (.eqRefl _) (GaussianInitialCoefficientBound.coefficient_bound (row N e) (succ N) s ((succ_monus_succ _ _).eqTrans hs))

theorem gain_positive (N e : PTm n) : Γ ⊢[PRAAx] le one (gain N e) :=
  GaussianRationalHorner.positive_product _ _ (zero_lt_succ N) (GaussianInitialCoefficientBound.initial_positive _ _)

theorem observation_at (C D N E s : PTm n) (h : Γ ⊢[PRAAx] observationsClose C D N E)
    (hs : Γ ⊢[PRAAx] le s N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (observation C s) (observation D s))) E := by
  have gate : Γ ⊢[PRAAx] le s N ⟶ rationalLE (qL1 (qsub (observation C s) (observation D s))) E := by
    simpa [observationsClose] using h.allE s
  exact .impE gate hs

theorem cell_error (C D N e E s : PTm n) (h : Γ ⊢[PRAAx] observationsClose C D N E)
    (hs : Γ ⊢[PRAAx] le s N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (cell C N e s) (cell D N e s))) (multiply (natCode (rowBound N e)) E) := by
  have code : Γ ⊢[PRAAx] qsub (cell C N e s) (cell D N e s) ≐
      qmul (inverseCoefficient (grid N) e s) (qsub (observation C s) (observation D s)) :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
      (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
        (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr code).eqSymm (.eqRefl _)
    (RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply _ _)
      (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ (GaussianRationalL1.qL1_nonnegative _)
        (GaussianRationalSyntheticBounds.natCode_nonnegative _) (row_bound N e s hs) (observation_at C D N E s h hs)))

theorem coefficient_error (C D N e E : PTm n) (h : Γ ⊢[PRAAx] observationsClose C D N E) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (coefficient C N e) (coefficient D N e))) (multiply (natCode (gain N e)) E) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] observationsClose (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift E) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianFiniteSumL1Variation.termsError cellBody cellBody (succ N) (data C N e) (data D N e)
      (multiply (natCode (rowBound N e)) E) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
    have term := RationalArgmin.rationalLE_congr
      (GaussianCoefficientL1.qL1_congr (GaussianRationalSyntheticDivision.qsub_congr
        (cell_body_at (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift e) (var 0))
        (cell_body_at (Syn.shift D) (Syn.shift N) (Syn.shift e) (var 0)))).eqSymm (.eqRefl _)
      (cell_error (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift e) (Syn.shift E) (var 0) hs.wk
        ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
    simpa only [Δ,Syn.shift,GaussianLagrangeInterpolation.subst_data,ConciseIPRA.PTm.subst_succ,
      RationalArithmetic.subst_multiply,GaussianRationalSyntheticBounds.subst_natCode,subst_rowBound] using term
  have scale : Γ ⊢[PRAAx] multiply (natCode (succ N)) (multiply (natCode (rowBound N e)) E) ≐
      multiply (natCode (gain N e)) E :=
    (RationalAlgebra.multiply_associative _ _ _).eqSymm.eqTrans
      (RationalAlgebra.multiply_congr (GaussianRationalSyntheticBounds.natCode_multiply _ _) (.eqRefl _))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) scale
    (GaussianFiniteSumL1Variation.sum_error cellBody cellBody _ _ _ _ terms)

theorem original_coefficient_error (C D N e E : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (he : Γ ⊢[PRAAx] le e N) (h : Γ ⊢[PRAAx] observationsClose C D N E) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (GaussianTranslatedNonconstant.recode (entry C (monus N e)))
      (GaussianTranslatedNonconstant.recode (entry D (monus N e))))) (multiply (natCode (gain N e)) E) :=
  RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr
    (GaussianRationalSyntheticDivision.qsub_congr (original_coefficient C N e hC he) (original_coefficient D N e hD he))).eqSymm
      (.eqRefl _) (coefficient_error C D N e E h)

theorem actual_finite_grid_coefficient_sensitivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (var 0) ≐ succ (var 2)) ⟶ (length (var 1) ≐ succ (var 2)) ⟶ le (var 3) (var 2) ⟶
      observationsClose (var 0) (var 1) (var 2) (var 4) ⟶
      rationalLE (qL1 (qsub (GaussianTranslatedNonconstant.recode (entry (var 0) (monus (var 2) (var 3))))
        (GaussianTranslatedNonconstant.recode (entry (var 1) (monus (var 2) (var 3))))))
          (multiply (natCode (gain (var 2) (var 3))) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (original_coefficient_error _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianLagrangeCoefficientSensitivity

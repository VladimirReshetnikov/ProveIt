import IPRADerivations.Analysis.GaussianPolynomialFirstCoefficients
import IPRADerivations.Analysis.GaussianRationalPowerExpansion

/-!
# Actual low coefficients when one convolution factor has degree at most one

The original coefficient-after theorem zeros the early prefix; three
original coefficient-successor equations then isolate the two nonzero
quadratic cells of a degree-one right factor. This removes the degree-two
guard on that factor without postulating a convolution identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialLinearFactorCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qadd)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalPolynomialProduct (product coefficient contribution coefficient_succ coefficient_zero contribution_inside contribution_outside)
open GaussianRationalLinearProduct (padded_inside padded_congr)
open GaussianRationalMonicReduction (singleton)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem first_row (P Q M k : PTm n) (hk : Γ ⊢[PRAAx] le k M) : Γ ⊢[PRAAx]
    coefficient P Q M one k ≐ qmul (entry P zero) (entry Q k) := by
  have row := (contribution_inside (Γ := Γ) P Q M k zero (zero_le k)).eqTrans
    (qmul_congr (.eqRefl _)
      ((padded_congr (.eqRefl _) (.eqRefl _) (monus_zero k)).eqTrans
        (padded_inside Q (succ M) k ((succ_monus_succ _ _).eqTrans hk))))
  exact (coefficient_succ P Q M zero k).eqTrans
    ((qadd_congr (coefficient_zero P Q M k) row).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem constant_left_value (a Q M k : PTm n) (hk : Γ ⊢[PRAAx] le k M) : Γ ⊢[PRAAx]
    entry (product (singleton a) Q zero M) k ≐ qmul a (entry Q k) :=
  (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _
    (le_congr (.eqRefl _) (zero_add M).eqSymm hk)).eqTrans
      ((first_row (singleton a) Q M k hk).eqTrans
        (qmul_congr (GaussianRationalMonicReduction.singleton_lookup a) (.eqRefl _)))

theorem bilinear_leading (P Q : PTm n) : Γ ⊢[PRAAx]
    entry (product P Q one one) zero ≐ qmul (entry P zero) (entry Q zero) :=
  (GaussianRationalPolynomialProduct.product_lookup P Q one one zero (zero_le _)).eqTrans
    ((coefficient_succ P Q one one zero).eqTrans
      ((qadd_congr (first_row P Q one zero (zero_le one))
        (contribution_outside P Q one zero one (le_refl one))).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _))))

theorem successor_difference (r : PTm n) : Γ ⊢[PRAAx] LeanProofs.IPRA.PTm.monus (succ r) r ≐ one :=
  (GaussianRationalPowerExpansion.remaining_before r r (le_refl r)).eqTrans (congrSucc (monus_self r))

theorem quadratic_first_row (P Q r : PTm n) : Γ ⊢[PRAAx]
    contribution P Q one (succ r) r ≐ qmul (entry P r) (entry Q one) :=
  (contribution_inside P Q one (succ r) r (le_succ_self r)).eqTrans
    (qmul_congr (.eqRefl _) ((padded_congr (.eqRefl _) (.eqRefl _) (successor_difference r)).eqTrans
      (padded_inside Q two one (le_refl two))))

theorem quadratic_second_row (P Q r : PTm n) : Γ ⊢[PRAAx]
    contribution P Q one (succ r) (succ r) ≐ qmul (entry P (succ r)) (entry Q zero) :=
  (contribution_inside P Q one (succ r) (succ r) (le_refl _)).eqTrans
    (qmul_congr (.eqRefl _) ((padded_congr (.eqRefl _) (.eqRefl _) (monus_self (succ r))).eqTrans
      (padded_inside Q two zero (le_succ_self one))))

/-- Literal quadratic coefficient for a degree-one right factor; the
left degree is r+2, so no hidden degree-two guard on the right appears. -/
theorem quadratic_value (P Q r : PTm n) : Γ ⊢[PRAAx]
    entry (product P Q (succ (succ r)) one) (succ r) ≐
      qadd (qmul (entry P r) (entry Q one)) (qmul (entry P (succ r)) (entry Q zero)) := by
  have initial := GaussianRationalPolynomialProduct.coefficient_after (Γ := Γ) P Q one r (succ r)
    (le_of_eq_add (d := zero) (by ipra_ring))
  have first := (coefficient_succ P Q one r (succ r)).eqTrans
    ((qadd_congr initial (quadratic_first_row P Q r)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))
  have second := (coefficient_succ P Q one (succ r) (succ r)).eqTrans
    (qadd_congr first (quadratic_second_row P Q r))
  exact (GaussianRationalPolynomialProduct.product_lookup P Q (succ (succ r)) one (succ r)
    (le_of_eq_add (d := two) (by ipra_ring))).eqTrans
      ((coefficient_succ P Q one (succ (succ r)) (succ r)).eqTrans
        ((qadd_congr second (contribution_outside P Q one (succ r) (succ (succ r)) (le_refl _))).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qadd_canonical _ _))))

theorem actual_linear_right_factor_quadratic_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (entry (product (var 0) (var 1) (succ (succ (var 2))) one) (succ (var 2)) ≐
      qadd (qmul (entry (var 0) (var 2)) (entry (var 1) one))
        (qmul (entry (var 0) (succ (var 2))) (entry (var 1) zero))) :=
  closeUniv 3 (quadratic_value _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialLinearFactorCoefficients

import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianPolynomialNormBuffers
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Coefficient differences of sums and scalar multiples

These laws compare the stored output buffers of the existing polynomial
operations. They also apply to raw coefficients and empty buffers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialCoefficientDifferences

open_ipra
open GaussianRationalHorner
  (qadd qmul qzero represents qadd_represents represents_congr canonical_unique)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalL1 (qL1 rawGaussian rawDen raw_represents)
open GaussianRationalSyntheticDivision
  (rescale_to remainingDen remaining_den_positive qmul_congr qsub_congr qadd_congr qmul_zero_right qzero_add)
open GaussianCoefficientL1 (coefficientNorm subCoefficients sub_lookup)
open GaussianRationalPolynomialBuffers (added added_length added_lookup subst_added)
open GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup subst_scaled)
open GaussianPolynomialNormBuffers (norm_entries norm_added norm_scaled)
open GaussianRationalSumSegments (entriesEqual)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add multiply)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem sub_length (A B N : PTm n) : Γ ⊢[PRAAx] length (subCoefficients A B N) ≐ N :=
  GaussianCoefficientL1.zip_length GaussianCoefficientL1.subF A B N

/-- The four independently denominated values are put over the same
positive denominator before the literal normalized equality is derived. -/
theorem scalar_sum_difference (a b c d : PTm n) : Γ ⊢[PRAAx]
    qsub (qadd a c) (qadd b d) ≐ qadd (qsub a b) (qsub c d) := by
  let E := remainingDen a b c d
  have positive := remaining_den_positive (Γ := Γ) a b c d
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b*rawDen c*rawDen d) E
    (raw_represents (Γ := Γ) a) (by unfold E remainingDen; ipra_ring)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a*rawDen c*rawDen d) E
    (raw_represents (Γ := Γ) b) (by unfold E remainingDen; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (rawDen a*rawDen b*rawDen d) E
    (raw_represents (Γ := Γ) c) (by unfold E remainingDen; ipra_ring)
  have hd := rescale_to d (rawGaussian d) (rawDen d) (rawDen a*rawDen b*rawDen c) E
    (raw_represents (Γ := Γ) d) (by unfold E remainingDen; ipra_ring)
  have lhs := qsub_represents _ _ _ _ _ positive
    (qadd_represents _ _ _ _ _ positive ha hc) (qadd_represents _ _ _ _ _ positive hb hd)
  have rhs := qadd_represents _ _ _ _ _ positive
    (qsub_represents _ _ _ _ _ positive ha hb) (qsub_represents _ _ _ _ _ positive hc hd)
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (GaussianRationalHorner.qadd_canonical _ _) positive (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

theorem scalar_scaled_difference (z a b : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul z a) (qmul z b) ≐ qmul z (qsub a b) := by
  have zero := (qmul_congr (GaussianCoefficientNormOrder.qsub_self (Γ := Γ) z) (.eqRefl a)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_left a)
  exact (GaussianRationalPowerDifference.product_difference z z a b).eqTrans
    ((qadd_congr zero (.eqRefl _)).eqTrans (qzero_add _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem sum_difference_at (A B C D N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (subCoefficients (added A C N) (added B D N) N) i ≐
      entry (added (subCoefficients A B N) (subCoefficients C D N) N) i := by
  exact (sub_lookup _ _ _ _ hi).eqTrans
    ((qsub_congr (added_lookup _ _ _ _ hi) (added_lookup _ _ _ _ hi)).eqTrans
      ((scalar_sum_difference _ _ _ _).eqTrans
        ((added_lookup _ _ _ _ hi).eqTrans (qadd_congr (sub_lookup _ _ _ _ hi) (sub_lookup _ _ _ _ hi))).eqSymm))

theorem sum_difference_norm (A B C D N : PTm n) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (added A C N) (added B D N) N))
      (add (coefficientNorm (subCoefficients A B N)) (coefficientNorm (subCoefficients C D N))) := by
  have entries : Γ ⊢[PRAAx] entriesEqual (subCoefficients (added A C N) (added B D N) N)
      (added (subCoefficients A B N) (subCoefficients C D N) N) N := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift, GaussianCoefficientL1.subst_subCoefficients, subst_added] using
      (sum_difference_at (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0)
        (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _))
  exact rationalLE_congr (norm_entries _ _ _ (sub_length _ _ _) (added_length _ _ _) entries).eqSymm
    (.eqRefl _) (norm_added _ _ _ (sub_length _ _ _) (sub_length _ _ _))

theorem scaled_difference_at (A B N z i : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ N)
    (hB : Γ ⊢[PRAAx] length B ≐ N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (subCoefficients (scaled A z) (scaled B z) N) i ≐ entry (scaled (subCoefficients A B N) z) i := by
  have ha := lt_congr (.eqRefl _) hA.eqSymm hi
  have hb := lt_congr (.eqRefl _) hB.eqSymm hi
  have hs := lt_congr (.eqRefl _) (sub_length A B N).eqSymm hi
  exact (sub_lookup _ _ _ _ hi).eqTrans
    ((qsub_congr (scaled_lookup _ _ _ ha) (scaled_lookup _ _ _ hb)).eqTrans
      ((scalar_scaled_difference _ _ _).eqTrans
        ((scaled_lookup _ _ _ hs).eqTrans (qmul_congr (.eqRefl _) (sub_lookup _ _ _ _ hi))).eqSymm))

theorem scaled_difference_norm (A B N z : PTm n) (hA : Γ ⊢[PRAAx] length A ≐ N)
    (hB : Γ ⊢[PRAAx] length B ≐ N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (scaled A z) (scaled B z) N))
      (multiply (qL1 z) (coefficientNorm (subCoefficients A B N))) := by
  have entries : Γ ⊢[PRAAx] entriesEqual (subCoefficients (scaled A z) (scaled B z) N)
      (scaled (subCoefficients A B N) z) N := by
    refine .allI (.impI ?_)
    have ha : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift A) ≐ Syn.shift N := by
      simpa [Fm.shift, Syn.shift] using hA.shift
    have hb : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift B) ≐ Syn.shift N := by
      simpa [Fm.shift, Syn.shift] using hB.shift
    simpa only [Syn.shift, GaussianCoefficientL1.subst_subCoefficients, subst_scaled] using
      (scaled_difference_at (Syn.shift A) (Syn.shift B) (Syn.shift N) (Syn.shift z) (var 0)
        ha.wk hb.wk (Prf.hyp0 : lt (var 0) (Syn.shift N) :: Γ.map Fm.shift ⊢[PRAAx] _))
  exact rationalLE_congr
    (norm_entries _ _ _ (sub_length _ _ _) ((scaled_length _ _).eqTrans (sub_length _ _ _)) entries).eqSymm
    (.eqRefl _) (norm_scaled _ _)

theorem actual_sum_difference_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rationalLE
      (coefficientNorm (subCoefficients (added (var 0) (var 2) (var 4)) (added (var 1) (var 3) (var 4)) (var 4)))
      (add (coefficientNorm (subCoefficients (var 0) (var 1) (var 4)))
        (coefficientNorm (subCoefficients (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (sum_difference_norm _ _ _ _ _)

theorem actual_scaled_difference_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (var 0) ≐ var 2 ⋏ length (var 1) ≐ var 2) ⟶
      rationalLE (coefficientNorm (subCoefficients (scaled (var 0) (var 3)) (scaled (var 1) (var 3)) (var 2)))
        (multiply (qL1 (var 3)) (coefficientNorm (subCoefficients (var 0) (var 1) (var 2))))) :=
  closeUniv 4 (.impI (scaled_difference_norm _ _ _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialCoefficientDifferences

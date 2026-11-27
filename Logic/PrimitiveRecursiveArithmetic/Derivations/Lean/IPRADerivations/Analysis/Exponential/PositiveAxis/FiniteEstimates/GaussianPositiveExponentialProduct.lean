import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.Exponential.FiniteSeries.Products.GaussianScalarExponentialProductLowDegrees

/-!
# The positive high part of the original rectangular exponential product

Every stored scalar coefficient, guarded convolution contribution and
actual high-part summand is nonnegative on the nonnegative real axis.
The original exact rectangular split therefore gives submultiplicativity
of the SAME finite scalar exponential at every numerical cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialProduct

open_ipra
open GaussianPositiveRealArithmetic
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianScalarExponentialProductLowDegrees (buffer product highPart evaluationData)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem positive_coefficient (q e : PTm n) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive (GaussianScalarExponentialDiagonal.coefficient q e) :=
  positive_multiply _ _ (positive_inverse_factorial e) (positive_power q e hq)

theorem positive_scalar_sum (q K : PTm n) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive (scalarSum q K) := by
  apply positive_sum
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) := by simpa [Fm.shift,Syn.shift] using hq.shift
  simpa only [positiveTerms,GaussianRationalPolynomialExponential.scalar_body_at,GaussianScalarExponentialDiagonal.coefficient] using
    positive_coefficient (Syn.shift q) (var 0) hs.wk

theorem positive_buffer_entry (q K i : PTm n) (hq : Γ ⊢[PRAAx] positive q)
    (hi : Γ ⊢[PRAAx] le i K) : Γ ⊢[PRAAx] positive (entry (buffer q K) i) :=
  positive_congr (GaussianScalarExponentialProductLowDegrees.descending_at q K i hi).eqSymm
    (positive_coefficient q _ hq)

theorem positive_padded_buffer (q K i : PTm n) (hq : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] positive (GaussianRationalLinearProduct.padded (buffer q K) (succ K) i) := by
  refine .orE (lt_or_le i (succ K)) ?_ ?_
  · exact positive_congr (GaussianRationalLinearProduct.padded_inside _ _ _ Prf.hyp0).eqSymm
      (positive_buffer_entry q K i hq.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0))
  · exact positive_congr (GaussianRationalLinearProduct.padded_outside _ _ _ Prf.hyp0).eqSymm positive_zero

theorem positive_contribution (u v K k i : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (hi : Γ ⊢[PRAAx] le i K) : Γ ⊢[PRAAx]
    positive (GaussianRationalPolynomialProduct.contribution (buffer u K) (buffer v K) K k i) := by
  refine .orE (lt_or_le k i) ?_ ?_
  · exact positive_congr (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm positive_zero
  · exact positive_congr (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm
      (positive_multiply _ _ (positive_buffer_entry u K i hu.wk hi.wk) (positive_padded_buffer v K _ hv.wk))

theorem positive_product_coefficient (u v K k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) : Γ ⊢[PRAAx]
    positive (GaussianRationalPolynomialProduct.coefficient (buffer u K) (buffer v K) K (succ K) k) := by
  apply positive_sum
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift K)) :: Γ.map Fm.shift
  have us : Δ ⊢[PRAAx] positive (Syn.shift u) := by simpa [Δ,Fm.shift,Syn.shift] using hu.shift.wk
  have vs : Δ ⊢[PRAAx] positive (Syn.shift v) := by simpa [Δ,Fm.shift,Syn.shift] using hv.shift.wk
  have p := positive_contribution (Syn.shift u) (Syn.shift v) (Syn.shift K) (Syn.shift k) (var 0) us vs
    ((succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift K))))
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data,GaussianScalarExponentialProductLowDegrees.subst_buffer,
    ConciseIPRA.PTm.subst_succ] using positive_congr (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqSymm p

theorem positive_product_entry (u v K k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (hk : Γ ⊢[PRAAx] le k (K+K)) :
    Γ ⊢[PRAAx] positive (entry (product u v K) k) :=
  positive_congr (GaussianRationalPolynomialProduct.product_lookup _ _ _ _ _ hk).eqSymm
    (positive_product_coefficient u v K k hu hv)

theorem positive_product_exponent (u v K e : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (he : Γ ⊢[PRAAx] le e (K+K)) :
    Γ ⊢[PRAAx] positive (exponentCoefficient (product u v K) (K+K) e) :=
  positive_congr (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ he).eqSymm
    (positive_product_entry u v K _ hu hv (GaussianRationalMonicReconstruction.monus_le_left _ _))

theorem positive_high_part (u v K : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) : Γ ⊢[PRAAx] positive (highPart u v K) := by
  apply positive_sum
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have us : Δ ⊢[PRAAx] positive (Syn.shift u) := by simpa [Δ,Fm.shift,Syn.shift] using hu.shift.wk
  have vs : Δ ⊢[PRAAx] positive (Syn.shift v) := by simpa [Δ,Fm.shift,Syn.shift] using hv.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) (Syn.shift K) := Prf.hyp0
  have he : Δ ⊢[PRAAx] le (succ (Syn.shift K)+var 0) (Syn.shift K+Syn.shift K) :=
    le_congr (by ipra_ring) (.eqRefl _) (add_le_add_right (Syn.shift K) hi)
  have p := positive_product_exponent (Syn.shift u) (Syn.shift v) (Syn.shift K) _ us vs he
  simpa only [Δ,Syn.shift,GaussianScalarExponentialProductLowDegrees.subst_evaluationData,subst_pairT,
    ConciseIPRA.PTm.subst_succ] using positive_congr
      (GaussianScalarExponentialProductLowDegrees.high_part_term _ _ _ _ hi).eqSymm p

theorem scalar_le_add (a b : PTm n) (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a)
    (hb : Γ ⊢[PRAAx] sign b) : Γ ⊢[PRAAx] rationalLE a (RationalArithmetic.add a b) := by
  have lo : Γ ⊢[PRAAx] rationalLE (GaussianRationalSyntheticBounds.natCode zero) b :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ one (RationalSupMetric.denominatorOf b)
      (le_refl one) (RationalArgmin.denominator_positive b)
      (GaussianRationalSyntheticBounds.natCode_represents zero) (natural_representation b hb)
      (le_congr (by ipra_ring) (by ipra_ring) (zero_le (numerator b)))
  exact RationalArgmin.rationalLE_congr (GaussianRationalLinearProduct.scalar_add_zero a ha) (.eqRefl _)
    (GaussianRationalSyntheticBounds.add_monotone a a _ b (RationalArgmin.reflexive a) lo)

theorem real_product (q r : PTm n) (hr : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis r) : Γ ⊢[PRAAx]
    fstT (qmul q r) ≐ RationalArithmetic.multiply (fstT q) (fstT r) := by
  have e := (GaussianRationalSyntheticCoefficientValues.qmul_recode_right (Γ := Γ) q r).eqSymm.eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (RationalGaussianEmbedding.axis_roundtrip r hr))
  exact (congrFst e).eqTrans (RationalGaussianRealPart.real_product q (fstT r))

theorem scalar_sum_submultiplicative (u v K : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) : Γ ⊢[PRAAx]
    rationalLE (fstT (scalarSum (qadd u v) K))
      (RationalArithmetic.multiply (fstT (scalarSum u K)) (fstT (scalarSum v K))) := by
  have h := scalar_le_add (fstT (scalarSum (qadd u v) K)) (fstT (highPart u v K))
    (GaussianRationalFiniteSum.sum_canonical scalarBody (succ K) _).andE₂.andE₁ (positive_high_part u v K hu hv).andE₂
  have e := (congrFst (GaussianScalarExponentialProductLowDegrees.exact_rectangular_product_split (Γ := Γ) u v K)).eqTrans
    (RationalGaussianRealPart.real_add _ _)
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (e.eqSymm.eqTrans (real_product _ _ (positive_scalar_sum v K hv).andE₁)) h

theorem original_positive_high_part_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (positive (var 0) ⟶ positive (var 1) ⟶ positive (highPart (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (positive_high_part _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_positive_scalar_exponential_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (positive (var 0) ⟶ positive (var 1) ⟶ rationalLE (fstT (scalarSum (qadd (var 0) (var 1)) (var 2)))
      (RationalArithmetic.multiply (fstT (scalarSum (var 0) (var 2))) (fstT (scalarSum (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (scalar_sum_submultiplicative _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialProduct

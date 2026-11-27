import IPRADerivations.Analysis.Exponential.PositiveAxis.FiniteEstimates.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.Exponential.FiniteSeries.ScalarSeries.GaussianScalarExponentialOddTaylor
import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScale

/-!
# Finite positive lower bound for the original hyperbolic sine

The same even exponential cutoff on the two signed rational inputs
gives an exact odd Taylor sum. Its first term provides a rational lower
bound in the original Euclidean norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelSinhOddLower

open_ipra
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_numerator_norm)
open GaussianPositiveExponentialProduct (positive_coefficient scalar_le_add)
open GaussianPositiveRealArithmetic (positive positive_sum positiveTerms natural_representation)
open GaussianRationalHorner (qadd qmul qzero canonical canonical_unique represents_congr
  ofGaussian_represents positive_product scalar_congr)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr qzero_add)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_neg im_neg re_scale im_scale)
open GaussianScalarExponentialOddTaylor (oddSum oddBody odd_sum_succ scalarTerm)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalSupMetric (denominatorOf)
open GaussianPositiveExponentialTermBound renaming as_lower_bound → positive_real_lower

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem first_term (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] scalarTerm q one ≐ q := by
  have f : Γ ⊢[PRAAx] Products.fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))
  have inv : Γ ⊢[PRAAx] inverseFactorial (one : PTm n) ≐ qone :=
    GaussianIntegerFractionPowers.fraction_congr (.eqRefl _) f
  exact (qmul_congr inv (GaussianRationalPowerAlgebra.power_one q hq)).eqTrans
    (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq)

theorem odd_positive (q K : PTm n) (h : Γ ⊢[PRAAx] positive q) : Γ ⊢[PRAAx] positive (oddSum q K) := by
  apply positive_sum
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [positiveTerms,GaussianScalarExponentialOddTaylor.odd_body_at,scalarTerm,
    GaussianScalarExponentialDiagonal.coefficient] using positive_coefficient (Syn.shift q) (succ (two*var 0)) hs.wk

private def firstLaw (q K : PTm n) : Fm PTm n :=
  rationalLE (fstT q) (fstT (oddSum q (succ K)))

@[simp] private theorem subst_firstLaw {m : ℕ} (σ : Fin n → PTm m) (q K : PTm n) :
    (firstLaw q K).subst σ = firstLaw (Syn.subst σ q) (Syn.subst σ K) := by simp [firstLaw]

private theorem first_base (q : PTm n) (h : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] firstLaw q zero := by
  have i : Γ ⊢[PRAAx] succ (two*zero) ≐ (one : PTm n) := by ipra_ring
  have e : Γ ⊢[PRAAx] scalarTerm q (succ (two*zero)) ≐ scalarTerm q one := by
    simpa only [GaussianRationalPolynomialExponential.scalar_body_at,scalarTerm] using congrInst2 scalarBody i (.eqRefl q)
  have z : Γ ⊢[PRAAx] oddSum q zero ≐ qzero := GaussianRationalFiniteSum.sum_zero _ _
  have p := (odd_sum_succ q zero).eqTrans
    ((qadd_congr z (e.eqTrans (first_term q h))).eqTrans (qzero_add q h))
  exact rationalLE_congr (.eqRefl _) (congrFst p).eqSymm (RationalArgmin.reflexive _)

private theorem first_succ (q K : PTm n) (h : Γ ⊢[PRAAx] positive q) (ih : Γ ⊢[PRAAx] firstLaw q K) :
    Γ ⊢[PRAAx] firstLaw q (succ K) := by
  let j := succ (two*succ K)
  have step := (congrFst (odd_sum_succ (Γ := Γ) q (succ K))).eqTrans (RationalGaussianRealPart.real_add _ _)
  have nonneg : Γ ⊢[PRAAx] positive (scalarTerm q j) := positive_coefficient q j h
  have le := scalar_le_add (fstT (oddSum q (succ K))) (fstT (scalarTerm q j))
    (GaussianScalarExponentialOddTaylor.odd_sum_canonical (Γ := Γ) q (succ K)).andE₂.andE₁ nonneg.andE₂
  exact transitive ih (rationalLE_congr (.eqRefl _) step.eqSymm le)

theorem odd_first_order (q K : PTm n) (hq : Γ ⊢[PRAAx] canonical q) (h : Γ ⊢[PRAAx] positive q) :
    Γ ⊢[PRAAx] rationalLE (fstT q) (fstT (oddSum q (succ K))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift q) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (firstLaw (Syn.shift q) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_firstLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using first_base q hq
    · simp only [subst_firstLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact first_succ _ _ hs.wk Prf.hyp0
  change Γ ⊢[PRAAx] firstLaw q K
  simpa only [subst_firstLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

theorem odd_lower (A B K E D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint E D)) (fstT (radiusPoint A B))) :
    Γ ⊢[PRAAx] lower (oddSum (radiusPoint A B) (succ K)) E D := by
  let q := radiusPoint A B
  have hp : Γ ⊢[PRAAx] positive q := GaussianPositiveExponentialTermBound.actual_positive_fraction A B hB
  exact positive_real_lower _ _ _ (odd_positive q _ hp) (GaussianScalarExponentialOddTaylor.odd_sum_canonical _ _) hD
    (transitive h (odd_first_order q K (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hp))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelSinhOddLower

import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalReciprocal
import IPRADerivations.Analysis.Names.Rates.GaussianRadiusBudget
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalSyntheticBounds
import IPRADerivations.Analysis.Polynomials.Horner.GaussianReciprocalHorner

/-!
# Radius of an actual monic polynomial with small residual

The intended source04 estimate is derived from the actual rational coefficient
list and Horner residual. Exact reciprocal-tail bounds retain the Euclidean
constant and use a finite geometric sum, uniformly in the internal degree.
No descent contract or desired root-radius bound is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianMonicResidualRadius

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (qone reciprocal power normLower bound_congr bounded_product bounded_sum bounded_difference)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qadd qmul qzero evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1 rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (coefficientBounds natCode coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRadiusBudget (radius geometric)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (tail tail_zero tail_succ subst_tail)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The genuine original coefficient L1 bound implies its Euclidean bound
without changing the coefficient constant. -/
theorem bounded_of_l1 (q A : PTm n)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qL1 q) (natCode A)) : Γ ⊢[PRAAx]
    bounded q A one := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianRationalL1.qL1_represents (Γ := Γ) q (rawGaussian q) (rawDen q)
      (raw_den_positive q) (raw_represents q))
    (GaussianRationalSyntheticBounds.natCode_represents A) h
  have linear : Γ ⊢[PRAAx] le (GaussianL1.norm1 (rawGaussian q)) (A*rawDen q) :=
    le_congr (one_mul _) (.eqRefl _) raw
  have square := le_mul_mono linear linear
  have euclidean := le_trans (GaussianL1.normSq_le_norm1_square (rawGaussian q)) square
  apply (GaussianRationalMetric.bounded_iff _ _ _ _ _ (raw_den_positive q) (le_refl _) (raw_represents q)).iffMpr
  exact le_congr (by ipra_ring) (by ipra_ring) euclidean

alias monus_le_left := Common.monus_le_self

theorem coefficient_euclidean (C N A i : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] bounded (entry C i) A one :=
  bounded_of_l1 _ _ (coefficient_at C A i hC
    (le_congr (succ_eq_add_one i).eqSymm
      ((succ_eq_add_one N).eqSymm.eqTrans hLen.eqSymm) (add_le_add_right one hi)))

/-- Positive common factors in the radius fraction may be canceled. The
actual point's two independent component denominators remain untouched. -/
theorem bounded_cancel (q A B E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] bounded q (A*E) (B*E)) : Γ ⊢[PRAAx] bounded q A B := by
  have raw := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _
    (raw_den_positive q) (GaussianRationalHorner.positive_product _ _ hB hE) (raw_represents q) h
  have scaled : Γ ⊢[PRAAx] le ((E*E)*((B*B)*normSq (rawGaussian q)))
      ((E*E)*((A*A)*(rawDen q*rawDen q))) := le_congr (by ipra_ring) (by ipra_ring) raw
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (raw_den_positive q) hB (raw_represents q)
    (RationalValueBounds.positive_cancel (GaussianRationalHorner.positive_product _ _ hE hE) scaled)

theorem bounded_difference_same_den (q r A C D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] bounded q A D) (hr : Γ ⊢[PRAAx] bounded r C D) : Γ ⊢[PRAAx]
    bounded (GaussianRationalMetric.qsub q r) (A+C) D :=
  bounded_cancel _ _ _ _ hD hD
    (bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (bounded_difference _ _ _ _ _ _ hD hD hq hr))

theorem zero_bounded (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    bounded (qzero : PTm n) A B := by
  apply (GaussianRationalMetric.bounded_iff qzero ComplexLogarithmRemainder.zeroCode one A B
    (le_refl _) hB (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))).iffMpr
  exact le_congr (by
    have h := ComplexLogarithmRemainder.normSq_zero (Γ := Γ) (n := n)
    exact ((congrMul (.eqRefl _) h).eqTrans (mul_zero _)).eqSymm) (.eqRefl _) (zero_le _)

/-- An actual bound on the canonical point one yields the unsquared
fraction inequality, including a zero numerator. -/
theorem qone_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] bounded (qone : PTm n) A B) : Γ ⊢[PRAAx] le B A := by
  have raw := GaussianRationalMetric.bounded_to_cleared qone ComplexLogarithmRemainder.oneCode one A B
    (le_refl _) hB (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _)) h
  apply nat_sqrt_mono
  exact le_congr ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
    (by ipra_ring) raw

theorem tail_bound_step (C w N A k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hw : Γ ⊢[PRAAx] bounded w one (radius A))
    (ih : Γ ⊢[PRAAx] bounded (tail C w N k) (A*geometric A k) (pw (radius A) k)) :
    Γ ⊢[PRAAx] bounded (tail C w N (succ k)) (A*geometric A (succ k)) (pw (radius A) (succ k)) := by
  have positive := GaussianPolynomialPerturbation.power_positive (Γ := Γ) (radius A) k
    (GaussianRadiusBudget.radius_positive A)
  have sum := bounded_sum _ _ _ _ _ _ positive (le_refl _)
    ih (coefficient_euclidean C N A (monus N k) hLen hC (monus_le_left N k))
  have product := bounded_product _ _ _ _ _ _ (GaussianRadiusBudget.radius_positive A)
    (GaussianRationalHorner.positive_product _ _ positive (le_refl _)) hw sum
  apply bound_congr (tail_succ C w N k).eqSymm ?_ ?_ product
  · have g := natEq (GaussianRadiusBudget.geometric_succ (Γ := Γ) A k)
    apply deriveNat
    ipra_simps
    rw [g]
    ring
  · exact (show Γ ⊢[PRAAx] radius A*(pw (radius A) k*one) ≐ pw (radius A) k*radius A from by ipra_ring).eqTrans
      (pw_succ _ _).eqSymm

/-- The actual backwards coefficient tail satisfies the exact finite
geometric budget. Quantifier-free induction ranges over its runtime length;
every coefficient bound is obtained from the original input list. -/
theorem tail_bound (C w N A k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hw : Γ ⊢[PRAAx] bounded w one (radius A)) : Γ ⊢[PRAAx]
    bounded (tail C w N k) (A*geometric A k) (pw (radius A) k) := by
  have lenShift : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hLen.shift
  have cShift : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift A) := by
    simpa only [Fm.shift,GaussianRationalSyntheticBounds.subst_coefficientBounds,Syn.shift] using hC.shift
  have wShift : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) one (radius (Syn.shift A)) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,GaussianRadiusBudget.subst_radius,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hw.shift
  have all : Γ ⊢[PRAAx] .all (bounded (tail (Syn.shift C) (Syn.shift w) (Syn.shift N) (var 0))
      (Syn.shift A*geometric (Syn.shift A) (var 0)) (pw (radius (Syn.shift A)) (var 0))) := by
    ipra_qfind (le_QF _ _) [GaussianRationalMetric.subst_bounded, subst_tail, GaussianRadiusBudget.subst_geometric,
        GaussianRadiusBudget.subst_radius, subst_ap2]
    · exact bound_congr (tail_zero C w N).eqSymm (.eqRefl _) (.eqRefl _)
        (zero_bounded _ _ (GaussianPolynomialPerturbation.power_positive _ _ (GaussianRadiusBudget.radius_positive A)))
    · exact tail_bound_step _ _ _ _ _ lenShift.wk cShift.wk wShift.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded,subst_tail,PTm.subst_mul,
    GaussianRadiusBudget.subst_geometric,GaussianRadiusBudget.subst_radius,subst_ap2,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

/-- The monic reciprocal-Horner identity and the genuine residual bound
contradict the strict finite geometric budget at every outside point. -/
theorem outside_impossible (C z N A : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate C z) one one)
    (hOutside : Γ ⊢[PRAAx] normLower z (radius A)) : Γ ⊢[PRAAx] .bot := by
  have hR : Γ ⊢[PRAAx] le one (radius A) := le_trans hA (le_add_right A two)
  have positive := GaussianPolynomialPerturbation.power_positive (Γ := Γ) (radius A) N hR
  have hInv := GaussianRationalReciprocal.inverse_bound z (radius A) hR hOutside
  have hPower := GaussianRationalReciprocal.reciprocal_power_bound z (radius A) N hR hOutside
  have hProduct := bounded_product _ _ _ _ _ _ (le_refl _) positive hResidual hPower
  have productBound : Γ ⊢[PRAAx]
      bounded (qmul (evaluate C z) (power (reciprocal z) N)) one (pw (radius A) N) :=
    bound_congr (.eqRefl _) (one_mul one) (one_mul _) hProduct
  have tailBound := tail_bound C (reciprocal z) N A N hLen hC hInv
  have difference := bounded_difference_same_den _ _ _ _ _ positive productBound tailBound
  have actualOne := GaussianReciprocalHorner.isolated_one C z (reciprocal z) N hLen hMonic
    (GaussianRationalReciprocal.reciprocal_identity z (GaussianRationalReciprocal.norm_positive z (radius A) hR hOutside))
  have oneBound : Γ ⊢[PRAAx] bounded qone (GaussianRadiusBudget.numerator A N) (pw (radius A) N) :=
    bound_congr actualOne (add_comm _ _) (.eqRefl _) difference
  exact le_lt_absurd _ (qone_bound _ _ positive oneBound) (GaussianRadiusBudget.strict_budget A N hN)

/-- Source04's monic residual-radius estimate on actual original rational
coefficients and points. Both the degree and all input codes are internal. -/
theorem residual_radius (C z N A : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate C z) one one) :
    Γ ⊢[PRAAx] bounded z (A+two) one := by
  refine .orE (RationalArgmin.total (qnormSq z) (squaredTolerance (radius A) one)) Prf.hyp0 ?_
  exact .botE _ (outside_impossible C z N A hN.wk hA.wk hLen.wk hMonic.wk hC.wk hResidual.wk Prf.hyp0)

theorem l1_euclidean_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (RationalArgmin.rationalLE (qL1 (var 0)) (natCode (var 1)) ⟶ bounded (var 0) (var 1) one) :=
  closeUniv 2 (.impI (bounded_of_l1 _ _ Prf.hyp0))

theorem reciprocal_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (var 0) ≐ succ (var 2)) ⟶ coefficientBounds (var 0) (var 3) ⟶
      bounded (var 1) one (radius (var 3)) ⟶
        bounded (tail (var 0) (var 1) (var 2) (var 4))
          (var 3*geometric (var 3) (var 4)) (pw (radius (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (tail_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem monic_outside_impossible_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ normLower (var 1) (radius (var 3)) ⟶ .bot) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (outside_impossible _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))))

theorem monic_residual_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ bounded (var 1) (var 3+two) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (residual_radius _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianMonicResidualRadius

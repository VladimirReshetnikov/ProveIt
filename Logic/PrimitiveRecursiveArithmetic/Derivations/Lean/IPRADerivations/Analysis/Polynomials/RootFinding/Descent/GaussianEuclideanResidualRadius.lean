import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicResidualRadius

/-!
# The exact monic residual radius from original Euclidean coefficient bounds

Every coefficient comparison is an original rational squared-norm comparison
with A². The actual reciprocal-Horner tail has budget A G_k/R^k for R=A+2,
proved by quantifier-free induction, without converting to L1 or enlarging A.
The original residual bound then contradicts the strict geometric gap at an
outside point. All degrees, codes, coefficients and indices remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (qone reciprocal power normLower bound_congr bounded_product bounded_sum)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianMonicResidualRadius
  (monus_le_left zero_bounded bounded_difference_same_den qone_bound)
open LeanProofs.IPRA.Analysis.GaussianRadiusBudget (radius geometric)
open LeanProofs.IPRA.Analysis.GaussianReciprocalHorner (tail tail_zero tail_succ subst_tail)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Every stored original coefficient has its actual Euclidean norm at
most A. The two scalar component denominators remain independently decoded. -/
def coefficientBounds (C A : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift C)) ⟶ bounded (entry (Syn.shift C) (var 0)) (Syn.shift A) one)

ipra_subst coefficientBounds [Fm.subst_all, Fm.subst_imp, subst_lt, subst_length,
    GaussianRationalMetric.subst_bounded, subst_entry, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem coefficient_at (C A i : PTm n) (h : Γ ⊢[PRAAx] coefficientBounds C A)
    (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx] bounded (entry C i) A one := by
  have rule : Γ ⊢[PRAAx] lt i (length C) ⟶ bounded (entry C i) A one := by
    simpa only [coefficientBounds,Fm.subst_imp,subst_lt,subst_length,
      GaussianRationalMetric.subst_bounded,subst_entry,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact .impE rule hi

theorem tail_bound_step (C w N A k : PTm n)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hC : Γ ⊢[PRAAx] coefficientBounds C A)
    (hw : Γ ⊢[PRAAx] bounded w one (radius A))
    (ih : Γ ⊢[PRAAx] bounded (tail C w N k) (A*geometric A k) (pw (radius A) k)) :
    Γ ⊢[PRAAx] bounded (tail C w N (succ k)) (A*geometric A (succ k)) (pw (radius A) (succ k)) := by
  have positive := GaussianPolynomialPerturbation.power_positive (Γ := Γ) (radius A) k
    (GaussianRadiusBudget.radius_positive A)
  have sum := bounded_sum _ _ _ _ _ _ positive (le_refl _)
    ih (coefficient_at C A (monus N k) hC
      (le_congr (succ_eq_add_one _).eqSymm
        ((succ_eq_add_one N).eqSymm.eqTrans hLen.eqSymm)
        (add_le_add_right one (monus_le_left N k))))
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
    simpa only [Fm.shift,subst_coefficientBounds,Syn.shift] using hC.shift
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

theorem euclidean_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (var 0) ≐ succ (var 2)) ⟶ coefficientBounds (var 0) (var 3) ⟶
      bounded (var 1) one (radius (var 3)) ⟶
        bounded (tail (var 0) (var 1) (var 2) (var 4))
          (var 3*geometric (var 3) (var 4)) (pw (radius (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (tail_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem euclidean_outside_impossible_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ normLower (var 1) (radius (var 3)) ⟶ .bot) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (.impI
    (outside_impossible _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))))

theorem euclidean_residual_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ (length (var 0) ≐ succ (var 2)) ⟶
      (entry (var 0) zero ≐ qone) ⟶ coefficientBounds (var 0) (var 3) ⟶
        bounded (evaluate (var 0) (var 1)) one one ⟶ bounded (var 1) (var 3+two) one) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (residual_radius _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianEuclideanResidualRadius

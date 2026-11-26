import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTATrajectory
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTAInvariant
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTARates
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalRelativeTwoTerm
import IPRADerivations.Algebra.PowerDifference

/-!
# Finite telescoping of the actual changing-precision trajectory

The finite geometric accumulator is an actual PR program. Quantifier-free
induction on the numerical interval length sums genuine Euclidean step
distances of the actual trajectory. No limit, chosen summation value,
canonical raw increment, or global distance estimate is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTATelescope

open_ipra
open LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants (R C K rhoNum)
open LeanProofs.IPRA.Analysis.GaussianGeneralFTATrajectory (trajectory delta)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded qsub qnormSq)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product)
open LeanProofs.IPRA.Algebra.PowerDifference (gd gd_zero gd_succ power_diff)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scale (a : PR 3) (N h x : PTm n) : PTm n := R a N h x*C a N h x
def numerator (a : PR 3) (N h x j m : PTm n) : PTm n :=
  scale a N h x*K N*pw (rhoNum N) j*gd (K N) (rhoNum N) m
def denominator (N j m : PTm n) : PTm n := pw (K N) (j+m)
def tailNumerator (a : PR 3) (N h x j : PTm n) : PTm n := scale a N h x*K N*pw (rhoNum N) j
def tailDenominator (N j : PTm n) : PTm n := pw (K N) j
def law (a : PR 3) (N h x j m : PTm n) : Fm PTm n :=
  distanceBounded (trajectory a N h x (j+m)) (trajectory a N h x j)
    (numerator a N h x j m) (denominator N j m)
def increments (a : PR 3) (N h x : PTm n) : Fm PTm n := .all
  (bounded (delta a (Syn.shift N) (Syn.shift h) (Syn.shift x) (var 0))
    (scale a (Syn.shift N) (Syn.shift h) (Syn.shift x)*pw (rhoNum (Syn.shift N)) (var 0))
    (pw (K (Syn.shift N)) (var 0)))

ipra_subst scale
ipra_subst numerator
ipra_subst denominator
ipra_subst tailNumerator
ipra_subst tailDenominator
ipra_subst law
ipra_subst increments [Fm.subst_all, GaussianRationalMetric.subst_bounded, GaussianGeneralFTATrajectory.subst_delta,
    subst_scale, GaussianGeneralFTAConstants.subst_rhoNum, GaussianGeneralFTAConstants.subst_K, subst_ap2,
    PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem denominator_positive (N j m : PTm n) (hK : Γ ⊢[PRAAx] le one (K N)) : Γ ⊢[PRAAx]
    le one (denominator N j m) := GaussianPolynomialPerturbation.power_positive _ _ hK

/-- A raw increment is compared through its canonical value, never
identified literally with that value without a canonicality hypothesis. -/
theorem add_increment_distance (z d A B : PTm n) (hd : Γ ⊢[PRAAx] bounded d A B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalHorner.qadd z d) z A B := by
  have recoded : Γ ⊢[PRAAx] bounded (GaussianTranslatedNonconstant.recode d) A B :=
    RationalArgmin.rationalLE_congr (GaussianRationalRelativeTwoTerm.norm_recode d).eqSymm (.eqRefl _) hd
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticCoefficientValues.qadd_sub_recode z d).eqSymm (.eqRefl _) (.eqRefl _) recoded

theorem increment_at (a : PR 3) (N h x j : PTm n) (hs : Γ ⊢[PRAAx] increments a N h x) : Γ ⊢[PRAAx]
    bounded (delta a N h x j) (scale a N h x*pw (rhoNum N) j) (pw (K N) j) := by
  simpa only [increments,GaussianRationalMetric.subst_bounded,GaussianGeneralFTATrajectory.subst_delta,subst_scale,
    GaussianGeneralFTAConstants.subst_rhoNum,GaussianGeneralFTAConstants.subst_K,subst_ap2,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.allE j

theorem adjacent_distance (a : PR 3) (N h x j : PTm n) (hs : Γ ⊢[PRAAx] increments a N h x) : Γ ⊢[PRAAx]
    distanceBounded (trajectory a N h x (succ j)) (trajectory a N h x j)
      (scale a N h x*pw (rhoNum N) j) (pw (K N) j) :=
  distance_congr (GaussianGeneralFTATrajectory.trajectory_update a N h x j).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (add_increment_distance _ _ _ _ (increment_at a N h x j hs))

theorem numerator_zero (a : PR 3) (N h x j : PTm n) : Γ ⊢[PRAAx] numerator a N h x j zero ≐ zero :=
  (congrMul (.eqRefl _) (gd_zero _ _)).eqTrans (by ipra_ring)

theorem finite_zero (a : PR 3) (N h x j : PTm n) (hK : Γ ⊢[PRAAx] le one (K N)) : Γ ⊢[PRAAx]
    law a N h x j zero :=
  distance_congr (GaussianGeneralFTATrajectory.trajectory_index_congr a N h x (add_zero j)).eqSymm
    (.eqRefl _) (numerator_zero a N h x j).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (denominator_positive N j zero hK))

theorem finite_step_cross (a : PR 3) (N h x j m : PTm n) : Γ ⊢[PRAAx]
    (scale a N h x*pw (rhoNum N) (j+m)+numerator a N h x j m)*denominator N j (succ m) ≐
      numerator a N h x j (succ m)*denominator N j m := by
  have g := natEq (gd_succ (Γ := Γ) (K N) (rhoNum N) m)
  have p := natEq (pw_add (Γ := Γ) (rhoNum N) j m)
  have d : Γ ⊢[PRAAx] pw (K N) (j+succ m) ≐ pw (K N) (j+m)*K N :=
    (congrAp2 powF (by ipra_ring) (.eqRefl _)).eqTrans (pw_succ _ _)
  have de := natEq d
  unfold numerator denominator
  apply deriveNat; ipra_simps
  rw [de,g,p]
  ring

theorem finite_step (a : PR 3) (N h x j m : PTm n)
    (hK : Γ ⊢[PRAAx] le one (K N)) (hs : Γ ⊢[PRAAx] increments a N h x)
    (previous : Γ ⊢[PRAAx] law a N h x j m) : Γ ⊢[PRAAx] law a N h x j (succ m) := by
  have current := adjacent_distance a N h x (j+m) hs
  have triangle := distance_triangle_same _ _ _ _ _ _ (denominator_positive N j m hK) current previous
  have index : Γ ⊢[PRAAx] j+succ m ≐ succ (j+m) := by ipra_ring
  have cross : Γ ⊢[PRAAx]
      le ((scale a N h x*pw (rhoNum N) (j+m)+numerator a N h x j m)*denominator N j (succ m))
        (numerator a N h x j (succ m)*denominator N j m) :=
    le_of_eq_add (d := zero) ((finite_step_cross a N h x j m).eqSymm.eqTrans (add_zero _).eqSymm)
  exact distance_congr
    (GaussianGeneralFTATrajectory.trajectory_index_congr a N h x index).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (denominator_positive N j m hK) (denominator_positive N j (succ m) hK)
      cross triangle)

theorem finite_bound (a : PR 3) (N h x j m : PTm n)
    (hK : Γ ⊢[PRAAx] le one (K N)) (hs : Γ ⊢[PRAAx] increments a N h x) : Γ ⊢[PRAAx]
    law a N h x j m := by
  have kshift : Γ.map Fm.shift ⊢[PRAAx] le one (K (Syn.shift N)) := by
    simpa only [Fm.shift,subst_le,GaussianGeneralFTAConstants.subst_K,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero,Syn.shift] using hK.shift
  have sshift : Γ.map Fm.shift ⊢[PRAAx] increments a (Syn.shift N) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,subst_increments,Syn.shift] using hs.shift
  have all : Γ ⊢[PRAAx] .all (law a (Syn.shift N) (Syn.shift h) (Syn.shift x) (Syn.shift j) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_law]
    · exact finite_zero a N h x j hK
    · exact finite_step _ _ _ _ _ _ kshift.wk sshift.wk Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

theorem geometric_complement (N m : PTm n) (hK : Γ ⊢[PRAAx] le one (K N)) : Γ ⊢[PRAAx]
    pw (K N) m ≐ pw (rhoNum N) m+gd (K N) (rhoNum N) m := by
  have shape : Γ ⊢[PRAAx] K N ≐ rhoNum N+one := GaussianGeneralFTARates.predecessor_form (K N) hK
  ipra_lc natEq (power_diff (Γ := Γ) (K N) (rhoNum N) m)+(Groth.ι (IPRA.Q.mk Γ (gd (K N) (rhoNum N) m)))*natEq shape

theorem geometric_le (N m : PTm n) (hK : Γ ⊢[PRAAx] le one (K N)) : Γ ⊢[PRAAx]
    le (gd (K N) (rhoNum N) m) (pw (K N) m) :=
  le_congr (.eqRefl _) (geometric_complement N m hK).eqSymm (le_add_left _ _)

theorem uniform_cross (a : PR 3) (N h x j m : PTm n) (hK : Γ ⊢[PRAAx] le one (K N)) : Γ ⊢[PRAAx]
    le (numerator a N h x j m*tailDenominator N j) (tailNumerator a N h x j*denominator N j m) := by
  have actual := mul_le_mul_right (scale a N h x*K N*pw (rhoNum N) j*pw (K N) j) (geometric_le N m hK)
  refine le_congr (by unfold numerator tailDenominator; ipra_ring) ?_ actual
  refine withEq (pw_add (K N) j m) fun e => ?_
  unfold tailNumerator denominator
  apply deriveNat; ipra_simps; rw [e]; ring

theorem offset_tail (a : PR 3) (N h x j m : PTm n)
    (hK : Γ ⊢[PRAAx] le one (K N)) (hs : Γ ⊢[PRAAx] increments a N h x) : Γ ⊢[PRAAx]
    distanceBounded (trajectory a N h x (j+m)) (trajectory a N h x j)
      (tailNumerator a N h x j) (tailDenominator N j) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive N j m hK)
    (GaussianPolynomialPerturbation.power_positive _ _ hK) (uniform_cross a N h x j m hK)
    (finite_bound a N h x j m hK hs)

theorem interval_tail (a : PR 3) (N h x j ell : PTm n)
    (hK : Γ ⊢[PRAAx] le one (K N)) (hs : Γ ⊢[PRAAx] increments a N h x)
    (hj : Γ ⊢[PRAAx] le j ell) : Γ ⊢[PRAAx]
    distanceBounded (trajectory a N h x ell) (trajectory a N h x j)
      (tailNumerator a N h x j) (tailDenominator N j) :=
  distance_congr (GaussianGeneralFTATrajectory.trajectory_index_congr a N h x (eq_add_of_le hj).eqSymm)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (offset_tail a N h x j (monus ell j) hK hs)

theorem source_increments (a : PR 3) (N k h x : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGeneralPolynomialSamples.sourceInput a N k h x) : Γ ⊢[PRAAx]
    increments a N h x := by
  have shifted : Γ.map Fm.shift ⊢[PRAAx] GaussianGeneralPolynomialSamples.sourceInput a
      (Syn.shift N) (Syn.shift k) (Syn.shift h) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianGeneralPolynomialSamples.subst_sourceInput,Syn.shift] using hSource.shift
  refine .allI ?_
  exact GaussianGeneralFTAInvariant.displacement_uniform a (Syn.shift N) (Syn.shift k) (Syn.shift h)
    (Syn.shift x) (var 0) shifted

theorem source_finite_bound (a : PR 3) (N k h x j m : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGeneralPolynomialSamples.sourceInput a N k h x) : Γ ⊢[PRAAx]
    law a N h x j m :=
  finite_bound a N h x j m
    (GaussianGeneralFTAConstants.K_positive N (GaussianGeneralFTARadiusStep.source_degree a N k h x hSource))
    (source_increments a N k h x hSource)

/-- The actual source interval bound has only the original coefficient
names, finite apartness input and the queried interval order as premises. -/
theorem source_tail (a : PR 3) (N k h x j ell : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGeneralPolynomialSamples.sourceInput a N k h x)
    (hj : Γ ⊢[PRAAx] le j ell) : Γ ⊢[PRAAx]
    distanceBounded (trajectory a N h x ell) (trajectory a N h x j)
      (tailNumerator a N h x j) (tailDenominator N j) :=
  interval_tail a N h x j ell
    (GaussianGeneralFTAConstants.K_positive N (GaussianGeneralFTARadiusStep.source_degree a N k h x hSource))
    (source_increments a N k h x hSource) hj

def output (a : PR 3) (N h x j ell : PTm n) : PTm n :=
  pairT (trajectory a N h x ell) (pairT (trajectory a N h x j)
    (pairT (tailNumerator a N h x j) (tailDenominator N j)))
def outputF (a : PR 3) : PR 5 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3) (var 4))
def run (a : PR 3) (N h x j ell : PTm n) : PTm n := PTm.app (outputF a) ![N,h,x,j,ell]
ipra_subst output
ipra_subst run

theorem program_at (a : PR 3) (N h x j ell : PTm n) : Γ ⊢[PRAAx]
    run a N h x j ell ≐ output a N h x j ell := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output a (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![N,h,x,j,ell]
theorem returned_later (a : PR 3) (N h x j ell : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N h x j ell) ≐ trajectory a N h x ell :=
  (program_at a N h x j ell).fstE
theorem returned_earlier (a : PR 3) (N h x j ell : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run a N h x j ell)) ≐ trajectory a N h x j :=
  (program_at a N h x j ell).sndE.fstE
theorem returned_numerator (a : PR 3) (N h x j ell : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run a N h x j ell))) ≐ tailNumerator a N h x j :=
  (program_at a N h x j ell).sndE.sndE.fstE
theorem returned_denominator (a : PR 3) (N h x j ell : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run a N h x j ell))) ≐ tailDenominator N j :=
  (program_at a N h x j ell).sndE.sndE.sndE

theorem returned_tail (a : PR 3) (N k h x j ell : PTm n)
    (hSource : Γ ⊢[PRAAx] GaussianGeneralPolynomialSamples.sourceInput a N k h x)
    (hj : Γ ⊢[PRAAx] le j ell) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run a N h x j ell)) (fstT (sndT (run a N h x j ell)))
      (fstT (sndT (sndT (run a N h x j ell)))) (sndT (sndT (sndT (run a N h x j ell)))) :=
  distance_congr (returned_later a N h x j ell).eqSymm (returned_earlier a N h x j ell).eqSymm
    (returned_numerator a N h x j ell).eqSymm (returned_denominator a N h x j ell).eqSymm
    (source_tail a N k h x j ell hSource hj)

theorem actual_finite_telescope_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGeneralPolynomialSamples.sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶
      law a (var 0) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (source_finite_bound _ _ _ _ _ _ _ Prf.hyp0))
theorem source_iterate_tail_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGeneralPolynomialSamples.sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      distanceBounded (trajectory a (var 0) (var 2) (var 3) (var 5)) (trajectory a (var 0) (var 2) (var 3) (var 4))
        (tailNumerator a (var 0) (var 2) (var 3) (var 4)) (tailDenominator (var 0) (var 4))) :=
  closeUniv 6 (.impI (.impI (source_tail _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_telescope_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run a (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output a (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _ _)
theorem returned_source_tail_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGeneralPolynomialSamples.sourceInput a (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      distanceBounded (fstT (run a (var 0) (var 2) (var 3) (var 4) (var 5)))
        (fstT (sndT (run a (var 0) (var 2) (var 3) (var 4) (var 5))))
        (fstT (sndT (sndT (run a (var 0) (var 2) (var 3) (var 4) (var 5)))))
        (sndT (sndT (sndT (run a (var 0) (var 2) (var 3) (var 4) (var 5)))))) :=
  closeUniv 6 (.impI (.impI (returned_tail _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGeneralFTATelescope

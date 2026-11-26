import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormEntries
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianReconstructionRoots

/-!
# Computed source bounds for Gaussian-rational coefficient names

The coefficient evaluator is a fixed PR3 schema; degree, sample precision
and persistent data remain internal. The actual normalized maximum of the
precision-zero L1 norms computes the exact source ceiling and radius. No
maximum certificate or uniform coefficient bound is supplied as an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode natCode_represents)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE left)
open LeanProofs.IPRA.Analysis.RationalArithmetic (maximum)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize positivePart)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.BoundedFormulas (subst_up_shift')

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def maxStep (a : PR 3) : PTm 3 := maximum (var 1) (qL1 (ap3 a (var 0) zero (var 2)))
def maxF (a : PR 3) : PR 2 := rec2 (natCode zero : PTm 1) (maxStep a)
def M (a : PR 3) (N x : PTm n) : PTm n := ap2 (maxF a) N x
def ceilM (a : PR 3) (N x : PTm n) : PTm n := GaussianDescentClockArithmetic.ceiling
  (positivePart (numeratorOf (M a N x))) (denominatorOf (M a N x))
def three : PTm n := succ two
def A (a : PR 3) (N x : PTm n) : PTm n := three+ceilM a N x
def R (a : PR 3) (N x : PTm n) : PTm n := A a N x+two

ipra_subst M
ipra_subst ceilM
ipra_subst three
ipra_subst A
ipra_subst R

theorem max_zero (a : PR 3) (x : PTm n) : Γ ⊢[PRAAx] M a zero x ≐ natCode zero := by
  simpa only [M,maxF,GaussianRationalSyntheticBounds.subst_natCode,ConciseIPRA.PTm.subst_zero] using
    rec2_zero (Γ := Γ) (natCode zero : PTm 1) (maxStep a) x

theorem max_succ (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx]
    M a (succ N) x ≐ maximum (M a N x) (qL1 (ap3 a N zero x)) := by
  simpa only [M,maxF,maxStep,RationalArithmetic.subst_maximum,GaussianRationalL1.subst_qL1,
    subst_ap3,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      rec2_succ (Γ := Γ) (natCode zero : PTm 1) (maxStep a) N x

theorem max_step_monotone (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] rationalLE (M a N x) (M a (succ N) x) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (max_succ a N x).eqSymm (Prf.andE₁ (RationalArithmetic.maximum_bounds _ _))
theorem max_last_bound (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (ap3 a N zero x)) (M a (succ N) x) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (max_succ a N x).eqSymm (Prf.andE₂ (RationalArithmetic.maximum_bounds _ _))

theorem max_nonnegative (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] rationalLE (natCode zero) (M a N x) := by
  have all : Γ ⊢[PRAAx] .all (rationalLE (natCode zero) (M a (var 0) (Syn.shift x))) := by
    ipra_qfind (le_QF _ _) [RationalArgmin.subst_rationalLE, GaussianRationalSyntheticBounds.subst_natCode, subst_M]
    · exact RationalArgmin.rationalLE_congr (.eqRefl _) (max_zero a x).eqSymm (RationalArgmin.reflexive _)
    · exact RationalArgmin.transitive Prf.hyp0 (max_step_monotone a _ _)
  simpa only [RationalArgmin.subst_rationalLE,GaussianRationalSyntheticBounds.subst_natCode,subst_M,
    ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def maxEntryLaw (a : PR 3) (i N x : PTm n) : Fm PTm n := lt i N ⟶ rationalLE (qL1 (ap3 a i zero x)) (M a N x)
ipra_subst maxEntryLaw

theorem max_entry_step (a : PR 3) (i N x : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N))
    (ih : Γ ⊢[PRAAx] maxEntryLaw a i N x) : Γ ⊢[PRAAx] rationalLE (qL1 (ap3 a i zero x)) (M a (succ N) x) := by
  have h : Γ ⊢[PRAAx] le i N := (succ_monus_succ _ _).eqSymm.eqTrans hi
  refine .orE (lt_or_eq_of_le h) ?_ ?_
  · exact RationalArgmin.transitive (.impE ih.wk Prf.hyp0) (max_step_monotone a N x)
  · exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr (congrAp3 a Prf.hyp0 (.eqRefl _) (.eqRefl _))).eqSymm
      (.eqRefl _) (max_last_bound a N x)

theorem max_entry_bound (a : PR 3) (i N x : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (ap3 a i zero x)) (M a N x) := by
  have all : Γ ⊢[PRAAx] .all (maxEntryLaw a (Syn.shift i) (var 0) (Syn.shift x)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_maxEntryLaw]
    · exact .impI (lt_irrefl zero _ (lt_of_le_of_lt (zero_le i) Prf.hyp0))
    · exact .impI (max_entry_step a _ _ _ Prf.hyp0 Prf.hyp1)
  have rule : Γ ⊢[PRAAx] maxEntryLaw a i N x := by
    simpa only [subst_maxEntryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE rule hi

theorem max_natural_representation (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (M a N x) (ZT.ofNat (positivePart (numeratorOf (M a N x)))) (denominatorOf (M a N x)) := by
  have h := GaussianRationalL1.nonnegative_of_lower _ _ (GaussianRationalSyntheticBounds.natCode_nonnegative zero) (max_nonnegative (Γ := Γ) a N x)
  have e := natEq (eq_add_of_le h)
  apply ZT.derive
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,positivePart]
  ipra_simps
  linear_combination -𝔞(denominatorOf (M a N x))*e

theorem max_le_ceiling (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] rationalLE (M a N x) (natCode (ceilM a N x)) := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ one (RationalArgmin.denominator_positive _) (le_refl _)
    (max_natural_representation a N x) (natCode_represents _)
  exact le_congr (one_mul _).eqSymm (mul_comm _ _)
    (GaussianDescentClockArithmetic.ceiling_lower _ _ (RationalArgmin.denominator_positive _))

theorem initial_coefficient_bound (a : PR 3) (i N x : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    bounded (ap3 a i zero x) (ceilM a N x) one :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl _)
    (RationalArgmin.transitive (max_entry_bound a i N x hi) (max_le_ceiling a N x))

theorem A_lower (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] le three (A a N x) := le_add_right _ _
theorem A_minus_one (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] PTm.monus (A a N x) one ≐ ceilM a N x+two :=
  (congrMonus (by unfold A three; ipra_ring : Γ ⊢[PRAAx] A a N x ≐ one+(ceilM a N x+two)) (.eqRefl _)).eqTrans (add_monus' _ _)

/-- Increasing an original nonnegative rational radius preserves its exact
Euclidean comparison; only the positive radius denominators are required. -/
theorem bounded_radius_mono (z A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hrad : Γ ⊢[PRAAx] le (A*D) (C*B)) (hz : Γ ⊢[PRAAx] bounded z A B) : Γ ⊢[PRAAx] bounded z C D := by
  have sq := le_mul_mono hrad hrad
  have tol : Γ ⊢[PRAAx] rationalLE (GaussianRationalMetric.squaredTolerance A B) (GaussianRationalMetric.squaredTolerance C D) :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
      (GaussianRationalHorner.positive_product _ _ hB hB) (GaussianRationalHorner.positive_product _ _ hD hD)
      (GaussianRationalMetric.squared_tolerance_represents _ _ hB) (GaussianRationalMetric.squared_tolerance_represents _ _ hD)
      (le_congr (by ipra_ring) (by ipra_ring) sq)
  exact RationalArgmin.transitive hz tol

def unit (s : PTm n) : PTm n := pw two s
ipra_subst unit
theorem unit_positive (s : PTm n) : Γ ⊢[PRAAx] le one (unit s) :=
  GaussianFactorBudget.power_positive two s (le_of_eq_add (d := one) (by ipra_ring))

def regularCoefficient (a : PR 3) (i x : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (ap3 a (Syn.shift (Syn.shift i)) (var 1) (Syn.shift (Syn.shift x)))
    (ap3 a (Syn.shift (Syn.shift i)) (var 0) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))
def CN (a : PR 3) (N x : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶ regularCoefficient a (var 0) (Syn.shift x))

ipra_subst regularCoefficient [Syn.subst_shift, Syn.shift_subst]
ipra_subst CN [Syn.subst_shift, Syn.shift_subst]

theorem regular_coefficient_at (a : PR 3) (i x s t : PTm n) (h : Γ ⊢[PRAAx] regularCoefficient a i x) : Γ ⊢[PRAAx]
    distanceBounded (ap3 a i s x) (ap3 a i t x) (unit s+unit t) (unit s*unit t) := by
  have pair : Γ ⊢[PRAAx] .all (distanceBounded (ap3 a (Syn.shift i) (Syn.shift s) (Syn.shift x))
      (ap3 a (Syn.shift i) (var 0) (Syn.shift x)) (unit (Syn.shift s)+unit (var 0)) (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [regularCoefficient,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap3,subst_unit,
      PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE s
  simpa only [Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap3,subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE t

theorem CN_at (a : PR 3) (N x i s t : PTm n) (h : Γ ⊢[PRAAx] CN a N x) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (ap3 a i s x) (ap3 a i t x) (unit s+unit t) (unit s*unit t) := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ regularCoefficient a i x := by
    simpa only [CN,Fm.subst_imp,subst_lt,subst_regularCoefficient,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i
  exact regular_coefficient_at a i x s t (.impE rule hi)

/-- The actual source CN inequality gives a distance at most two from the
precision-zero sample; no sample-size bound is part of CN. -/
theorem sample_zero_distance (a : PR 3) (N x i s : PTm n) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] distanceBounded (ap3 a i s x) (ap3 a i zero x) two one := by
  have h := CN_at a N x i s zero hCN hi
  have radius : Γ ⊢[PRAAx] distanceBounded (ap3 a i s x) (ap3 a i zero x) (unit s+one) (unit s) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (congrAdd (.eqRefl _) (pw_zero two))
      ((congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)) h
  have comparison : Γ ⊢[PRAAx] le ((unit s+one)*one) (two*unit s) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (unit s)) (unit_positive s))
  exact bounded_radius_mono _ _ _ _ _ (unit_positive s) (le_refl _) comparison radius

/-- Exact source sample bound: ceil(M)+2=A-1. The precision-zero maximum
and the original CN observations supply both inputs of the proved original
Gaussian distance triangle. No global sample bound is assumed. -/
theorem sample_bound (a : PR 3) (N x i s : PTm n) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] bounded (ap3 a i s x) (PTm.monus (A a N x) one) one := by
  have h := GaussianReconstructionRoots.norm_from_distance _ _ two one (ceilM a N x) one (le_refl _) (le_refl _)
    (sample_zero_distance a N x i s hCN hi) (initial_coefficient_bound a i N x hi)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    ((by ipra_ring : Γ ⊢[PRAAx] two*one+ceilM a N x*one ≐ ceilM a N x+two).eqTrans (A_minus_one a N x).eqSymm)
    (by ipra_ring) h

/-- The optional source initial AF bound 2A also follows for every sample;
it is not supplied as a bound on the coefficient family. -/
theorem sample_l1_bound (a : PR 3) (N x i s : PTm n) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] rationalLE (qL1 (ap3 a i s x)) (natCode (two*A a N x)) :=
  RationalArgmin.transitive
    (GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl _) (sample_bound a N x i s hCN hi))
    (GaussianRationalSyntheticBounds.natCode_order _ _
      (le_mul_mono (le_refl two) (GaussianMonicResidualRadius.monus_le_left (A a N x) one)))

/-! Actual constant program and uniformly closed source statements. -/
def output (a : PR 3) (N x : PTm n) : PTm n := pairT (M a N x) (pairT (ceilM a N x) (pairT (A a N x) (R a N x)))
def outputF (a : PR 3) : PR 2 := PTm.toPR (output a (var 0) (var 1))
ipra_subst output
theorem output_at (a : PR 3) (N x : PTm n) : Γ ⊢[PRAAx] ap2 (outputF a) N x ≐ output a N x := by
  simpa only [outputF,ap2,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output a (var 0) (var 1) : PTm 2) ![N,x]

theorem maximum_bounds_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (natCode zero) (M a (var 0) (var 1)) ⋏
      (rationalLE (M a (var 0) (var 1)) (natCode (ceilM a (var 0) (var 1))) ⋏
        (lt (var 2) (var 0) ⟶ rationalLE (qL1 (ap3 a (var 2) zero (var 1))) (M a (var 0) (var 1))))) :=
  closeUniv 3 (.andI (max_nonnegative _ _ _) (.andI (max_le_ceiling _ _ _) (.impI (max_entry_bound _ _ _ _ Prf.hyp0))))

theorem maximum_recurrence_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((M a zero (var 1) ≐ natCode zero) ⋏
      (M a (succ (var 0)) (var 1) ≐ maximum (M a (var 0) (var 1)) (qL1 (ap3 a (var 0) zero (var 1))))) :=
  closeUniv 2 (.andI (max_zero _ _) (max_succ _ _ _))

theorem sample_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 1) ⟶ lt (var 2) (var 0) ⟶
      (le three (A a (var 0) (var 1)) ⋏
        bounded (ap3 a (var 2) (var 3) (var 1)) (PTm.monus (A a (var 0) (var 1)) one) one)) :=
  closeUniv 4 (.impI (.impI (.andI (A_lower _ _ _) (sample_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem sample_l1_bound_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 1) ⟶ lt (var 2) (var 0) ⟶
      rationalLE (qL1 (ap3 a (var 2) (var 3) (var 1))) (natCode (two*A a (var 0) (var 1)))) :=
  closeUniv 4 (.impI (.impI (sample_l1_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem source_constants_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 (outputF a) (var 0) (var 1) ≐ output a (var 0) (var 1)) ⋏
      (le three (A a (var 0) (var 1)) ⋏ (R a (var 0) (var 1) ≐ A a (var 0) (var 1)+two))) :=
  closeUniv 2 (.andI (output_at _ _ _) (.andI (A_lower _ _ _) (.eqRefl _)))

end LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds

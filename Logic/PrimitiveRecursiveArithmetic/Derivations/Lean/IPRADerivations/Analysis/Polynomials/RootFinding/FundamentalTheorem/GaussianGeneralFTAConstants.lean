import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowerOrder
import IPRADerivations.Foundations.DemandClosure

/-!
# Computed global constants for the general coefficient-name FTA

The fixed PR3 supplies the coefficient observations. Every degree,
apartness precision and persistent data value is internal. The actual
ceiling of the initial constant-coefficient L1 norm and the existing
checked binary-length program compute all source constants. No global
radius, successful precision search or rate budget is an input.

Here bl is the existing least exponent with x<=2^bl(x). This is the
upper-power convention explicitly permitted by the source Lean plan.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positivePart)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (positive_product)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def initial (a : PR 3) (x : PTm n) : PTm n := ap3 a zero zero x
def ceilL1 (z : PTm n) : PTm n := GaussianDescentClockArithmetic.ceiling
  (positivePart (numeratorOf (qL1 z))) (denominatorOf (qL1 z))
def B (a : PR 3) (x : PTm n) : PTm n := two+ceilL1 (initial a x)
def D (N : PTm n) : PTm n := GaussianDescentClockArithmetic.descentD N
def qDen (N : PTm n) : PTm n := GaussianDescentClockArithmetic.rateDenominator N
def qNum (N : PTm n) : PTm n := pred (qDen N)
def q (N : PTm n) : PTm n := fraction (qNum N) (qDen N)
def QDen (N : PTm n) : PTm n := two*qDen N
def QNum (N : PTm n) : PTm n := pred (QDen N)
def Q (N : PTm n) : PTm n := fraction (QNum N) (QDen N)
def K (N : PTm n) : PTm n := N*QDen N
def rhoNum (N : PTm n) : PTm n := pred (K N)
def rho (N : PTm n) : PTm n := fraction (rhoNum N) (K N)
def C (a : PR 3) (N h x : PTm n) : PTm n := B a x*N*pw two (N+h+one)
def bl (z : PTm n) : PTm n := GaussianRootSchedule.binaryLength z
def A0 (a : PR 3) (N h x : PTm n) : PTm n := bl (two*C a N h x*K N)
def T (a : PR 3) (N h x : PTm n) : PTm n := K N*A0 a N h x
def R (a : PR 3) (N h x : PTm n) : PTm n := two*pw (one+C a N h x) (T a N h x)
def precisionCost (a : PR 3) (N h x : PTm n) : PTm n :=
  (two*two*two*two)*D N*succ N*pw (R a N h x) N
def L (a : PR 3) (N h x : PTm n) : PTm n := maximum (h+two) (bl (precisionCost a N h x))
def H (a : PR 3) (N h x : PTm n) : PTm n := bl (R a N h x*C a N h x*K N)

@[simp] theorem subst_initial {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (x : PTm n) :
    Syn.subst σ (initial a x) = initial a (Syn.subst σ x) := by simp [initial]
@[simp] theorem subst_ceilL1 {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (ceilL1 z) = ceilL1 (Syn.subst σ z) := by simp [ceilL1]
@[simp] theorem subst_B {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (x : PTm n) :
    Syn.subst σ (B a x) = B a (Syn.subst σ x) := by simp [B]
@[simp] theorem subst_D {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (D N) = D (Syn.subst σ N) := by simp [D]
@[simp] theorem subst_qDen {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (qDen N) = qDen (Syn.subst σ N) := by simp [qDen]
@[simp] theorem subst_qNum {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (qNum N) = qNum (Syn.subst σ N) := by simp [qNum]
@[simp] theorem subst_q {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (q N) = q (Syn.subst σ N) := by simp [q]
@[simp] theorem subst_QDen {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (QDen N) = QDen (Syn.subst σ N) := by simp [QDen]
@[simp] theorem subst_QNum {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (QNum N) = QNum (Syn.subst σ N) := by simp [QNum]
@[simp] theorem subst_Q {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (Q N) = Q (Syn.subst σ N) := by simp [Q]
@[simp] theorem subst_K {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (K N) = K (Syn.subst σ N) := by simp [K]
@[simp] theorem subst_rhoNum {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (rhoNum N) = rhoNum (Syn.subst σ N) := by simp [rhoNum]
@[simp] theorem subst_rho {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (rho N) = rho (Syn.subst σ N) := by simp [rho]
@[simp] theorem subst_C {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (C a N h x) = C a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [C]
@[simp] theorem subst_bl {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (bl z) = bl (Syn.subst σ z) := by simp [bl]
@[simp] theorem subst_A0 {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (A0 a N h x) = A0 a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [A0]
@[simp] theorem subst_T {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (T a N h x) = T a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [T]
@[simp] theorem subst_R {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (R a N h x) = R a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [R]
@[simp] theorem subst_precisionCost {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (precisionCost a N h x) = precisionCost a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [precisionCost]
@[simp] theorem subst_L {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (L a N h x) = L a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [L]
@[simp] theorem subst_H {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (H a N h x) = H a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [H]

theorem l1_natural_representation (z : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (qL1 z) (ZT.ofNat (positivePart (numeratorOf (qL1 z)))) (denominatorOf (qL1 z)) := by
  have e := natEq (eq_add_of_le (GaussianRationalL1.qL1_nonnegative (Γ := Γ) z))
  apply ZT.derive
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,positivePart]
  ipra_simps
  linear_combination -𝔞(denominatorOf (qL1 z))*e

theorem ceil_l1_bound (z : PTm n) : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qL1 z) (fraction (ceilL1 z) one) := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ one
    (RationalArgmin.denominator_positive _) (le_refl _) (l1_natural_representation z) (fraction_represents _ _ (le_refl _))
  exact le_congr (one_mul _).eqSymm (mul_comm _ _)
    (GaussianDescentClockArithmetic.ceiling_lower _ _ (RationalArgmin.denominator_positive _))

theorem ceil_norm_bound (z : PTm n) : Γ ⊢[PRAAx] GaussianRationalMetric.bounded z (ceilL1 z) one := by
  have lower : Γ ⊢[PRAAx] le (GaussianL1.norm1 (GaussianRationalL1.rawGaussian z))
      (ceilL1 z*GaussianRationalL1.rawDen z) :=
    le_congr (one_mul _) (.eqRefl _) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianRationalL1.qL1_represents z _ _ (GaussianRationalL1.raw_den_positive z) (GaussianRationalL1.raw_represents z))
      (fraction_represents _ _ (le_refl _)) (ceil_l1_bound z))
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ (GaussianRationalL1.raw_den_positive z)
    (le_refl _) (GaussianRationalL1.raw_represents z)
    (le_congr (by ipra_ring) (by ipra_ring)
      (le_trans (GaussianL1.normSq_le_norm1_square _) (le_mul_mono lower lower)))

theorem B_lower (a : PR 3) (x : PTm n) : Γ ⊢[PRAAx] le two (B a x) := le_add_right _ _
theorem B_positive (a : PR 3) (x : PTm n) : Γ ⊢[PRAAx] le one (B a x) := le_trans (le_succ_self one) (B_lower a x)
theorem D_positive (N : PTm n) : Γ ⊢[PRAAx] le one (D N) :=
  positive_product _ _ (GaussianPolynomialPerturbation.power_positive two N (le_succ_self one))
    (GaussianPolynomialPerturbation.power_positive _ _ GaussianDescentClockArithmetic.four_positive)
theorem qDen_positive (N : PTm n) : Γ ⊢[PRAAx] le one (qDen N) := GaussianDescentClockArithmetic.rate_positive N
theorem QDen_positive (N : PTm n) : Γ ⊢[PRAAx] le one (QDen N) := positive_product two _ (le_succ_self one) (qDen_positive N)
theorem QDen_lower (N : PTm n) : Γ ⊢[PRAAx] le two (QDen N) :=
  le_congr (by ipra_ring) (by unfold QDen; ipra_ring) (mul_le_mul_right two (qDen_positive N))
theorem K_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (K N) :=
  positive_product N _ hN (QDen_positive N)
theorem K_lower (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le two (K N) :=
  le_trans (QDen_lower N) (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (QDen N) hN))
theorem C_ge_B (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le (B a x) (C a N h x) :=
  le_congr (by ipra_ring) (by unfold C; ipra_ring)
    (le_mul_mono (le_refl (B a x)) (positive_product N _ hN (GaussianPolynomialPerturbation.power_positive two _ (le_succ_self one))))
theorem C_positive (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (C a N h x) :=
  le_trans (B_positive a x) (C_ge_B a N h x hN)
theorem R_lower (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] le two (R a N h x) :=
  le_congr (by ipra_ring) (by unfold R; ipra_ring) (mul_le_mul_right two
    (GaussianPolynomialPerturbation.power_positive _ _ (le_add_right one (C a N h x))))
theorem R_positive (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] le one (R a N h x) :=
  le_trans (le_succ_self one) (R_lower a N h x)
theorem bit_budget (z : PTm n) : Γ ⊢[PRAAx] le z (pw two (bl z)) := Prf.andE₁ (GaussianRootSchedule.binary_length_correct z)
theorem A0_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le (two*C a N h x*K N) (pw two (A0 a N h x)) := bit_budget _
theorem L_lower (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] le (h+two) (L a N h x) := Foundations.DemandClosure.maximum_left _ _
theorem L_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le (precisionCost a N h x) (pw two (L a N h x)) :=
  le_trans (bit_budget _) (GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (Foundations.DemandClosure.maximum_right _ _))
theorem H_budget (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    le (R a N h x*C a N h x*K N) (pw two (H a N h x)) := bit_budget _

theorem tail_small (a : PR 3) (N h x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((two*C a N h x*K N)*pw (rhoNum N) (T a N h x)) (pw (K N) (T a N h x)) :=
  le_trans (mul_le_mul_right _ (A0_budget a N h x))
    (GaussianDescentClockArithmetic.dyadic_decay (K N) (A0 a N h x) (K_positive N hN))

theorem C_factorization (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx]
    C a N h x ≐ B a x*(N*pw two N)*pw two (h+one) := by
  have e : Γ ⊢[PRAAx] pw two (N+h+one) ≐ pw two N*pw two (h+one) :=
    (congrAp2 powF (by ipra_ring) (.eqRefl two)).eqTrans (pw_add two N (h+one))
  exact (congrMul (.eqRefl (B a x*N)) e).eqTrans (by ipra_ring)

theorem qDen_value (N : PTm n) : Γ ⊢[PRAAx] qDen N ≐ (two*two)*D N := .eqRefl _
theorem QDen_value (N : PTm n) : Γ ⊢[PRAAx] QDen N ≐ (two*two*two)*D N :=
  (congrMul (.eqRefl two) (qDen_value N)).eqTrans (by ipra_ring)
theorem K_value (N : PTm n) : Γ ⊢[PRAAx] K N ≐ (two*two*two)*N*D N :=
  (congrMul (.eqRefl N) (QDen_value N)).eqTrans (by ipra_ring)

/-- The returned tuple contains all twelve source constants, including
the actual normalized rational rates rather than claimed rate values. -/
def output (a : PR 3) (N h x : PTm n) : PTm n :=
  pairT (B a x) (pairT (D N) (pairT (q N) (pairT (Q N) (pairT (K N) (pairT (rho N)
    (pairT (C a N h x) (pairT (A0 a N h x) (pairT (T a N h x)
      (pairT (R a N h x) (pairT (L a N h x) (H a N h x)))))))))))
def outputF (a : PR 3) : PR 3 := PTm.toPR (output a (var 0) (var 1) (var 2))
def run (a : PR 3) (N h x : PTm n) : PTm n := ap3 (outputF a) N h x
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (output a N h x) = output a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N h x : PTm n) :
    Syn.subst σ (run a N h x) = run a (Syn.subst σ N) (Syn.subst σ h) (Syn.subst σ x) := by simp [run]
theorem program_at (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] run a N h x ≐ output a N h x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) : PTm 3) ![N,h,x]
theorem returned_B (a : PR 3) (N h x : PTm n) : Γ ⊢[PRAAx] fstT (run a N h x) ≐ B a x :=
  (congrFst (program_at a N h x)).eqTrans (fst_pair _ _)

theorem initial_l1_ceiling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalArgmin.rationalLE (qL1 (var 0)) (fraction (ceilL1 (var 0)) one) ⋏
      GaussianRationalMetric.bounded (var 0) (ceilL1 (var 0)) one) :=
  closeUniv 1 (.andI (ceil_l1_bound _) (ceil_norm_bound _))
theorem computed_general_fta_positive_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ (le two (B a (var 2)) ⋏ (le one (D (var 0)) ⋏
      (le two (K (var 0)) ⋏ (le (B a (var 2)) (C a (var 0) (var 1) (var 2)) ⋏ le two (R a (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.impI (.andI (B_lower _ _) (.andI (D_positive _) (.andI (K_lower _ Prf.hyp0)
    (.andI (C_ge_B _ _ _ _ Prf.hyp0) (R_lower _ _ _ _))))))
theorem computed_general_fta_precision_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1+two) (L a (var 0) (var 1) (var 2)) ⋏
      (le (precisionCost a (var 0) (var 1) (var 2)) (pw two (L a (var 0) (var 1) (var 2))) ⋏
        le (R a (var 0) (var 1) (var 2)*C a (var 0) (var 1) (var 2)*K (var 0))
          (pw two (H a (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (L_lower _ _ _ _) (.andI (L_budget _ _ _ _) (H_budget _ _ _ _)))
theorem computed_general_fta_tail_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le ((two*C a (var 0) (var 1) (var 2)*K (var 0))*
      pw (rhoNum (var 0)) (T a (var 0) (var 1) (var 2))) (pw (K (var 0)) (T a (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (tail_small _ _ _ _ Prf.hyp0))
theorem source_step_constant_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (C a (var 0) (var 1) (var 2) ≐ B a (var 2)*(var 0*pw two (var 0))*pw two (var 1+one)) :=
  closeUniv 3 (C_factorization _ _ _ _)
theorem general_fta_constants_program_closed (a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run a (var 0) (var 1) (var 2) ≐ output a (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGeneralFTAConstants

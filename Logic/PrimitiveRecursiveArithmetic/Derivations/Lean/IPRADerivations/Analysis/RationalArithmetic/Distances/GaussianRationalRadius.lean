import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalMetric
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianProductStability

/-!
# An actual common-scale radius for original Gaussian rational lists

The rational radius u/v is inserted as the real query point in the actual
normalization pool for both input lists. The positive part of its computed
integer real numerator is the integer radius R. Its exact value vR=uD,
its lower bound D≤R when v≤u, and original-point norm bounds are derived
from the actual quotient normalization, not supplied as contracts.

The source precision budget transports exactly to the computed scale by
finite power multiplication and cancellation of the proved positive power
of v. Degree, radius data, error/tolerance data and lists remain numerical
inputs; zero degree and zero tolerances are allowed in these arithmetic
lemmas. This is the radius/budget adapter for finite-demand Section 4.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRadius

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code normSq eval_re_code)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positivePart positive_form)
open LeanProofs.IPRA.Analysis.GaussianRationalNormalization
  (commonD queryNumerator sourceNumerators targetNumerators commonD_positive query_clearing source_clearing target_clearing)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (ofGaussian represents)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded bounded_to_cleared)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The actual normalized Gaussian rational radius is added to the pool. -/
def radiusQuery (u v : PTm n) : PTm n := ofGaussian (code (ZT.ofNat u) (ZT.ofNat zero)) v
def scaleDenominator (S T u v : PTm n) : PTm n := commonD S T (radiusQuery u v)
def rawRadius (S T u v : PTm n) : PTm n := positivePart (re (queryNumerator S T (radiusQuery u v)))

ipra_subst radiusQuery
ipra_subst scaleDenominator
ipra_subst rawRadius

theorem scale_positive (S T u v : PTm n) : Γ ⊢[PRAAx] le one (scaleDenominator S T u v) := commonD_positive _ _ _

theorem radius_real_represents (u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (radiusQuery u v)) (ZT.ofNat u) v := by
  have h := Prf.andE₁ (GaussianRationalHorner.ofGaussian_represents (Γ := Γ)
    (code (ZT.ofNat u) (ZT.ofNat zero)) v hv)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _) h
  apply ZT.derive
  exact eval_re_code _ _

/-- The computed query numerator satisfies the exact signed rational radius
identity. Only the decoded positive denominator of the actual real query
component is canceled. -/
theorem query_radius_value (S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    ZT.eq (re (queryNumerator S T (radiusQuery u v))*ZT.ofNat v)
      (ZT.ofNat (u*scaleDenominator S T u v)) := by
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (denominatorOf (fstT (radiusQuery u v))) _ _
    (RationalArgmin.denominator_positive _)
  apply ZT.derive
  have h := ZT.toZ_eq (Prf.andE₁ (query_clearing (Γ := Γ) S T (radiusQuery u v)))
  have r := ZT.toZ_eq (radius_real_represents (Γ := Γ) u v hv)
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at h r ⊢
  change ZT.toZ Γ (re (queryNumerator S T (radiusQuery u v)))*𝔞(denominatorOf (fstT (radiusQuery u v))) =
    ZT.toZ Γ (numeratorOf (fstT (radiusQuery u v)))*𝔞(scaleDenominator S T u v) at h
  ipra_simps
  linear_combination 𝔞(v)*h-𝔞(scaleDenominator S T u v)*r

/-- The decoded signed query value is nonnegative. No canonical signed-part
condition is required of its input code. -/
theorem query_nonnegative (S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    le (re (queryNumerator S T (radiusQuery u v))).neg (re (queryNumerator S T (radiusQuery u v))).pos := by
  have value := ZT.toZ_eq (query_radius_value (Γ := Γ) S T u v hv)
  have scaled : Γ ⊢[PRAAx]
      le (v*(re (queryNumerator S T (radiusQuery u v))).neg)
        (v*(re (queryNumerator S T (radiusQuery u v))).pos) := by
    refine le_of_eq_add (d := u*scaleDenominator S T u v) ?_
    apply deriveNat
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at value
    simp only [ZT.toZ] at value
    ipra_simps
    linear_combination value
  exact RationalValueBounds.positive_cancel hv scaled

/-- The actual natural radius is exactly uD/v, with no rounding loss. -/
theorem radius_clears (S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    v*rawRadius S T u v ≐ u*scaleDenominator S T u v := by
  have value := ZT.toZ_eq (query_radius_value (Γ := Γ) S T u v hv)
  have gap := natEq (eq_add_of_le (query_nonnegative (Γ := Γ) S T u v hv))
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at value
  simp only [ZT.toZ] at value
  unfold rawRadius positivePart
  ipra_simps
  linear_combination value-𝔞(v)*gap

theorem radius_ge_scale (S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hvu : Γ ⊢[PRAAx] le v u) : Γ ⊢[PRAAx] le (scaleDenominator S T u v) (rawRadius S T u v) := by
  apply RationalValueBounds.positive_cancel hv
  have h := mul_le_mul_right (scaleDenominator S T u v) hvu
  exact le_congr (.eqRefl _) (radius_clears S T u v hv).eqSymm h

/-- Original rational norm bounds supply actual integer point bounds in the
computed radius. The factor canceled in this inequality is v²>0. -/
theorem bound_of_representation (q g S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hq : Γ ⊢[PRAAx] represents q g (scaleDenominator S T u v))
    (hbound : Γ ⊢[PRAAx] bounded q u v) : Γ ⊢[PRAAx]
    le (normSq g) (rawRadius S T u v*rawRadius S T u v) := by
  have bound := bounded_to_cleared q g (scaleDenominator S T u v) u v (scale_positive S T u v) hv hq hbound
  have same : Γ ⊢[PRAAx] (u*u)*(scaleDenominator S T u v*scaleDenominator S T u v) ≐
      (v*v)*(rawRadius S T u v*rawRadius S T u v) := by
    ipra_lc -(𝔞(v)*𝔞(rawRadius S T u v)+𝔞(u)*𝔞(scaleDenominator S T u v))*natEq (radius_clears (Γ := Γ) S T u v hv)
  exact RationalValueBounds.positive_cancel
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono hv hv))
    (le_congr (.eqRefl _) same bound)

theorem source_bound (S T u v i : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hi : Γ ⊢[PRAAx] lt i (length S)) (hbound : Γ ⊢[PRAAx] bounded (entry S i) u v) : Γ ⊢[PRAAx]
    le (normSq (entry (sourceNumerators S T (radiusQuery u v)) i)) (rawRadius S T u v*rawRadius S T u v) :=
  bound_of_representation _ _ _ _ _ _ hv (source_clearing S T (radiusQuery u v) i hi) hbound

theorem target_bound (S T u v i : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hi : Γ ⊢[PRAAx] lt i (length T)) (hbound : Γ ⊢[PRAAx] bounded (entry T i) u v) : Γ ⊢[PRAAx]
    le (normSq (entry (targetNumerators S T (radiusQuery u v)) i)) (rawRadius S T u v*rawRadius S T u v) :=
  bound_of_representation _ _ _ _ _ _ hv (target_clearing S T (radiusQuery u v) i hi) hbound

/-- Exact multiplication of the independently computed scale and radius
powers. No external bound on the numerical exponent is used. -/
theorem radius_power (S T u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    pw v k*pw (rawRadius S T u v) k ≐ pw u k*pw (scaleDenominator S T u v) k :=
  (GaussianProductStability.power_product v (rawRadius S T u v) k).eqSymm.eqTrans
    ((congrAp2 powF (.eqRefl k) (radius_clears S T u v hv)).eqTrans
      (GaussianProductStability.power_product u (scaleDenominator S T u v) k))

def sourceBudget (N u v A B p q : PTm n) : Fm PTm n :=
  le (pw q N*N*pw u (PTm.pred N)*A) (pw p N*B*pw v (PTm.pred N))
def scaledBudget (N S T u v A B p q : PTm n) : Fm PTm n :=
  le (pw q N*N*pw (rawRadius S T u v) (PTm.pred N)*A)
    (pw p N*B*pw (scaleDenominator S T u v) (PTm.pred N))

ipra_subst sourceBudget
ipra_subst scaledBudget

theorem budget_transport (N S T u v A B p q : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (h : Γ ⊢[PRAAx] sourceBudget N u v A B p q) : Γ ⊢[PRAAx] scaledBudget N S T u v A B p q := by
  apply RationalValueBounds.positive_cancel (c := pw v (PTm.pred N))
    (GaussianRationalRootProduct.common_denominator_positive v (PTm.pred N) hv)
  have lhs : Γ ⊢[PRAAx]
      pw v (PTm.pred N)*(pw q N*N*pw (rawRadius S T u v) (PTm.pred N)*A) ≐
        (pw q N*N*pw u (PTm.pred N)*A)*pw (scaleDenominator S T u v) (PTm.pred N) := by
    ipra_lc 𝔞(pw q N)*𝔞(N)*𝔞(A)*natEq (radius_power (Γ := Γ) S T u v (PTm.pred N) hv)
  exact le_congr lhs.eqSymm (by ipra_ring)
    (mul_le_mul_right (pw (scaleDenominator S T u v) (PTm.pred N)) h)

theorem radius_positive (S T u v : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hvu : Γ ⊢[PRAAx] le v u) : Γ ⊢[PRAAx] le one (rawRadius S T u v) :=
  le_trans (scale_positive S T u v) (radius_ge_scale S T u v hv hvu)

/-- Fixed PR4 output includes the actual rational radius query and both
computed natural parameters, rather than supplied correctness fields. -/
def radiusOutput (S T u v : PTm n) : PTm n :=
  pairT (radiusQuery u v) (pairT (scaleDenominator S T u v) (rawRadius S T u v))
def radiusF : PR 4 := PTm.toPR (radiusOutput (var 0) (var 1) (var 2) (var 3))

ipra_subst radiusOutput

theorem radius_program (S T u v : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app radiusF ![S,T,u,v] ≐ radiusOutput S T u v := by
  simpa only [radiusF,subst_radiusOutput,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (radiusOutput (var 0) (var 1) (var 2) (var 3) : PTm 4) ![S,T,u,v]

theorem actual_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ le (var 3) (var 2) ⟶
      (le one (scaleDenominator (var 0) (var 1) (var 2) (var 3)) ⋏
        ((var 3*rawRadius (var 0) (var 1) (var 2) (var 3) ≐
            var 2*scaleDenominator (var 0) (var 1) (var 2) (var 3)) ⋏
          (le (scaleDenominator (var 0) (var 1) (var 2) (var 3)) (rawRadius (var 0) (var 1) (var 2) (var 3)) ⋏
            le one (rawRadius (var 0) (var 1) (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.andI (scale_positive _ _ _ _)
    (.andI (radius_clears _ _ _ _ Prf.hyp1) (.andI (radius_ge_scale _ _ _ _ Prf.hyp1 Prf.hyp0)
      (radius_positive _ _ _ _ Prf.hyp1 Prf.hyp0))))))

theorem representation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ represents (var 0) (var 1) (scaleDenominator (var 2) (var 3) (var 4) (var 5)) ⟶
      bounded (var 0) (var 4) (var 5) ⟶
        le (normSq (var 1)) (rawRadius (var 2) (var 3) (var 4) (var 5)*rawRadius (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (bound_of_representation _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem source_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ lt (var 4) (length (var 0)) ⟶ bounded (entry (var 0) (var 4)) (var 2) (var 3) ⟶
      le (normSq (entry (sourceNumerators (var 0) (var 1) (radiusQuery (var 2) (var 3))) (var 4)))
        (rawRadius (var 0) (var 1) (var 2) (var 3)*rawRadius (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (source_bound _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem target_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ lt (var 4) (length (var 1)) ⟶ bounded (entry (var 1) (var 4)) (var 2) (var 3) ⟶
      le (normSq (entry (targetNumerators (var 0) (var 1) (radiusQuery (var 2) (var 3))) (var 4)))
        (rawRadius (var 0) (var 1) (var 2) (var 3)*rawRadius (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (target_bound _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem budget_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le one (var 4) ⟶ sourceBudget (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      scaledBudget (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (budget_transport _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem radius_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ConciseIPRA.PTm.app radiusF ![var 0,var 1,var 2,var 3] ≐ radiusOutput (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (radius_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalRadius

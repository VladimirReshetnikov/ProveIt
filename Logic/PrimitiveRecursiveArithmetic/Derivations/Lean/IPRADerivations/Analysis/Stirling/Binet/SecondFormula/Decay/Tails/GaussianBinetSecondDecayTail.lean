import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.FiniteRows.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.Stirling.Binet.Kernel.Bounds.GaussianBinetKernelTailMajorant

/-!
# Inverse-square summation of second Binet row bounds

The actual finite Gaussian sum inherits the scalar reciprocal-square
tail. The hypothesis is on the original row body and its finite
data, so it also applies when the rows use different certified clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayTail

open_ipra
open GaussianBinetSecondDecayEnvelope (fraction_majorized)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded comparison_to_cleared)
open GaussianRationalSumMajorant (majorized_congr termsMajorized sum_majorized)
open RationalAlgebra (multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalReciprocalPowerTail (potential)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBounds (f : PTm 2) (x C N r : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift r) ⟶
    bounded (inst2 f (var 0) (Syn.shift x)) (Syn.shift C)
      (succ (Syn.shift N+var 0)*succ (Syn.shift N+var 0)))

ipra_subst rowBounds [Syn.subst_shift, Syn.shift_subst]

abbrev scalarBody : PTm 2 := scaledBody RationalReciprocalPowerTail.body
def scalarData (C N : PTm n) : PTm n := pairT (fraction C one) (RationalReciprocalPowerTail.data two N)

ipra_subst scalarData [one, two]

theorem scalar_at (C N i : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (scalarData C N) ≐ fraction C (succ (N+i)*succ (N+i)) := by
  let k := succ (N+i)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have square : Γ ⊢[PRAAx] pw k two ≐ k*k :=
    (pw_succ k one).eqTrans (congrMul (pw_one k) (.eqRefl _))
  have power := (RationalReciprocalPowerTail.term_at (Γ := Γ) two N i).eqTrans
    (fraction_congr (.eqRefl _) square)
  exact (scaled_term (Γ := Γ) RationalReciprocalPowerTail.body i (fraction C one)
      (RationalReciprocalPowerTail.data two N)).eqTrans
    ((multiply_congr (.eqRefl _) power).eqTrans
      ((fraction_multiply C one one (k*k) (le_refl one) (positive_product _ _ hk hk)).eqTrans
        (fraction_congr ((mul_comm C one).eqTrans (one_mul C)) (one_mul _))))

private theorem potential_two (N : PTm n) : Γ ⊢[PRAAx] potential two N ≐ fraction one N :=
  fraction_congr (.eqRefl _) ((congrMul (pred_succ one) (congrAp2 powF (pred_succ one) (.eqRefl N))).eqTrans
    ((one_mul _).eqTrans (pw_one N)))

theorem scalar_tail (C N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (RationalFiniteSum.sum scalarBody r (scalarData C N)) (fraction C N) := by
  let c := fraction C one
  have rep := fraction_represents (Γ := Γ) C one (le_refl one)
  have hc := GaussianRationalL1.nonnegative_of_representation c C one (le_refl one) rep
  have line := sum_homogeneous (Γ := Γ) RationalReciprocalPowerTail.body r c (RationalReciprocalPowerTail.data two N)
  have top := (multiply_congr (.eqRefl c) (potential_two (Γ := Γ) N)).eqTrans
    ((fraction_multiply C one one N (le_refl one) hN).eqTrans
      (fraction_congr ((mul_comm C one).eqTrans (one_mul C)) (one_mul N)))
  exact rationalLE_congr line.eqSymm top
    (RationalArithmetic.multiply_monotone c _ _ hc (RationalReciprocalPowerTail.sharp_tail two N r (le_refl two) hN))

theorem finite_tail (f : PTm 2) (x C N r : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] rowBounds f x C N r) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum f r x) C N := by
  let M := RationalFiniteSum.sum scalarBody r (scalarData C N)
  have rows : Γ ⊢[PRAAx] termsMajorized f scalarBody r x (scalarData C N) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r) :: Γ.map Fm.shift
    let k := succ (s N+i)
    have hs : Δ ⊢[PRAAx] rowBounds f (s x) (s C) (s N) (s r) :=
      by simpa only [Δ,s,Fm.shift,Syn.shift,subst_rowBounds] using h.shift.wk
    have law : Δ ⊢[PRAAx] lt i (s r) ⟶ bounded (inst2 f i (s x)) (s C) (k*k) := by
      simpa only [rowBounds,k,Fm.subst_imp,subst_lt,GaussianRationalMetric.subst_bounded,subst_inst2,
        PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        using hs.allE i
    have hk : Δ ⊢[PRAAx] le one k := zero_lt_succ _
    have bound := fraction_majorized _ _ _ (positive_product _ _ hk hk) (.impE law Prf.hyp0)
    simpa only [termsMajorized,Δ,s,i,Syn.shift,subst_scalarData] using
      majorized_congr (.eqRefl _) (scalar_at (s C) (s N) i).eqSymm bound
  have a := sum_majorized f scalarBody r x (scalarData C N) rows
  have hM := RationalArgmin.denominator_positive (Γ := Γ) M
  have order := comparison_to_cleared M (fraction C N)
    (GaussianPositiveRealArithmetic.numerator M) C (denominatorOf M) N
    (GaussianPositiveRealArithmetic.natural_representation M a.andE₁) (fraction_represents _ _ hN)
    (scalar_tail C N r hN)
  exact bounded_radius_mono _ _ _ _ _ hM hN
    (le_congr (mul_comm _ _) (.eqRefl _) order) a.andE₂

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayTail

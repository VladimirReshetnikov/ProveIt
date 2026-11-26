import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumConstants
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# The rational observation of the original power-sum moment

The left grid average is the original natural power sum divided by
M^(p+1). Its exact rational value lies below 1/(p+1), with a gap
bounded by 1/M. The exponent and mesh width are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPowerMoments

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents subst_fraction)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr multiply_congr multiply_associative)
open RationalArgmin (rationalLE rationalLE_congr rationalEq_congr)
open RationalArithmetic (multiply)
open RationalFiniteSum (term sum termwiseEq sum_ext)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalRepresentedUpper (from_signed)
open RationalSumConstants (count_add)
open RationalValueBounds (upper upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def integerBody : PTm 2 := fraction (pw (var 0) (var 1)) one
def rationalBody : PTm 2 := fraction (pw (var 0) (fstT (var 1))) (pw (sndT (var 1)) (fstT (var 1)))
def naturalSum (p M : PTm n) : PTm n := ap2 (sumF PowerSums.Bq) M p
def average (p M : PTm n) : PTm n := fraction (naturalSum p M) (pw M (succ p))
def moment (p : PTm n) : PTm n := fraction one (succ p)
def gridAverage (p M : PTm n) : PTm n := multiply (fraction one M) (sum rationalBody M (pairT p M))

ipra_subst naturalSum

private theorem integer_at (i p : PTm n) : term integerBody i p = fraction (pw i p) one := by
  simp [term,integerBody,inst2,pw,one]

private theorem rational_at (i p M : PTm n) :
    Γ ⊢[PRAAx] term rationalBody i (pairT p M) ≐ fraction (pw i p) (pw M p) := by
  have a := fst_pair (Γ := Γ) p M
  have b := snd_pair (Γ := Γ) p M
  simpa [term,rationalBody,inst2,pw] using
    fraction_congr (congrAp2 powF a (.eqRefl i)) (congrAp2 powF a b)

theorem integer_sum (p M : PTm n) :
    Γ ⊢[PRAAx] sum integerBody M p ≐ fraction (naturalSum p M) one := by
  have all : Γ ⊢[PRAAx] .all (sum integerBody (var 0) (Syn.shift p) ≐ fraction (naturalSum (Syn.shift p) (var 0)) one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have step := (RationalFiniteSum.sum_zero (Γ := Γ) integerBody p).eqTrans RationalReciprocalPowerTail.zero_fraction.eqSymm
      have e := (fraction_congr (LeanProofs.IPRA.sum_zero (Γ := Γ) PowerSums.Bq p) (.eqRefl one)).eqSymm
      simpa [Syn.inst_zero,Syn.subst_inst_shift,naturalSum,one] using step.eqTrans e
    · let i : PTm (n+1) := var 0
      let q := Syn.shift p
      simp only [Fm.subst_eq,RationalFiniteSum.subst_sum,GaussianEuclideanDistanceName.subst_fraction,subst_naturalSum,Syn.subst_var,
        Syn.repl_zero,subst_repl_shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
      let IH : Fm PTm (n+1) := sum integerBody i q ≐ fraction (naturalSum q i) one
      let Δ := IH :: Γ.map Fm.shift
      have step : Δ ⊢[PRAAx] naturalSum q (succ i) ≐ naturalSum q i+pw i q :=
        (LeanProofs.IPRA.sum_succ PowerSums.Bq i q).eqTrans
          (congrAdd (.eqRefl _) (show Δ ⊢[PRAAx] inst2 PowerSums.Bq i q ≐ pw i q by
            rw [PowerSums.inst2_B]
            exact .eqRefl _))
      have source := (RationalFiniteSum.sum_succ (Γ := Δ) integerBody i q).eqTrans
        (add_congr (Prf.hyp0 : Δ ⊢[PRAAx] IH) (.eqRefl _))
      rw [integer_at] at source
      exact source.eqTrans ((count_add (naturalSum q i) (pw i q)).eqTrans (fraction_congr step.eqSymm (.eqRefl one)))
  simpa only [Fm.subst_eq,RationalFiniteSum.subst_sum,GaussianEuclideanDistanceName.subst_fraction,subst_naturalSum,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using all.allE M

set_option maxHeartbeats 600000 in
theorem literal_average (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] gridAverage p M ≐ average p M := by
  let d := pw M p
  let z := fraction one d
  let L := RationalSumLinearity.scaledBody integerBody
  let a := pairT p M
  let b := pairT z p
  have hd := GaussianFactorBudget.power_positive M p hM
  have row : Γ ⊢[PRAAx] termwiseEq rationalBody L M a b := by
    refine .allI (.impI ?_)
    let i : PTm (n+1) := var 0
    let q := Syn.shift p
    let W := Syn.shift M
    let Δ := lt i W :: Γ.map Fm.shift
    let x := pw i q
    let v := fraction one (pw W q)
    have hW : Δ ⊢[PRAAx] le one W := by
      apply Prf.wk
      simpa [W,Fm.shift,Syn.shift,one] using hM.shift
    have hv := GaussianFactorBudget.power_positive W q hW
    have f : Δ ⊢[PRAAx] multiply v (fraction x one) ≐ fraction x (pw W q) :=
      (fraction_multiply one (pw W q) x one hv (le_refl one)).eqTrans (fraction_congr (one_mul x) (by ipra_ring))
    have e := (RationalSumLinearity.scaled_term (Γ := Δ) integerBody i v q).eqTrans (by rw [integer_at]; exact f)
    simpa only [a,b,z,d,q,W,i,v,L,Syn.shift,pw,one,Δ,subst_pairT,subst_fraction,subst_ap2,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using rationalEq_congr (rational_at (Γ := Δ) i q W).eqSymm e.eqSymm (.eqRefl _)
  have bound := (sum_ext _ _ _ _ _ row).eqTrans ((RationalSumLinearity.sum_homogeneous integerBody M z p).eqTrans
    (multiply_congr (.eqRefl z) (integer_sum p M)))
  have D : Γ ⊢[PRAAx] le one (M*d) := positive_product _ _ hM hd
  have eD : Γ ⊢[PRAAx] M*d*one ≐ pw M (succ p) :=
    (mul_comm (M*d) one).eqTrans ((one_mul _).eqTrans ((mul_comm M d).eqTrans (pw_succ M p).eqSymm))
  exact (multiply_congr (.eqRefl _) bound).eqTrans ((multiply_associative _ _ _).eqSymm.eqTrans
    ((multiply_congr (fraction_multiply one M one d hM hd) (.eqRefl _)).eqTrans
      ((fraction_multiply _ _ _ _ D (le_refl one)).eqTrans (fraction_congr (by ipra_ring) eD))))

theorem moment_error (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] rationalLE (average p M) (moment p) ⋏ upper (moment p) (average p M) one M := by
  let x := naturalSum p M
  let E := pw M (succ p)
  let Q := succ p
  have hE := GaussianFactorBudget.power_positive M (succ p) hM
  have hQ := zero_lt_succ (Γ := Γ) p
  have base := PowerSums.moment (Γ := Γ) p M
  have low : Γ ⊢[PRAAx] rationalLE (average p M) (moment p) :=
    GaussianRationalMetric.comparison_of_cleared (fraction x E) (moment p) x one E Q hE hQ
      (fraction_represents _ _ hE) (fraction_represents _ _ hQ)
      (le_congr (.eqRefl _) (one_mul E).eqSymm base.andE₁)
  have high : Γ ⊢[PRAAx] upper (moment p) (average p M) one M := by
    apply from_signed _ _ (ZT.ofNat one) (ZT.ofNat x) Q E one M hQ hE
      (fraction_represents _ _ hQ) (fraction_represents _ _ hE)
    let k := monus (Q*x+Q*pw M p) E
    have diff : Γ ⊢[PRAAx] Q*x+Q*pw M p ≐ E+k := eq_add_of_le base.andE₂
    have diffValue := natEq diff
    have step := natEq (pw_succ (Γ := Γ) M p)
    apply zle_of_toZ (M*k)
    simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
    dsimp only [x,E,Q] at diffValue ⊢
    linear_combination -𝔞 M*diffValue-𝔞 (succ p)*step
  exact .andI low high

theorem actual_rational_power_moment_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ rationalLE (average (var 0) (var 1)) (moment (var 0)) ⋏
      upper (moment (var 0)) (average (var 0) (var 1)) one (var 1)) :=
  closeUniv 2 (.impI (moment_error _ _ Prf.hyp0))

theorem actual_literal_rational_power_grid_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ rationalLE (gridAverage (var 0) (var 1)) (moment (var 0)) ⋏
      upper (moment (var 0)) (gridAverage (var 0) (var 1)) one (var 1)) := by
  refine closeUniv 2 (.impI ?_)
  let p : PTm 2 := var 0
  let M : PTm 2 := var 1
  have f := literal_average (Γ := [le one M]) p M Prf.hyp0
  have e := moment_error (Γ := [le one M]) p M Prf.hyp0
  exact .andI (rationalLE_congr f.eqSymm (.eqRefl _) e.andE₁)
    (upper_congr (.eqRefl _) f.eqSymm (.eqRefl _) (.eqRefl _) e.andE₂)

end LeanProofs.IPRA.Analysis.RationalPowerMoments

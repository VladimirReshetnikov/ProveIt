import IPRADerivations.Analysis.Trigonometry.GaussianSineProductHeadLower
import IPRADerivations.Analysis.FiniteOperations.GaussianInverseSquareProductGrowth
import IPRADerivations.Analysis.Names.Rates.GaussianApproximateInverseDistance
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductAlgebra

/-!
# Uniform lower bound for the actual finite sine-product tails

After L ≥ 2R, each inverse factor is within 2R²/k² of one. The checked
inverse-square product envelope bounds the product of these actual
reciprocals by 2^(4R²). Exact finite cancellation therefore gives a
lower bound 2^(-4R²) for every suffix, regardless of its length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductTailLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerReflectionHead (body squareFactor square_factor_at)
open GaussianInverseSquareProductTail (factorBounds sine_factor_bound)
open GaussianSineProductHeadLower (lower_one)
open GaussianRationalLowerBounds (lower inverse_bound name_lower)
open GaussianRationalReciprocal (qone reciprocal reciprocal_canonical reciprocal_identity)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianBoundedInverseApartness (lower_near_one factor_lower)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalFiniteProduct (qprod offset_at)
open GaussianRationalProductAlgebra (multiplyBody multiply_body_at product_multiply oneTerms product_one_of_terms)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseBody : PTm 2 := reciprocal (offB body)

def inversePrefix (z B L r : PTm n) : PTm n := qprod inverseBody r (pairT L (pairT z B))

theorem factor_at (z B L i : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB body) i (pairT L (pairT z B)) ≐ squareFactor (L+i) z B :=
  (offset_at body L i (pairT z B)).eqTrans (square_factor_at _ _ _)

theorem inverse_at (z B L i : PTm n) :
    Γ ⊢[PRAAx] inst2 inverseBody i (pairT L (pairT z B)) ≐ reciprocal (squareFactor (L+i) z B) := by
  simpa only [inverseBody,inst2,GaussianRationalReciprocal.subst_reciprocal] using
    GaussianNameReciprocal.reciprocal_congr (factor_at z B L i)

theorem late_factor (z R B L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] lower (squareFactor (L+i) z B) one two := by
  let k := succ (L+i)
  let q := squareFactor (L+i) z B
  have hk : Γ ⊢[PRAAx] le (two*R) k :=
    le_trans hL (le_trans (le_add_right L i) (le_succ_self (L+i)))
  have k2 : Γ ⊢[PRAAx] le one (k*k) := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have c1 : Γ ⊢[PRAAx] le ((R*R)*two) ((two*R)*(two*R)) :=
    le_of_eq_add (d := two*(R*R)) (by ipra_ring)
  have cmp : Γ ⊢[PRAAx] le ((R*R)*two) (one*(k*k)) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans c1 (le_mul_mono hk hk))
  exact lower_near_one q (distance_radius_mono _ _ _ _ _ _ k2 (zero_lt_succ one) cmp
    (sine_factor_bound (L+i) z R B hB hz))

theorem late_inverse_identity (z R B L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] qmul (squareFactor (L+i) z B) (reciprocal (squareFactor (L+i) z B)) ≐ qone := by
  have twoPos : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  exact reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ _ twoPos
    (name_lower _ _ _ (le_refl one) twoPos (late_factor z R B L i hB hz hL)))

theorem inverse_deviation (z R B L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] distanceBounded (inst2 inverseBody i (pairT L (pairT z B))) qone (two*(R*R)) (succ i*succ i) := by
  let k := succ (L+i)
  let q := squareFactor (L+i) z B
  let v := reciprocal q
  have k2 : Γ ⊢[PRAAx] le one (k*k) := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have j2 : Γ ⊢[PRAAx] le one (succ i*succ i) := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have j : Γ ⊢[PRAAx] le (succ i) k :=
    le_congr (by ipra_ring) (by dsimp only [k]; ipra_ring) (add_le_add₂ (le_add_left i L) (le_refl one))
  have hv : Γ ⊢[PRAAx] bounded v two one :=
    inverse_bound q one two (le_refl one) (zero_lt_succ one) (late_factor z R B L i hB hz hL)
  have e : Γ ⊢[PRAAx] qmul v q ≐ qone :=
    (qmul_commutative v q).eqTrans (late_inverse_identity z R B L i hB hz hL)
  have close := multiply_distance v qone q two (R*R) (k*k) k2 hv
    (distance_symmetric _ _ _ _ k2 (sine_factor_bound (L+i) z R B hB hz))
  have atK : Γ ⊢[PRAAx] distanceBounded (inst2 inverseBody i (pairT L (pairT z B))) qone (two*(R*R)) (k*k) :=
    distance_congr ((qmul_one_right v (reciprocal_canonical _)).eqTrans (inverse_at z B L i).eqSymm)
      e (.eqRefl _) (.eqRefl _) close
  have cmp : Γ ⊢[PRAAx] le ((two*(R*R))*(succ i*succ i)) ((two*(R*R))*(k*k)) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (two*(R*R)) (le_mul_mono j j))
  exact distance_radius_mono _ _ _ _ _ _ k2 j2 cmp atK

theorem inverse_bound_all (z R B L r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] bounded (inversePrefix z B L r) (unit (two*(two*(R*R)))) one := by
  apply GaussianInverseSquareProductGrowth.uniform_bound inverseBody (pairT L (pairT z B)) (two*(R*R)) r
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have hl : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using hL.shift
  refine .allI ?_
  have e : Γ.map Fm.shift ⊢[PRAAx] (Syn.shift (zero : PTm n)+var 0) ≐ var 0 := by
    simpa only [Syn.shift,ConciseIPRA.PTm.subst_zero] using zero_add (Γ := Γ.map Fm.shift) (var 0)
  have j := Prf.eqCongr (Γ := Γ.map Fm.shift) (Ax := PRAAx)
    (inst2 inverseBody (var 0) (var 1) : PTm 2)
    (σ := ![Syn.shift (zero : PTm n)+var 0,pairT (Syn.shift L) (pairT (Syn.shift z) (Syn.shift B))])
    (σ' := ![var 0,pairT (Syn.shift L) (pairT (Syn.shift z) (Syn.shift B))])
    (fun i => by fin_cases i; exact e; exact .eqRefl _)
  have je : Γ.map Fm.shift ⊢[PRAAx]
      inst2 inverseBody (Syn.shift (zero : PTm n)+var 0) (pairT (Syn.shift L) (pairT (Syn.shift z) (Syn.shift B))) ≐
        inst2 inverseBody (var 0) (pairT (Syn.shift L) (pairT (Syn.shift z) (Syn.shift B))) := by
    simpa only [subst_inst2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using j
  have h := distance_congr je.eqSymm (.eqRefl _) (.eqRefl _)
    (congrMul (congrSucc e.eqSymm) (congrSucc e.eqSymm))
    (inverse_deviation (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift L) (var 0) hb hd hl)
  simpa only [factorBounds,Syn.shift,subst_pairT,PTm.subst_mul,two,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,GaussianRationalReciprocal.qone,GaussianRationalSyntheticDivision.qone] using h

theorem inverse_product (z R B L r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] qmul (GaussianInverseSquareProductTail.product body L r (pairT z B)) (inversePrefix z B L r) ≐ qone := by
  let x := pairT L (pairT z B)
  let t := multiplyBody (offB body) inverseBody
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have hl : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift L) := by simpa [Fm.shift,Syn.shift] using hL.shift
  have terms : Γ ⊢[PRAAx] oneTerms t r x := by
    refine .allI (.impI ?_)
    simpa only [oneTerms,t,x,Syn.shift,subst_pairT,multiply_body_at,GaussianRationalReciprocal.qone,
      GaussianRationalSyntheticDivision.qone] using
      (qmul_congr (factor_at (Syn.shift z) (Syn.shift B) (Syn.shift L) (var 0))
        (inverse_at (Syn.shift z) (Syn.shift B) (Syn.shift L) (var 0))).eqTrans
        (late_inverse_identity (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift L) (var 0) hb.wk hd.wk hl.wk)
  exact (product_multiply (offB body) inverseBody r x).eqSymm.eqTrans (product_one_of_terms t r x terms)

theorem tail_lower (z R B L r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hL : Γ ⊢[PRAAx] le (two*R) L) :
    Γ ⊢[PRAAx] lower (GaussianInverseSquareProductTail.product body L r (pairT z B))
      one (unit (two*(two*(R*R)))) := by
  have p := inverse_product z R B L r hB hz hL
  have hq := GaussianRationalLowerBounds.lower_congr p.eqSymm (.eqRefl _) (.eqRefl _) lower_one
  exact GaussianRationalLowerBounds.lower_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (factor_lower _ _ _ _ _ (le_refl _) (unit_positive _) hq (inverse_bound_all z R B L r hB hz hL))

theorem actual_sine_product_tail_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶ le (two*var 1) (var 3) ⟶
      lower (GaussianInverseSquareProductTail.product body (var 3) (var 4) (pairT (var 0) (var 2)))
        one (unit (two*(two*(var 1*var 1))))) :=
  closeUniv 5 (.impI (.impI (.impI (tail_lower _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineProductTailLower

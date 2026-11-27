import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleFiniteFactors
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianMeshLogSign

/-!
# Exact inverse of the original pole factor product

The rational multiplier for the local Gamma formula is the inverse step,
the signed inverse factorial, and the actual finite product of inverse
normalized factors. Positivity of the checked distances licenses every
reciprocal on the punctured unit disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleMultiplier

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaLocalPoleGuards (center localMargin translated_pole_left)
open GaussianGammaPoleFiniteFactors
  (factor factorBody factor_at factorProduct signedFactorial centered_rising_factorization)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul qmul_canonical
  qmul_represents canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRationalMetric (qnegative_represents)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRationalReciprocal (reciprocal reciprocal_identity power power_zero power_succ)
open GaussianRationalLowerBounds (lower lower_from_representation name_lower)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianGammaEulerHeadLower (poleAt translated_zero)
open ComplexLogarithmRemainder (oneCode normSq_neg normSq scale bounded)
open GaussianRootAlgebra (equal equal_of_values normSq_equal re_mul im_mul re_neg im_neg re_one im_one)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseFactorBody : PTm 2 := reciprocal factorBody
def inverseFactorProduct (h B j : PTm n) : PTm n := qprod inverseFactorBody j (pairT h B)
def signedInverseFactorial (j : PTm n) : PTm n := qmul (power minusOne j) (ofGaussian oneCode (fact j))
def multiplier (h B j : PTm n) : PTm n :=
  qmul (reciprocal (ofGaussian h B)) (qmul (signedInverseFactorial j) (inverseFactorProduct h B j))

ipra_subst inverseFactorProduct

theorem factor_lower (h B A S D j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hj : Γ ⊢[PRAAx] le one j)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] lower (factor h B j) A (D*j) := by
  let c := center h B j
  let E := B*j
  let F := D*j
  have he := positive_product _ _ hB hj
  have hf := positive_product _ _ hD hj
  have guard : Γ ⊢[PRAAx] poleAt c B A D zero := translated_pole_left h B A S D j zero hm hh hj
  have eq := (normSq_equal (translated_zero (Γ := Γ) c B)).eqTrans (normSq_neg c).eqSymm
  have old : Γ ⊢[PRAAx] le ((A*B)*(A*B)) (D*D*normSq (ComplexLogarithmRemainder.neg c)) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) eq) guard
  exact lower_from_representation (factor h B j) (ComplexLogarithmRemainder.neg c) E A F he hf
    (ofGaussian_represents _ _ he)
    (le_congr (by unfold E; ipra_ring) (by unfold F; ipra_ring)
      (mul_le_mul_right (j*j) old))

private theorem inverse_of_lower (q A D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hq : Γ ⊢[PRAAx] lower q A D) :
    Γ ⊢[PRAAx] qmul q (reciprocal q) ≐ qone :=
  reciprocal_identity q (GaussianNameReciprocal.lower_norm_positive _ _ hD (name_lower q A D hA hD hq))

theorem factor_inverse (h B A S D j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hj : Γ ⊢[PRAAx] le one j)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] qmul (factor h B j) (reciprocal (factor h B j)) ≐ qone :=
  inverse_of_lower _ _ _ hA (positive_product _ _ hD hj) (factor_lower h B A S D j hB hD hj hm hh)

theorem step_inverse (h B A S D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] qmul (ofGaussian h B) (reciprocal (ofGaussian h B)) ≐ qone :=
  inverse_of_lower _ _ _ hA hD
    (lower_from_representation _ _ _ _ _ hB hD (ofGaussian_represents _ _ hB)
      (le_congr (by ipra_ring) (.eqRefl _) hm.andE₂.andE₂))

private theorem reciprocal_congr {u v : PTm n} (e : Γ ⊢[PRAAx] u ≐ v) :
    Γ ⊢[PRAAx] reciprocal u ≐ reciprocal v := by
  ipra_congr (reciprocal (var 0) : PTm 1) with [e]

theorem inverseFactorProduct_succ (h B j : PTm n) : Γ ⊢[PRAAx] inverseFactorProduct h B (succ j) ≐
    qmul (inverseFactorProduct h B j) (reciprocal (factor h B (succ j))) := by
  have e := product_succ (Γ := Γ) inverseFactorBody j (pairT h B)
  have entry : Γ ⊢[PRAAx] inst2 inverseFactorBody j (pairT h B) ≐ reciprocal (factor h B (succ j)) := by
    simpa only [inverseFactorBody,inst2,GaussianRationalReciprocal.subst_reciprocal] using
      reciprocal_congr (factor_at (Γ := Γ) h B j)
  exact e.eqTrans (qmul_congr (.eqRefl _) entry)

def inverseLaw (h B j : PTm n) : Fm PTm n := qmul (factorProduct h B j) (inverseFactorProduct h B j) ≐ qone

ipra_subst inverseLaw

private theorem inverseLaw_zero (h B : PTm n) : Γ ⊢[PRAAx] inverseLaw h B zero :=
  (qmul_congr (product_zero factorBody (pairT h B)) (product_zero inverseFactorBody (pairT h B))).eqTrans
    (qmul_one_right _ qone_canonical)

private theorem inverseLaw_succ (h B A S D j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B))
    (ih : Γ ⊢[PRAAx] inverseLaw h B j) : Γ ⊢[PRAAx] inverseLaw h B (succ j) := by
  have e := qmul_congr (GaussianGammaPoleFiniteFactors.factor_succ (Γ := Γ) h B j)
    (inverseFactorProduct_succ h B j)
  exact e.eqTrans ((qmul_shuffle _ _ _ _).eqTrans
    ((qmul_congr ih (factor_inverse h B A S D (succ j) hB hA hD (zero_lt_succ j) hm hh)).eqTrans
      (qmul_one_right _ qone_canonical)))

theorem product_inverse (h B A S D j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] le (A+S) D) (hh : Γ ⊢[PRAAx] bounded (scale D h) (S*B)) :
    Γ ⊢[PRAAx] inverseLaw h B j := by
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have a : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
  have d : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have m : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A+Syn.shift S) (Syn.shift D) :=
    by simpa [Fm.shift,Syn.shift] using hm.shift
  have u : Γ.map Fm.shift ⊢[PRAAx] bounded (scale (Syn.shift D) (Syn.shift h)) (Syn.shift S*Syn.shift B) :=
    by simpa [Fm.shift,Syn.shift,bounded] using hh.shift
  have all : Γ ⊢[PRAAx] .all (inverseLaw (Syn.shift h) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_inverseLaw]
    · exact inverseLaw_zero h B
    · exact inverseLaw_succ _ _ _ _ _ _ b.wk a.wk d.wk m.wk u.wk Prf.hyp0
  simpa only [subst_inverseLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

private theorem minusOne_square : Γ ⊢[PRAAx] qmul (minusOne : PTm n) minusOne ≐ qone := by
  let o : PTm n := oneCode
  let no := ComplexLogarithmRemainder.neg o
  have r := qnegative_represents qone o one (ofGaussian_represents (Γ := Γ) o one (le_refl _))
  have same : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul no no) o := by
    apply equal_of_values <;> simp only [no,o,re_mul,im_mul,re_neg,im_neg,re_one,im_one] <;> ring
  have p := qmul_represents (minusOne : PTm n) minusOne no no one one (le_refl one) (le_refl one) r r
  exact canonical_unique _ _ _ one (qmul_canonical _ _) qone_canonical (le_refl _)
    (represents_congr (.eqRefl _) same (one_mul _) p) (ofGaussian_represents _ _ (le_refl _))

def signSquare (j : PTm n) : Fm PTm n := qmul (power minusOne j) (power minusOne j) ≐ qone

ipra_subst signSquare

theorem sign_square (j : PTm n) : Γ ⊢[PRAAx] signSquare j := by
  have all : Γ ⊢[PRAAx] .all (signSquare (var 0)) := by
    ipra_qfind [subst_signSquare]
    · exact (qmul_congr (power_zero minusOne) (power_zero minusOne)).eqTrans (qmul_one_right _ qone_canonical)
    · exact (qmul_congr (power_succ minusOne _) (power_succ minusOne _)).eqTrans
        ((qmul_shuffle _ _ _ _).eqTrans ((qmul_congr Prf.hyp0 minusOne_square).eqTrans
          (qmul_one_right _ qone_canonical)))
  simpa only [subst_signSquare,Syn.subst_var,Syn.inst_zero] using all.allE j

theorem signed_factorial_inverse (j : PTm n) : Γ ⊢[PRAAx]
    qmul (signedFactorial j) (signedInverseFactorial j) ≐ qone := by
  have inv := GaussianMeshLogSign.inverse_point_product (Γ := Γ) (fact j)
    (GaussianRationalPolynomialExponential.factorial_positive j)
  have exactProduct := (qmul_commutative (Γ := Γ) _ _).eqTrans inv
  exact (qmul_shuffle _ _ _ _).eqTrans ((qmul_congr (sign_square j) exactProduct).eqTrans
    (qmul_one_right _ qone_canonical))

theorem actual_pole_multiplier_inverse (h B A S D j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] qmul (GaussianGammaRepeatedShift.risingProduct (center h B j) B (succ j)) (multiplier h B j) ≐ qone := by
  have cut := centered_rising_factorization h B j hB
  have outer := step_inverse h B A S D hB hA hD hm
  have inner := (qmul_shuffle (Γ := Γ) _ _ _ _).eqTrans
    ((qmul_congr (signed_factorial_inverse j) (product_inverse h B A S D j hB hA hD hm.andE₁ hm.andE₂.andE₁)).eqTrans
      (qmul_one_right _ qone_canonical))
  exact (qmul_congr cut (.eqRefl _)).eqTrans
    ((qmul_shuffle _ _ _ _).eqTrans ((qmul_congr outer inner).eqTrans (qmul_one_right _ qone_canonical)))

theorem original_pole_multiplier_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 4) ⟶ localMargin (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      qmul (GaussianGammaRepeatedShift.risingProduct (center (var 0) (var 1) (var 5)) (var 1) (succ (var 5)))
        (multiplier (var 0) (var 1) (var 5)) ≐ qone) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (actual_pole_multiplier_inverse _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleMultiplier

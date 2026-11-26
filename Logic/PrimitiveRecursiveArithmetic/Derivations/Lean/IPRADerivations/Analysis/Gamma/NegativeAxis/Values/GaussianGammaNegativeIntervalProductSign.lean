import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivative
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Inequalities.GaussianRationalNonnegativeFractions
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialTangent
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsLog

/-!
# Sign and separation of the original rising product on each negative interval

At a/b-(N+1), the first N+1 factors are negative and the last is a/b.
After multiplying by (-1)^(N+1), the reversed negative prefix has
positive factors i-a/b. Its first factor is (b-a)/b and each later
factor is at least one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalProductSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianFactorBudget (power_positive)
open GaussianGammaLocalPoleGuards (center)
open GaussianGammaPoleFiniteFactors (difference differenceBody differenceProduct difference_succ)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteProduct (product_zero)
open GaussianRationalHorner (qmul ofGaussian_canonical ofGaussian_represents canonical_unique represents_congr
  positive_product qmul_canonical)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents)
open GaussianRationalNonnegativeFractions (fraction_nonnegative)
open GaussianRationalNonnegativeProducts (nonnegative)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianReciprocalHorner (qmul_one_right qmul_associative)
open GaussianRootAlgebra (equal_of_values re_add im_add re_neg im_neg re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg)
open RationalArgmin (rationalLE rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def magnitudeBody : PTm 2 := monus (sndT (var 1)*succ (var 0)) (fstT (var 1))
def magnitude (a b j : PTm n) : PTm n := ap2 (prodF magnitudeBody) j (pairT a b)

def signUnit (j : PTm n) : PTm n := power minusOne j

def signedProduct (a b N : PTm n) : PTm n :=
  qmul (signUnit (succ N)) (risingProduct (center (arg a) b (succ N)) b (succ (succ N)))

def lowerPoint (a b : PTm n) : PTm n := fraction (a*monus b a) (b*b)

@[simp] theorem subst_magnitude {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    Syn.subst σ (magnitude a b j) = magnitude (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [magnitude]

@[simp] theorem subst_signUnit {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (signUnit j) = signUnit (Syn.subst σ j) := by simp [signUnit, minusOne]

@[simp] theorem subst_signedProduct {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (signedProduct a b N) = signedProduct (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [signedProduct]

@[simp] theorem subst_lowerPoint {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (lowerPoint a b) = lowerPoint (Syn.subst σ a) (Syn.subst σ b) := by simp [lowerPoint]

private theorem magnitude_zero (a b : PTm n) : Γ ⊢[PRAAx] magnitude a b zero ≐ one :=
  prod_zero magnitudeBody (pairT a b)

private theorem magnitude_succ (a b j : PTm n) :
    Γ ⊢[PRAAx] magnitude a b (succ j) ≐ magnitude a b j*monus (b*succ j) a := by
  have e : Γ ⊢[PRAAx] Syn.subst ![j,pairT a b] magnitudeBody ≐ monus (b*succ j) a := by
    simpa only [magnitudeBody, PTm.subst_monus, PTm.subst_mul, PTm.subst_succ, subst_sndT, subst_fstT,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
      congrMonus (congrMul (snd_pair (Γ := Γ) a b) (.eqRefl (succ j))) (fst_pair a b)
  exact (prod_succ magnitudeBody j (pairT a b)).eqTrans (congrMul (.eqRefl _) e)

private theorem oriented_factor (a b j : PTm n) (hB : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] qmul minusOne (difference (arg a) b (succ j)) ≐ fraction (monus (b*succ j) a) b := by
  let z := center (arg a) b (succ j)
  let q := difference (arg a) b (succ j)
  let v := monus (b*succ j) a
  have h : Γ ⊢[PRAAx] le a (b*succ j) := by ipra_le sl hab+𝔞 b*𝔞 j
  have e := natEq (eq_add_of_le h)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.neg z) (arg v) := by
    apply equal_of_values
    · simp only [z, center, arg, GaussianGammaPoleZeros.poleNumerator, re_add, re_neg, re_scale, re_one]
      ipra_simps
      linear_combination e
    · simp only [z, center, arg, GaussianGammaPoleZeros.poleNumerator, im_add, im_neg, im_scale, im_one]
      ipra_simps
      ring
  have raw := qnegative_represents q z b (ofGaussian_represents z b hB)
  exact (negative_as_minusOne q).eqSymm.eqTrans
    (canonical_unique _ _ (arg v) b (qnegative_canonical _) (ofGaussian_canonical _ _ hB) hB
      (represents_congr (.eqRefl _) same (.eqRefl _) raw) (ofGaussian_represents _ _ hB))

private def prefixLaw (a b j : PTm n) : Fm PTm n :=
  qmul (signUnit j) (differenceProduct (arg a) b j) ≐ fraction (magnitude a b j) (pw b j)

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (a b j : PTm n) :
    (prefixLaw a b j).subst σ = prefixLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [prefixLaw]

private theorem prefix_zero (a b : PTm n) : Γ ⊢[PRAAx] prefixLaw a b zero := by
  have x := qmul_congr (power_zero (Γ := Γ) (minusOne : PTm n)) (product_zero differenceBody (pairT (arg a) b))
  have e := GaussianCompactRiemannName.fraction_congr (Γ := Γ) _ _ _ _ (magnitude_zero a b) (pw_zero b)
  exact (x.eqTrans (qmul_one_right _ qone_canonical)).eqTrans
    ((e.eqTrans (GaussianRationalExponentialTangent.fraction_one one (le_refl one))).eqSymm)

private theorem prefix_succ (a b j : PTm n) (hB : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) (ih : Γ ⊢[PRAAx] prefixLaw a b j) :
    Γ ⊢[PRAAx] prefixLaw a b (succ j) := by
  let q := differenceProduct (arg a) b j
  let r := difference (arg a) b (succ j)
  have h := (qmul_congr (power_succ (Γ := Γ) minusOne j) (difference_succ (arg a) b j)).eqTrans
    (qmul_shuffle (signUnit j) minusOne q r)
  have e := (qmul_congr ih (oriented_factor a b j hB hab)).eqTrans
    (fraction_product _ _ _ _ (power_positive b j hB) hB)
  exact h.eqTrans (e.eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _
    (magnitude_succ a b j).eqSymm (pw_succ b j).eqSymm))

private theorem prefix_value (a b j : PTm n) (hB : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] prefixLaw a b j := by
  have pb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hB.shift
  have ab : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hab.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using prefix_zero (Γ := Γ) a b
    · simpa only [subst_prefixLaw, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        prefix_succ (Syn.shift a) (Syn.shift b) (var 0) pb.wk ab.wk Prf.hyp0
  simpa only [subst_prefixLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE j

theorem fraction_readback (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx]
    signedProduct a b N ≐ fraction (magnitude a b (succ N)*a) (pw b (succ N)*b) := by
  let j := succ N
  have hB := le_trans ha (le_of_lt hab)
  have h := (qmul_congr (.eqRefl (signUnit j))
    (GaussianGammaNegativeProductDerivative.rising_product (arg a) b j hB)).eqTrans
      (qmul_associative (signUnit j) (differenceProduct (arg a) b j) (fraction a b)).eqSymm
  exact h.eqTrans ((qmul_congr (prefix_value a b j hB (le_of_lt hab)) (.eqRefl _)).eqTrans
    (fraction_product _ _ _ _ (power_positive b j hB) hB))

private def magnitudeLower (a b N : PTm n) : Fm PTm n :=
  le (monus b a*pw b N) (magnitude a b (succ N))

@[simp] private theorem subst_magnitudeLower {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    (magnitudeLower a b N).subst σ = magnitudeLower (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [magnitudeLower]

private theorem magnitude_lower_zero (a b : PTm n) : Γ ⊢[PRAAx] magnitudeLower a b zero := by
  have e := (magnitude_succ (Γ := Γ) a b zero).eqTrans ((congrMul (magnitude_zero a b)
    (congrMonus (by ipra_ring) (.eqRefl a))).eqTrans (one_mul _))
  have f : Γ ⊢[PRAAx] monus b a ≐ monus b a*pw b zero :=
    (by ipra_ring : Γ ⊢[PRAAx] monus b a ≐ monus b a*one).eqTrans (congrMul (.eqRefl _) (pw_zero b).eqSymm)
  exact le_congr f e.eqSymm (le_refl (monus b a))

private theorem magnitude_lower_succ (a b N : PTm n) (hab : Γ ⊢[PRAAx] le a b)
    (ih : Γ ⊢[PRAAx] magnitudeLower a b N) : Γ ⊢[PRAAx] magnitudeLower a b (succ N) := by
  let t := b*succ (succ N)
  have h : Γ ⊢[PRAAx] le (a+b) t := by
    change Γ ⊢[PRAAx] le (a+b) (b*succ (succ N))
    ipra_le sl hab+𝔞 b*𝔞 N
  have e : Γ ⊢[PRAAx] t ≐ a+monus t a := eq_add_of_le (le_trans (le_add_right _ _) h)
  have factor : Γ ⊢[PRAAx] le b (monus t a) :=
    le_of_add_le_add_right (c := a)
      (le_congr (add_comm _ _) (e.eqTrans (add_comm _ _)) h)
  have step := le_mul_mono ih factor
  refine le_congr ?_ (magnitude_succ a b (succ N)).eqSymm step
  have pow := natEq (pw_succ (Γ := Γ) b N)
  apply deriveNat
  ipra_simps
  rw [pow]
  ring

private theorem magnitude_lower (a b N : PTm n) (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] magnitudeLower a b N := by
  have ab : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hab.shift
  have all : Γ ⊢[PRAAx] .all (magnitudeLower (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_magnitudeLower, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using
        magnitude_lower_zero (Γ := Γ) a b
    · simpa only [subst_magnitudeLower, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        magnitude_lower_succ (Syn.shift a) (Syn.shift b) (var 0) ab.wk Prf.hyp0
  simpa only [subst_magnitudeLower, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE N

theorem product_sign (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] nonnegative (signedProduct a b N) ⋏
      rationalLE (fstT (lowerPoint a b)) (fstT (signedProduct a b N)) := by
  let c := magnitude a b (succ N)*a
  let d := pw b (succ N)*b
  have hB := le_trans ha (le_of_lt hab)
  have dpos : Γ ⊢[PRAAx] le one d := positive_product _ _ (power_positive _ _ hB) hB
  have e := fraction_readback a b N ha hab
  have h := magnitude_lower a b N (le_of_lt hab)
  have clear : Γ ⊢[PRAAx] le (d*(a*monus b a)) (c*(b*b)) := by
    apply le_congr ?_ (by dsimp only [c]; ipra_ring) (mul_le_mul_right (a*(b*b)) h)
    have pwStep := natEq (pw_succ (Γ := Γ) b N)
    apply deriveNat
    dsimp only [d]
    ipra_simps
    rw [pwStep]
    ring
  have order := GaussianStirlingMultiplicativeBoundsLog.fractions_order _ _ _ _
    (positive_product _ _ hB hB) dpos clear
  exact .andI (GaussianRationalNonnegativeProducts.congr e.eqSymm (fraction_nonnegative c d dpos))
    (rationalLE_congr (.eqRefl _) (congrFst e).eqSymm order)

theorem uniform_separation (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction one (b*b))) (fstT (signedProduct a b N)) := by
  let d := b*b
  have hb := le_trans ha (le_of_lt hab)
  have hd := positive_product _ _ hb hb
  have hg := positive_product _ _ ha (GaussianEulerUnitLogarithmicMargin.gap_positive a b hab)
  have h : Γ ⊢[PRAAx] le (d*one) ((a*monus b a)*d) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right d hg)
  exact RationalArgmin.transitive
    (GaussianStirlingMultiplicativeBoundsLog.fractions_order _ _ _ _ hd hd h) (product_sign a b N ha hab).andE₂

theorem actual_negative_interval_original_product_sign_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ lt (var 0) (var 1)) ⟶
        (nonnegative (signedProduct (var 0) (var 1) (var 2)) ⋏
          rationalLE (fstT (lowerPoint (var 0) (var 1))) (fstT (signedProduct (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (product_sign _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_negative_interval_original_product_separation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ lt (var 0) (var 1)) ⟶
        rationalLE (fstT (fraction one (var 1*var 1))) (fstT (signedProduct (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (uniform_separation _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalProductSign

import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductName
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Finite logarithmic derivative of the literal sine product on the imaginary axis

At a rational argument iA/B, each original Euler factor has the positive
value 1+(A/B)^2/j^2. The derivative recurrence for the original finite
product factors as the product times the literal sum of its rational
logarithmic derivative rows, including at A=0.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryLogDerivative

open_ipra
open ComplexLogarithmRemainder (code eval_im_code eval_re_code im mul re scale)
open GaussianGammaEulerReflectionHead (sineProduct squareFactor)
open GaussianRationalFiniteProduct (product_zero)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product
    qadd qmul qmul_canonical qmul_represents qzero represents_congr)
open GaussianRationalMetric (qsub_canonical qsub_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qmul_zero_right qmul_zero_left qzero_canonical rescale_to)
open GaussianReciprocalHorner (qadd_zero_right qmul_associative)
open GaussianRootAlgebra (equal_of_values im_mul im_scale im_sub re_mul re_scale re_sub)
open GaussianSineProductName (sine_product_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def axisNumerator (A : PTm n) : PTm n := code (ZT.ofNat zero) (ZT.ofNat A)
def realNumerator (A : PTm n) : PTm n := code (ZT.ofNat A) (ZT.ofNat zero)
def rationalReal (A B : PTm n) : PTm n := ofGaussian (realNumerator A) B
def squareDenominator (i B : PTm n) : PTm n := (B*succ i)*(B*succ i)
def factor (i A B : PTm n) : PTm n := squareFactor i (axisNumerator A) B
def product (A B N : PTm n) : PTm n := sineProduct (axisNumerator A) B N

def factorDerivative (i A B : PTm n) : PTm n :=
  rationalReal (two*A*B) (squareDenominator i B)

def logarithmRow (i A B : PTm n) : PTm n :=
  rationalReal (two*A*B) (squareDenominator i B+A*A)

private def logarithmBody : PTm 2 := logarithmRow (var 0) (fstT (var 1)) (sndT (var 1))
def logarithmSum (A B N : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum logarithmBody N (pairT A B)

private def derivativeBody : PTm 3 :=
  let i : PTm 3 := var 0
  let D : PTm 3 := var 1
  let A := fstT (var 2 : PTm 3)
  let B := sndT (var 2 : PTm 3)
  qadd (qmul D (factor i A B)) (qmul (product A B i) (factorDerivative i A B))

def derivativeF : PR 2 := rec2 (qzero : PTm 1) derivativeBody
def derivative (A B N : PTm n) : PTm n := ap2 derivativeF N (pairT A B)

ipra_subst axisNumerator [ZT.subst, ZT.ofNat]

ipra_subst realNumerator [ZT.subst, ZT.ofNat]

ipra_subst rationalReal

ipra_subst squareDenominator

ipra_subst factor

ipra_subst product [sineProduct]

ipra_subst factorDerivative [two]

ipra_subst logarithmRow [two]

ipra_subst logarithmSum

ipra_subst derivative

theorem factor_value (i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] factor i A B ≐ rationalReal (squareDenominator i B+A*A) (squareDenominator i B) := by
  let X := axisNumerator A
  let J := B*succ i
  let E := squareDenominator i B
  have hJ : Γ ⊢[PRAAx] le one J := positive_product _ _ hB (zero_lt_succ _)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hJ hJ
  have hz := ofGaussian_represents (Γ := Γ) X J hJ
  have hsq := qmul_represents _ _ _ _ _ _ hJ hJ hz hz
  have fact := qsub_represents _ _ _ _ E hE (qone_represents_scaled E) hsq
  have tar := ofGaussian_represents (Γ := Γ) (realNumerator (E+A*A)) E hE
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (ofGaussian_canonical _ _ hE) hE (hrv := tar)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := fact)
  apply equal_of_values <;>
    simp only [re_sub, im_sub, re_scale, im_scale, re_mul, im_mul, GaussianRootAlgebra.re_one, GaussianRootAlgebra.im_one,
      X, axisNumerator, realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem factor_derivative (i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (factor i A B) (logarithmRow i A B) ≐ factorDerivative i A B := by
  let E := squareDenominator i B
  let T := E+A*A
  let W := two*A*B
  have hJ : Γ ⊢[PRAAx] le one (B*succ i) := positive_product _ _ hB (zero_lt_succ _)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hJ hJ
  have hT : Γ ⊢[PRAAx] le one T := le_trans hE (le_add_right _ _)
  have hD := positive_product E T hE hT
  have lhs := qmul_represents _ _ _ _ _ _ hE hT
    (ofGaussian_represents (realNumerator T) E hE) (ofGaussian_represents (realNumerator W) T hT)
  have exactLeft := represents_congr (qmul_congr (factor_value i A B hB).eqSymm (.eqRefl _))
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _) lhs
  have rhs := rescale_to (factorDerivative i A B) (realNumerator W) E T (E*T)
    (ofGaussian_represents _ _ hE) (.eqRefl _)
  apply canonical_unique _ _ _ (E*T) (qmul_canonical _ _) (ofGaussian_canonical _ _ hE) hD (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := exactLeft)
  apply equal_of_values <;>
    simp only [re_mul, im_mul, re_scale, im_scale, realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

theorem derivative_zero (A B : PTm n) : Γ ⊢[PRAAx] derivative A B zero ≐ qzero := by
  simpa [derivative, derivativeF] using rec2_zero (Γ := Γ) (qzero : PTm 1) derivativeBody (pairT A B)

private theorem derivative_congr {v w i i' A A' B B' : PTm n}
    (hv : Γ ⊢[PRAAx] v ≐ w) (hi : Γ ⊢[PRAAx] i ≐ i')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    qadd (qmul v (factor i A B)) (qmul (product A B i) (factorDerivative i A B)) ≐
      qadd (qmul w (factor i' A' B')) (qmul (product A' B' i') (factorDerivative i' A' B')) := by
  simpa only [GaussianRationalHorner.subst_qadd, GaussianRationalHorner.subst_qmul, subst_factor,
    subst_product, subst_factorDerivative, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
        (qadd (qmul (var 0) (factor (var 1) (var 2) (var 3)))
          (qmul (product (var 2) (var 3) (var 1)) (factorDerivative (var 1) (var 2) (var 3))) : PTm 4)
        (σ := ![v,i,A,B]) (σ' := ![w,i',A',B']) (fun j => by fin_cases j; exacts [hv,hi,hA,hB])

theorem derivative_succ (A B N : PTm n) : Γ ⊢[PRAAx] derivative A B (succ N) ≐
    qadd (qmul (derivative A B N) (factor N A B)) (qmul (product A B N) (factorDerivative N A B)) := by
  have raw := rec2_succ (Γ := Γ) (qzero : PTm 1) derivativeBody N (pairT A B)
  have step : Γ ⊢[PRAAx]
      derivative A B (succ N) ≐
        qadd (qmul (derivative A B N) (factor N (fstT (pairT A B)) (sndT (pairT A B))))
          (qmul (product (fstT (pairT A B)) (sndT (pairT A B)) N)
            (factorDerivative N (fstT (pairT A B)) (sndT (pairT A B)))) := by
    simpa only [derivative, derivativeF, derivativeBody, inst3, GaussianRationalHorner.subst_qadd,
      GaussianRationalHorner.subst_qmul, subst_factor, subst_product, subst_factorDerivative, subst_fstT, subst_sndT,
      Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using raw
  exact step.eqTrans (derivative_congr (.eqRefl _) (.eqRefl _) (fst_pair _ _) (snd_pair _ _))

theorem logarithm_sum_succ (A B N : PTm n) : Γ ⊢[PRAAx] logarithmSum A B (succ N) ≐
    qadd (logarithmSum A B N) (logarithmRow N A B) := by
  apply (GaussianRationalFiniteSum.sum_succ logarithmBody N (pairT A B)).eqTrans
  apply qadd_congr (.eqRefl _)
  simpa only [logarithmBody, inst2, subst_logarithmRow, subst_fstT, subst_sndT,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (logarithmRow (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![N,fstT (pairT A B),sndT (pairT A B)]) (σ' := ![N,A,B])
        (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)

private def derivativeIdentity (A B N : PTm n) : Fm PTm n :=
  derivative A B N ≐ qmul (product A B N) (logarithmSum A B N)

@[simp] private theorem subst_derivativeIdentity {m : ℕ} (σ : Fin n → PTm m) (A B N : PTm n) :
    (derivativeIdentity A B N).subst σ = derivativeIdentity (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [derivativeIdentity]

private theorem identity_succ (A B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] derivativeIdentity A B N) : Γ ⊢[PRAAx] derivativeIdentity A B (succ N) := by
  let P := product A B N
  let F := factor N A B
  let S := logarithmSum A B N
  let W := logarithmRow N A B
  have commute : Γ ⊢[PRAAx] qmul (qmul P S) F ≐ qmul (qmul P F) S :=
    (qmul_associative P S F).eqTrans ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative S F)).eqTrans
      (qmul_associative P F S).eqSymm)
  have d := derivative_succ (Γ := Γ) A B N
  refine d.eqTrans ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans commute)
    ((qmul_congr (.eqRefl _) (factor_derivative N A B hB).eqSymm).eqTrans
      (qmul_associative P F W).eqSymm)).eqTrans ?_)
  exact (GaussianRationalCoefficientScaling.qmul_add (qmul P F) S W).eqSymm.eqTrans
    (qmul_congr (sine_product_succ (axisNumerator A) B N).eqSymm (logarithm_sum_succ A B N).eqSymm)

theorem finite_logarithmic_derivative (A B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] derivative A B N ≐ qmul (product A B N) (logarithmSum A B N) := by
  have h0 : Γ ⊢[PRAAx] derivativeIdentity A B zero :=
    (derivative_zero A B).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero logarithmBody (pairT A B))).eqTrans
        (qmul_zero_right _)).eqSymm
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift, one] using hB.shift
  have full : Γ ⊢[PRAAx] .all (derivativeIdentity (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_derivativeIdentity, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h0
    · simpa only [subst_derivativeIdentity, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        identity_succ (Syn.shift A) (Syn.shift B) (var 0) hs.wk Prf.hyp0
  have final : Γ ⊢[PRAAx] derivativeIdentity A B N := by
    simpa only [subst_derivativeIdentity, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using full.allE N
  exact final

theorem actual_finite_imaginary_sine_product_logarithmic_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶
        derivative (var 0) (var 1) (var 2) ≐
          qmul (product (var 0) (var 1) (var 2)) (logarithmSum (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (finite_logarithmic_derivative _ _ _ Prf.hyp0))

theorem denom_positive (i B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (squareDenominator i B) :=
  positive_product _ _ (positive_product _ _ hB (zero_lt_succ _)) (positive_product _ _ hB (zero_lt_succ _))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryLogDerivative

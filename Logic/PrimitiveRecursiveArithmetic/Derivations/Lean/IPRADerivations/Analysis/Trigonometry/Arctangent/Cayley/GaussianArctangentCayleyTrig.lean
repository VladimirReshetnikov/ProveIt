import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.GaussianArctangentCayleyStep
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineFromExponential

/-!
# Exact trigonometric readback of the Cayley fraction

The conjugate Cayley value is its reciprocal. The sine difference and
cosine sum produce their respective real rational codes at the literal
Cayley denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyTrig

open_ipra
open ComplexLogarithmRemainder (code oneCode scale normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (numerator denominator denominator_positive value imaginaryCode exact_square_norm)
open GaussianArctangentCayleyStep (conjugateValue)
open GaussianNamedSineFromExponential (multiplier)
open GaussianRationalHorner (qadd qmul ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  qadd_represents qmul_canonical qmul_represents represents_congr represents_rescale positive_product)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled conjugate re_conjugate im_conjugate)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_sub im_sub re_mul im_mul
  re_scale im_scale re_one im_one re_neg im_neg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sineCode (M j : PTm n) : PTm n := code (ZT.ofNat (two*M*j)) (ZT.ofNat zero)
def cosineCode (M j : PTm n) : PTm n := code (ZT.ofNat (M*M)-ZT.ofNat (j*j)) (ZT.ofNat zero)
def sinePoint (M j : PTm n) : PTm n := ofGaussian (sineCode M j) (denominator M j)
def cosinePoint (M j : PTm n) : PTm n := ofGaussian (cosineCode M j) (denominator M j)
def cosineMultiplier : PTm n := ofGaussian oneCode two

ipra_subst sinePoint [sineCode, denominator]

ipra_subst cosinePoint [cosineCode, denominator]

ipra_subst cosineMultiplier

theorem conjugate_inverse (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (conjugateValue M j) (value M j) ≐ qone := by
  let a := numerator M j
  let d := denominator M j
  have hd := denominator_positive M j hM
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul (conjugate a) a) (scale (d*d) oneCode) := by
    apply equal_of_values
    · simp only [re_mul, re_conjugate, im_conjugate, re_scale, re_one]
      have square := natEq (exact_square_norm (Γ := Γ) M j)
      rw [normSq_eval, Q.mk_mul, map_mul] at square
      rw [Q.mk_mul, map_mul, mul_one]
      dsimp only [a,d]
      linear_combination square
    · simp only [im_mul, re_conjugate, im_conjugate, im_scale, im_one]
      ring
  have rep := qmul_represents _ _ (conjugate a) a d d hd hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one))
    (positive_product _ _ hd hd) (represents_congr (.eqRefl _) e (.eqRefl _) rep) (qone_represents_scaled _)

theorem sine_readback (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul multiplier (qsub (value M j) (conjugateValue M j)) ≐ sinePoint M j := by
  let a := numerator M j
  let d := denominator M j
  let ni := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have hd := denominator_positive M j hM
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have dif := qsub_represents (value M j) (conjugateValue M j) a (conjugate a) d hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  have prod := qmul_represents multiplier _ ni _ two d htwo hd (ofGaussian_represents _ _ htwo) dif
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul ni (GaussianRootAlgebra.sub a (conjugate a)))
      (scale two (sineCode M j)) := by
    dsimp only [a,ni]
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_neg, im_neg, re_sub, im_sub, re_conjugate, im_conjugate,
        re_scale, im_scale, sineCode, imaginaryCode, numerator, eval_re_code, eval_im_code, ZT.toZ_ofNat, ZT.toZ_sub] <;>
      ipra_simps <;> ring
  have target := represents_rescale (sinePoint M j) (sineCode M j) d two (ofGaussian_represents _ _ hd)
  exact canonical_unique _ _ _ (two*d) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd) (positive_product _ _ htwo hd)
    (represents_congr (.eqRefl _) e (.eqRefl _) prod)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _) target)

theorem cosine_readback (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul cosineMultiplier (qadd (value M j) (conjugateValue M j)) ≐ cosinePoint M j := by
  let a := numerator M j
  let d := denominator M j
  have hd := denominator_positive M j hM
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have add := qadd_represents (value M j) (conjugateValue M j) a (conjugate a) d hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  have prod := qmul_represents cosineMultiplier _ oneCode _ two d htwo hd (ofGaussian_represents _ _ htwo) add
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul oneCode (ComplexLogarithmRemainder.add a (conjugate a)))
      (scale two (cosineCode M j)) := by
    dsimp only [a]
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_one, im_one, re_add, im_add, re_conjugate, im_conjugate, re_scale, im_scale,
        cosineCode, numerator, eval_re_code, eval_im_code, ZT.toZ_ofNat, ZT.toZ_sub] <;>
      ipra_simps <;> ring
  have target := represents_rescale (cosinePoint M j) (cosineCode M j) d two (ofGaussian_represents _ _ hd)
  exact canonical_unique _ _ _ (two*d) (qmul_canonical _ _) (ofGaussian_canonical _ _ hd) (positive_product _ _ htwo hd)
    (represents_congr (.eqRefl _) e (.eqRefl _) prod)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _) target)

def linearCode (M j : PTm n) : PTm n := code (ZT.ofNat M) (ZT.ofNat j)
def linearPoint (M j : PTm n) : PTm n := ofGaussian (linearCode M j) one
def conjugateLinearPoint (M j : PTm n) : PTm n := ofGaussian (conjugate (linearCode M j)) one

/-- Clear the factor B-iA in the quotient (B+iA)/(B-iA). -/
theorem quotient_readback (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qmul (value M j) (conjugateLinearPoint M j) ≐ linearPoint M j := by
  let a := numerator M j
  let b := linearCode M j
  let d := denominator M j
  have hd := denominator_positive M j hM
  have hp := qmul_represents (value M j) (conjugateLinearPoint M j) a (conjugate b) d one hd (le_refl one)
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ (le_refl one))
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul a (conjugate b)) (scale d b) := by
    dsimp only [a,b,d]
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_conjugate, im_conjugate, re_scale, im_scale,
        linearCode, numerator, denominator, eval_re_code, eval_im_code, ZT.toZ_ofNat, ZT.toZ_sub] <;>
      ipra_simps <;> ring
  have target := represents_rescale (Γ := Γ) (linearPoint M j) b one d (ofGaussian_represents _ _ (le_refl one))
  exact canonical_unique _ _ _ d (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hd
    (represents_congr (.eqRefl _) e (by ipra_ring) hp)
    (represents_congr (.eqRefl _) (equal_refl _) (one_mul _) target)

theorem actual_Cayley_quotient_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ qmul (value (var 0) (var 1)) (conjugateLinearPoint (var 0) (var 1)) ≐
      linearPoint (var 0) (var 1)) :=
  closeUniv 2 (.impI (quotient_readback _ _ Prf.hyp0))

theorem actual_Cayley_trigonometric_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶
      ((qmul (conjugateValue (var 0) (var 1)) (value (var 0) (var 1)) ≐ qone) ⋏
        ((qmul multiplier (qsub (value (var 0) (var 1)) (conjugateValue (var 0) (var 1))) ≐ sinePoint (var 0) (var 1)) ⋏
          (qmul cosineMultiplier (qadd (value (var 0) (var 1)) (conjugateValue (var 0) (var 1))) ≐ cosinePoint (var 0) (var 1))))) :=
  closeUniv 2 (.impI (.andI (conjugate_inverse _ _ Prf.hyp0)
    (.andI (sine_readback _ _ Prf.hyp0) (cosine_readback _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyTrig

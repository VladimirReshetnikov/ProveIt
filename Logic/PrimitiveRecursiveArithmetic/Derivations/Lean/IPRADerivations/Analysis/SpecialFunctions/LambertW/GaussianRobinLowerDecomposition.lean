import IPRADerivations.Analysis.SpecialFunctions.LambertW.GaussianRobinLogRangeReduction

/-!
# The original Robin lower logarithm as two rational terms

At every numerical cutoff the stored lower endpoint is exactly the
original binary exponent times the fixed odd sum, plus the odd sum at the
computed reduced fraction. The equality retains the actual numerators
and denominators used by the Robin sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinLowerDecomposition

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb Bt dt st c3 loN loD)
open GaussianRobinLogarithmParity (native)
open GaussianRobinOddLogarithmName (stored)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents ofGaussian_canonical qadd qmul qadd_canonical qadd_represents
    qmul_represents represents represents_congr canonical_unique positive_product)
open GaussianRationalSyntheticDivision (rescale_to qadd_congr qmul_congr)
open ComplexLogarithmRemainder (scale)
open GaussianRootAlgebra
  (equal_of_values re_scale im_scale re_one im_one re_add im_add re_mul im_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fraction (a b : PTm n) : PTm n := RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction a b)
def lower (a b K : PTm n) : PTm n := fraction (loN a b K) (loD a b K)
def exponentPoint (a b : PTm n) : PTm n := ofGaussian (native (eb a b)) one
def decomposition (a b K : PTm n) : PTm n :=
  qadd (qmul (exponentPoint a b) (stored K one c3)) (stored K (dt a b) (st a b))

theorem fraction_native (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] fraction a b ≐ ofGaussian (native a) b := by
  have hp := RationalGaussianEmbedding.embed_from_representation (RationalCubeMidpoint.fraction a b)
    (ZT.ofNat a) b (RationalIntegerNormalization.normalize_preserves_value (ZT.ofNat a) b hb)
  have he : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (RationalGaussianEmbedding.native (ZT.ofNat a)) (native a) := by
    apply equal_of_values <;>
      simp only [native,RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,re_scale,im_scale,re_one,im_one,ZT.toZ_ofNat] <;>
      (try ipra_simps) <;> ring
  exact GaussianRationalHorner.cleared_input_exact _ _ _ (RationalGaussianEmbedding.embed_canonical _) hb
    (represents_congr (.eqRefl _) he (.eqRefl _) hp)

theorem original_lower_decomposition (a b K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (ha : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    lower a b K ≐ decomposition a b K := by
  let e := eb a b
  let c := Nz K one c3
  let d := Dz K one c3
  let u := Nz K (dt a b) (st a b)
  let v := Dz K (dt a b) (st a b)
  let E := d*v
  let f := qmul (exponentPoint a b) (ofGaussian (native c) d)
  let g := ofGaussian (native u) v
  have h3 : Γ ⊢[PRAAx] le one (c3 : PTm n) := le_of_eq_add (d := two) (by ipra_ring)
  have hs := (GaussianRobinLogRangeReduction.reduced_source a b hb ha).andE₁
  have hd := GaussianRobinOddLogarithm.denominator_positive one c3 K h3
  have hv := GaussianRobinOddLogarithm.denominator_positive (dt a b) (st a b) K hs
  have hE := positive_product _ _ hd hv
  have raw := qmul_represents _ _ _ _ _ _ (le_refl one) hd
    (ofGaussian_represents (native e) one (le_refl _)) (ofGaussian_represents (native c) d hd)
  have inner : Γ ⊢[PRAAx] represents f (native (e*c)) d := by
    refine represents_congr (.eqRefl _) ?_ (one_mul _) raw
    apply equal_of_values <;> simp only [native,re_scale,im_scale,re_one,im_one,re_mul,im_mul] <;>
      (try ipra_simps) <;> ring
  have first := rescale_to f (native (e*c)) d v E inner (.eqRefl _)
  have second := rescale_to g (native u) v d E (ofGaussian_represents _ _ hv) (mul_comm _ _)
  have outer := qadd_represents f g _ _ E hE first second
  have nativeSum : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (scale v (native (e*c))) (scale d (native u))) (native (loN a b K)) := by
    apply equal_of_values <;>
      simp only [native,re_scale,im_scale,re_one,im_one,re_add,im_add,loN,e,c,d,u,v] <;>
      (try ipra_simps) <;> ring
  have r := (GaussianRationalHorner.cleared_input_exact (qadd f g) (native (loN a b K)) E (qadd_canonical _ _) hE
    (represents_congr (.eqRefl _) nativeSum (.eqRefl _) outer)).eqSymm
  exact (fraction_native (loN a b K) E hE).eqTrans
    (r.eqTrans (qadd_congr (qmul_congr (.eqRefl _) (fraction_native c d hd).eqSymm)
      (fraction_native u v hv).eqSymm))

theorem original_Robin_lower_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶
      lower (var 0) (var 1) (var 2) ≐ decomposition (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_lower_decomposition _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRobinLowerDecomposition

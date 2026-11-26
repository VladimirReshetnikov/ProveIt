import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderKernel

/-!
# Exact first centered Bernoulli kernel identity

The first centered sample is t(1-t) on the original grid. Its product
with the reciprocal-square weight has the signed partial-fraction
decomposition needed to identify the first integral with the original
logarithmic difference. This is an identity of literal rational codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderBernoulliMesh (homogeneous toZ_value)
open GaussianStirlingAllOrderCenteredBernoulli
  (sample numerator denominator factor sample_canonical sample_value denominator_positive)
open GaussianStirlingAllOrderKernel (row rowWeight offset offset_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open BernoulliBounds (bden bint toZ_zint)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem degree_two_value {R : Type*} [CommRing R] (x y : R) :
    homogeneous 2 x y = 4*y^2-24*x*y+24*x^2 := by
  have h0 : bint 2 0 = 4 := by
    norm_num [bint,bden,BernoulliCoefficients.bc,Finset.sum_range_succ,Finset.prod_range_succ]
  have h1 : bint 2 1 = -24 := by
    norm_num [bint,bden,BernoulliCoefficients.bc,Finset.sum_range_succ,Finset.prod_range_succ]
  have h2 : bint 2 2 = 24 := by
    norm_num [bint,bden,BernoulliCoefficients.bc,Finset.sum_range_succ,Finset.prod_range_succ]
  unfold homogeneous
  rw [Fin.sum_univ_three]
  change ((bint 2 0 : ℤ) : R)*x^0*y^2+((bint 2 1 : ℤ) : R)*x^1*y^1+((bint 2 2 : ℤ) : R)*x^2*y^0 = _
  rw [h0,h1,h2]
  push_cast
  ring

theorem first_sample (r M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] sample 1 r M ≐ fraction (r*monus M r) (M*M) := by
  have hD := denominator_positive 1 M hM
  have hMM := positive_product M M hM hM
  have d : bden 2 = 48 := by
    norm_num [bden,BernoulliCoefficients.bc,Finset.sum_range_succ,Finset.prod_range_succ]
  have f : factor 1 = -2 := by decide
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (sample_canonical 1 r M hM) (normalize_well_formed _ _ hMM)
    (sample_value 1 r M hM) (fraction_represents _ _ hMM) hD hMM
  apply ZT.derive
  have er := natEq (eq_add_of_le hr)
  simp only [numerator,denominator,ZT.toZ_mul,ZT.toZ_sub,toZ_value,toZ_zint,ZT.toZ_ofNat,Nat.mul_one,
    degree_two_value,IPRA.Q.mk_zero,map_zero,IPRA.Q.mk_mul,map_mul,
    AnalyticNumberTheory.RobinThreePos.pw_lit,IPRA.Q.mk_num,map_natCast]
  norm_num [d,f] at er ⊢
  linear_combination (48*𝔞(r)*(𝔞(M))^2)*er

def base (A B M k r : PTm n) : PTm n := offset A B M k+B*r

/-- Signed numerator of the three partial-fraction contributions over their
common positive square denominator. -/
def splitNumerator (A B M k r : PTm n) : ZT n :=
  let U := A+B*k
  let D := base A B M k r
  ZT.ofNat ((two*U+B)*M*D) - ZT.ofNat (D*D+U*(U+B)*(M*M))

def splitRow (A B M k r : PTm n) : PTm n :=
  normalize (splitNumerator A B M k r) (base A B M k r*base A B M k r)

theorem first_kernel_decomposition (A B M k r : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] row 0 one A B M k r ≐ splitRow A B M k r := by
  let D := base A B M k r
  let P := B*M
  have hD : Γ ⊢[PRAAx] le one D := le_trans (offset_positive A B M k hA hM) (le_add_right _ _)
  have hDD := positive_product D D hD hD
  have hMM := positive_product M M hM hM
  have e : Γ ⊢[PRAAx] rowWeight one A B M k r ≐ fraction (P*P) (D*D) :=
    RationalNonnegativePowers.fraction_congr ((pw_succ P one).eqTrans (congrMul (pw_one P) (.eqRefl _)))
      ((pw_succ D one).eqTrans (congrMul (pw_one D) (.eqRefl _)))
  refine (RationalAlgebra.multiply_congr (first_sample r M hM hr) e).eqTrans ?_
  let Q := r*monus M r*(P*P)
  have eq := RationalNonnegativePowers.fraction_multiply (r*monus M r) (M*M) (P*P) (D*D) hMM hDD
  refine eq.eqTrans ?_
  have hden := positive_product (M*M) (D*D) hMM hDD
  apply RationalFiniteSum.canonical_equal (fraction Q (M*M*(D*D))) (splitRow A B M k r) _ _ _ _
    (normalize_well_formed _ _ hden) (normalize_well_formed _ _ hDD)
    (fraction_represents _ _ hden) (normalize_preserves_value _ _ hDD) hden hDD
  apply ZT.derive
  have er := natEq (eq_add_of_le hr)
  dsimp only [Q,P,D,splitNumerator,base,offset]
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination ((𝔞(B))^2*𝔞(r)*(𝔞(M))^2*
    ((𝔞(A)+𝔞(B)*𝔞(k))*𝔞(M)+𝔞(B)*𝔞(r))^2)*(-er)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanel

import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalRelativeTaylor
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalCubicName
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# Exact first-order cancellation for a Barnes logarithm row

After the two original factor corrections are included, the scaled
quadratic polynomial of the relative Mercator argument is the linear
term with the actual rational slope, plus the difference-of-squares
error. This is a literal Gaussian-rational equality.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add mul scale normSq_eval)
open ComplexLogarithmName (baseNumerator baseDenominator base_positive)
open GaussianBarnesCanonicalFactor (correction)
open GaussianBarnesCanonicalRelativeStep (source numerator denominator relative denominator_positive)
open GaussianBarnesCanonicalRelativeTaylor (step quadraticError)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents positive_product
  canonical_unique qadd qadd_canonical qadd_represents qmul qmul_canonical qmul_represents
  represents represents_congr represents_rescale)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity qone qone_represents_scaled
  conjugate scaled_conjugate_product re_conjugate im_conjugate)
open GaussianRationalSyntheticDivision (rescale_to qmul_congr qone_canonical)
open GaussianRootAlgebra (sub equal_of_values re_sub im_sub re_add im_add re_mul im_mul re_scale im_scale re_neg im_neg re_one im_one)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "base" => GaussianBarnesCanonicalFactor.base
local notation "row" => GaussianBarnesCanonicalDerivativeRow.value

def linearTerm (z h B k : PTm n) : PTm n := qmul (ofGaussian h B) (row z B k)
def localQuadratic (z h B k : PTm n) : PTm n :=
  qmul (radiusPoint k one) (GaussianBarnesCanonicalCubicName.base (numerator z h B k) (denominator z B k))
def correctionDifference (z h B k : PTm n) : PTm n := qsub (correction (add z h) B k) (correction z B k)

@[simp] theorem subst_linearTerm {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (linearTerm z h B k) = linearTerm (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [linearTerm]

@[simp] theorem subst_localQuadratic {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (localQuadratic z h B k) = localQuadratic (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [localQuadratic,one]

@[simp] theorem subst_correctionDifference {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (correctionDifference z h B k) =
      correctionDifference (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) := by simp [correctionDifference]

private theorem inverse_represents (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] represents (reciprocal (base z B k)) (scale (B*k) (conjugate (translated z B k))) (denominator z B k) := by
  let b := base z B k
  let d := B*k
  let a := translated z B k
  let E := denominator z B k
  let c := scale d (conjugate a)
  let v := ofGaussian c E
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hB hk
  have hE := denominator_positive z R B k hs.andE₁
  have hv := ofGaussian_represents (Γ := Γ) c E hE
  have p := qmul_represents b v a c d E hd hE (GaussianBarnesCanonicalBase.base_represents z B k hB hk) hv
  have e : Γ ⊢[PRAAx] qmul b v ≐ qone :=
    canonical_unique _ _ (scale (d*E) ComplexLogarithmRemainder.oneCode) _ (qmul_canonical _ _) qone_canonical
      (positive_product _ _ hd hE)
      (represents_congr (.eqRefl _) (scaled_conjugate_product a d) (.eqRefl _) p) (qone_represents_scaled _)
  have nz := GaussianNameReciprocal.lower_norm_positive b two (zero_lt_succ one)
    (GaussianBarnesCanonicalDerivativeRow.base_lower z R B k hs.andE₁)
  have left := (qmul_commutative (reciprocal b) b).eqTrans (reciprocal_identity b nz)
  have cancel := GaussianRationalInverseQuadraticAlgebra.cancel_nested_product (reciprocal b) b v (ofGaussian_canonical _ _ hE) left
  have eq : Γ ⊢[PRAAx] reciprocal b ≐ v :=
    (GaussianReciprocalHorner.qmul_one_right (reciprocal b) (GaussianRationalReciprocal.reciprocal_canonical b)).eqSymm.eqTrans
      ((qmul_congr (.eqRefl _) e.eqSymm).eqTrans cancel)
  exact represents_congr eq.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _) hv

private theorem correction_represents (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] represents (correction z B k) (sub (mul z z) (scale (two*(B*k)) z)) (B*(two*(B*k))) := by
  let d := B*k
  let t := two*d
  let u := ofGaussian z B
  let v := ofGaussian z t
  have hd := positive_product B k hB hk
  have ht := positive_product two d (zero_lt_succ one) hd
  have htB := positive_product B t hB ht
  have ur := ofGaussian_represents z B hB
  have vr := ofGaussian_represents z t ht
  exact qsub_represents (qmul u v) u (mul z z) (scale t z) (B*t) htB
    (qmul_represents _ _ _ _ _ _ hB ht ur vr) (represents_rescale u z B t ur)

theorem cancellation (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qadd (localQuadratic z h B k) (correctionDifference z h B k) ≐
      qadd (linearTerm z h B k) (quadraticError z h B k) := by
  let d := B*k
  let a := translated z B k
  let E := denominator z B k
  let D := two*(B*d*d*E*E)
  let e := numerator z h B k
  let v := add z h
  let b := radiusNumerator k
  let l := localQuadratic z h B k
  let c := correctionDifference z h B k
  let m := linearTerm z h B k
  let t := quadraticError z h B k
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have h2 : Γ ⊢[PRAAx] le one two := zero_lt_succ one
  have hd := positive_product B k hB hk
  have hd2 := positive_product d d hd hd
  have hE := denominator_positive z R B k hs.andE₁
  have hE2 := positive_product E E hE hE
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ h2 (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hB hd) hd) hE) hE)
  have lr := qmul_represents (radiusPoint k one) (GaussianBarnesCanonicalCubicName.base e E) b (baseNumerator e E) one
    (baseDenominator E) (le_refl one) (base_positive E hE) (radius_represents k one (le_refl one))
    (ofGaussian_represents _ _ (base_positive E hE))
  have l' := rescale_to l (mul b (baseNumerator e E)) (one*baseDenominator E) (B*d*d) D lr
    (by simp only [D,baseDenominator]; ipra_ring)
  let F := B*(two*d)
  let c₁ := sub (mul v v) (scale (two*d) v)
  let c₀ := sub (mul z z) (scale (two*d) z)
  have hF := positive_product B (two*d) hB (positive_product _ _ h2 hd)
  have cr := qsub_represents (correction v B k) (correction z B k) c₁ c₀ F hF
    (correction_represents v B k hB hk) (correction_represents z B k hB hk)
  have c' := rescale_to c (sub c₁ c₀) F (d*E*E) D cr (by simp only [D,F]; ipra_ring)
  let w := GaussianBarnesCanonicalDerivativeRow.offset z B k
  let γ := mul (mul z z) (scale d (conjugate a))
  have wr := qmul_represents w w z z d d hd hd (ofGaussian_represents z d hd) (ofGaussian_represents z d hd)
  have rr := qmul_represents (qmul w w) (reciprocal (base z B k)) (mul z z) (scale d (conjugate a)) (d*d) E
    hd2 hE wr (inverse_represents z h R B k H hs)
  have mr := qmul_represents (ofGaussian h B) (row z B k) h γ B (d*d*E) hB (positive_product _ _ hd2 hE)
    (ofGaussian_represents h B hB) rr
  have m' := rescale_to m (mul h γ) (B*(d*d*E)) (two*E) D mr (by simp only [D]; ipra_ring)
  let g := step h B k
  let j := relative z h B k
  let V := d*d*(E*E)
  have hV := positive_product _ _ hd2 hE2
  have ga := ofGaussian_represents h d hd
  have jb := ofGaussian_represents e E hE
  have gr := qmul_represents g g h h d d hd hd ga ga
  have jr := qmul_represents j j e e E E hE hE jb jb
  have gr' := rescale_to (qmul g g) (mul h h) (d*d) (E*E) V gr (.eqRefl _)
  have jr' := rescale_to (qmul j j) (mul e e) (E*E) (d*d) V jr (by simp only [V]; ipra_ring)
  let θ := sub (scale (E*E) (mul h h)) (scale (d*d) (mul e e))
  have zr := qsub_represents (qmul g g) (qmul j j) _ _ V hV gr' jr'
  have tr := qmul_represents (radiusPoint k two) (qsub (qmul g g) (qmul j j)) b θ two V h2 hV
    (radius_represents k two h2) zr
  have t' := rescale_to t (mul b θ) (two*V) B D tr (by simp only [D,V]; ipra_ring)
  have lhs := qadd_represents l c _ _ D hD l' c'
  have rhs := qadd_represents m t _ _ D hD m' t'
  apply canonical_unique _ _ _ D (qadd_canonical _ _) (qadd_canonical _ _) hD (hrv := rhs)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) lhs
  apply equal_of_values <;>
    simp only [c₁,c₀,v,γ,θ,b,a,E,e,d,radiusNumerator,baseNumerator,numerator,denominator,translated,
      re_add,im_add,re_sub,im_sub,re_mul,im_mul,re_scale,im_scale,re_neg,im_neg,re_conjugate,im_conjugate,re_one,im_one,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;>
    simp only [normSq_eval,re_add,im_add,re_scale,im_scale,re_one,im_one,Q.mk_mul,map_mul] <;> ring

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeAlgebra

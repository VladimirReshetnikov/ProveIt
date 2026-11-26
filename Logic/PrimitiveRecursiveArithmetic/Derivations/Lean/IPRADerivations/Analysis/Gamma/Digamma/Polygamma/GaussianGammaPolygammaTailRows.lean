import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineReflectionLower
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantPairAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalInvertibleNorm

/-!
# Pole-separated inverse powers in the polygamma tail

For a native Gaussian parameter z/B with radius R, each index j ≥ 2R
has |z/B + j| ≥ j/2. The literal reciprocal power therefore splits
into a factor 2^m and a normalized term of norm at most 1/j^m.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolygammaTailRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianDominantPairAlgebra (radiusPoint radius_power radius_bounded radius_multiply radius_one radius_congr)
open GaussianGammaEulerHeadLower (translated)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalLowerBounds (lower lower_from_representation inverse_bound)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power reciprocal bounded_power bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (z B j : PTm n) : PTm n := ofGaussian (translated z B j) B
def inverse (z B j : PTm n) : PTm n := reciprocal (argument z B j)
def term (z B j m : PTm n) : PTm n := power (inverse z B j) m
def halfInverse (z B j : PTm n) : PTm n := qmul (radiusPoint one two) (inverse z B j)
def normalizedTerm (z B j m : PTm n) : PTm n := power (halfInverse z B j) m
def weight (m : PTm n) : PTm n := radiusPoint (pw two m) one

@[simp] theorem subst_normalizedTerm {l : ℕ} (σ : Fin n → PTm l) (z B j m : PTm n) :
    Syn.subst σ (normalizedTerm z B j m) =
      normalizedTerm (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ m) := by
  simp [normalizedTerm,halfInverse,inverse,argument,one,two]

@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (z B j m : PTm n) :
    Syn.subst σ (term z B j m) = term (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ m) := by
  simp [term,inverse,argument]

private theorem distance_from_integer (z R B j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hj : Γ ⊢[PRAAx] le (two*R) j) : Γ ⊢[PRAAx]
    distanceBounded (ofGaussian (scale (B*j) oneCode) B) (argument z B j) j two := by
  let v := scale (B*j) oneCode
  let w := translated z B j
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub v w) (ComplexLogarithmRemainder.neg z) := by
    apply GaussianRootAlgebra.equal_of_values
    all_goals
      simp only [v,w,translated,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg]
      ring
  have norm := (GaussianRootAlgebra.normSq_equal e).eqTrans (ComplexLogarithmRemainder.normSq_neg z)
  apply (GaussianRationalMetric.bounded_difference_iff _ _ v w B j two hB (le_succ_self one)
    (ofGaussian_represents v B hB) (ofGaussian_represents w B hB)).iffMpr
  have b := AnalyticNumberTheory.PhiLower.le_mul_mono hj (le_refl B)
  unfold ComplexLogarithmRemainder.bounded at hz
  have scaled : Γ ⊢[PRAAx] le ((two*two)*normSq z) ((two*R*B)*(two*R*B)) :=
    le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right (two*two) hz)
  exact le_congr (congrMul (.eqRefl _) norm.eqSymm) (by ipra_ring)
    (le_trans scaled (AnalyticNumberTheory.PhiLower.le_mul_mono b b))

theorem argument_lower (z R B j : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hj : Γ ⊢[PRAAx] le (two*R) j) : Γ ⊢[PRAAx] lower (argument z B j) j two := by
  let v := scale (B*j) oneCode
  let q := ofGaussian v B
  have ht : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have norm : Γ ⊢[PRAAx] normSq v ≐ (B*j)*(B*j) :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have ref : Γ ⊢[PRAAx] lower q (two*j) two := by
    apply lower_from_representation _ v B _ _ hB ht (ofGaussian_represents v B hB)
    exact le_congr (by ipra_ring) (congrMul (.eqRefl _) norm.eqSymm) (le_refl (two*two*((B*j)*(B*j))))
  exact GaussianSineReflectionLower.lower_after_half_error q (argument z B j) j two ht ref
    (distance_from_integer z R B j hB hz hj)

theorem normalized_term_bound (z R B j m : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hj : Γ ⊢[PRAAx] le (two*R) j) (hp : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    bounded (normalizedTerm z B j m) one (pw j m) := by
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have bound := inverse_bound (argument z B j) j two hp h2 (argument_lower z R B j hB hz hj)
  have halfBound := bounded_product (radiusPoint one two) (inverse z B j) one two two j h2 hp
    (radius_bounded one two h2) bound
  have hhalf : Γ ⊢[PRAAx] bounded (halfInverse z B j) one j :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ h2 hp) hp
      (le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by ipra_ring)) halfBound
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power m) (.eqRefl _)
    (bounded_power _ one j m hp hhalf)

theorem term_factor (z B j m : PTm n) : Γ ⊢[PRAAx] term z B j m ≐ qmul (weight m) (normalizedTerm z B j m) := by
  let inv := inverse z B j
  let u : PTm n := radiusPoint two one
  let v : PTm n := radiusPoint one two
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have oneCodeEq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianDominantPairAlgebra.radiusNumerator two) (scale two oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianDominantPairAlgebra.radiusNumerator,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  have twoOverTwo : Γ ⊢[PRAAx] radiusPoint two two ≐ GaussianRationalReciprocal.qone :=
    GaussianRationalHorner.canonical_unique _ _ _ two
      (GaussianRationalHorner.ofGaussian_canonical _ _ h2)
      (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) h2
      (GaussianRationalHorner.represents_congr (.eqRefl _) oneCodeEq (.eqRefl _)
        (GaussianDominantPairAlgebra.radius_represents _ _ h2))
      (GaussianRationalReciprocal.qone_represents_scaled two)
  have unitLaw : Γ ⊢[PRAAx] qmul u v ≐ GaussianRationalReciprocal.qone :=
    (radius_multiply two one one two (le_refl one) h2).eqTrans
      ((radius_congr (by ipra_ring) (one_mul two)).eqTrans twoOverTwo)
  have e := GaussianRationalInvertibleNorm.qmul_roundtrip u v inv unitLaw
    (GaussianRationalReciprocal.reciprocal_canonical (argument z B j))
  have scale : Γ ⊢[PRAAx] power u m ≐ weight m := (radius_power two one m (le_refl one)).eqTrans
    (radius_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power m))
  exact (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl m) e.eqSymm).eqTrans
    ((GaussianRationalPowerAlgebra.power_product u (halfInverse z B j) m).eqTrans
      (qmul_congr scale (.eqRefl _)))

end LeanProofs.IPRA.Analysis.GaussianGammaPolygammaTailRows

import IPRADerivations.Analysis.GaussianRationalNonnegativeProducts
import IPRADerivations.Analysis.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.GaussianGammaHalfSqrtBrackets
import IPRADerivations.Analysis.GaussianNameArithmetic

/-!
# Exact natural-fraction readback of nonnegative real samples
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianRationalNonnegativeFractions

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalNonnegativeProducts (nonnegative nonnegative_mul)
open GaussianRationalHorner (canonical ofGaussian_canonical ofGaussian_represents scalar_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (sign natural_representation)
open RationalGaussianEmbedding (embed native scalarZero scalar_zero_represents)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalValueBounds (upper_of_order)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (q : PTm n) : PTm n := GaussianPositiveRealArithmetic.numerator (fstT q)
def denominator (q : PTm n) : PTm n := denominatorOf (fstT q)

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (numerator q) = numerator (Syn.subst σ q) := by
  simp [numerator,GaussianPositiveRealArithmetic.numerator,numeratorOf]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (q : PTm n) :
    Syn.subst σ (denominator q) = denominator (Syn.subst σ q) := by simp [denominator]

theorem denominator_positive (q : PTm n) : Γ ⊢[PRAAx] le one (denominator q) :=
  RationalArgmin.denominator_positive (fstT q)

private theorem scalar_sign (q : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q) : Γ ⊢[PRAAx] sign (fstT q) := by
  let a := fstT q
  let u := numeratorOf a
  let d := denominatorOf a
  have h := RationalRepresentedUpper.to_signed scalarZero a (ZT.ofNat zero) u one d zero one
    (scalar_zero_represents one) (RationalRepresentations.represents_self a)
    (upper_of_order scalarZero a zero one hq.andE₁)
  have s : Γ ⊢[PRAAx] zle (ZT.ofNat zero) u := by
    apply PolynomialBisection.zle_congr _ _ h
    · simp [RationalRepresentedUpper.left,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
    · simp [RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,
        map_one,IPRA.Q.mk_zero,map_zero]
  exact le_congr (zero_add u.neg) (add_zero u.pos) s

private theorem fraction_of_sign (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (axis : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis q) (hs : Γ ⊢[PRAAx] sign (fstT q)) :
    Γ ⊢[PRAAx] q ≐ fraction (numerator q) (denominator q) := by
  let a := numerator q
  let b := denominator q
  let u := fstT q
  have hb := denominator_positive (Γ := Γ) q
  have em := RationalGaussianEmbedding.embed_from_representation u (ZT.ofNat a) b
    (natural_representation u hs)
  have left := GaussianRationalHorner.represents_congr (.eqRefl _)
    (GaussianRootAlgebra.equal_of_values (b := ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode)
      (by simp [native,ComplexLogarithmRemainder.eval_re_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat])
      (by simp [native,ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]))
    (.eqRefl _) em
  exact (RationalGaussianEmbedding.canonical_axis_roundtrip q hc axis).eqSymm.eqTrans
    (GaussianRationalHorner.canonical_unique _ _ _ b (RationalGaussianEmbedding.embed_canonical u)
      (ofGaussian_canonical _ _ hb) hb left (ofGaussian_represents _ _ hb))

theorem fraction_at (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hq : Γ ⊢[PRAAx] nonnegative q) :
    Γ ⊢[PRAAx] q ≐ fraction (numerator q) (denominator q) :=
  fraction_of_sign q hc (RationalArgmin.rationalEq_congr hq.andE₂.eqSymm (.eqRefl _) (.eqRefl _)) (scalar_sign q hq)

theorem fraction_nonnegative (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] nonnegative (fraction A B) := by
  let q := fraction A B
  have hz : Γ ⊢[PRAAx] sndT q ≐ scalarZero :=
    (congrSnd (GaussianEulerDecayOrder.fraction_embedding A B hB).eqSymm).eqTrans (snd_pair _ _)
  refine .andI ?_ hz
  apply RationalArithmetic.order_of_representations scalarZero (fstT q) (ZT.ofNat zero) (ZT.ofNat A) one B
    (scalar_zero_represents one) (GaussianGammaHalfSqrtBrackets.fraction_first_represents A B hB) (le_refl one) hB
  apply zle_of_toZ A
  simp [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero,map_one]

theorem nonnegative_of_positive (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (h : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive q) : Γ ⊢[PRAAx] nonnegative q :=
  GaussianRationalNonnegativeProducts.congr (fraction_of_sign q hc h.andE₁ h.andE₂).eqSymm
    (fraction_nonnegative _ _ (denominator_positive q))

theorem multiply_nonnegative_at (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] nonnegative (ap2 f (GaussianFastValueCut.exponent (multiplyModulus f g x y) p) x))
    (hg : Γ ⊢[PRAAx] nonnegative (ap2 g (GaussianFastValueCut.exponent (multiplyModulus f g x y) p) y)) :
    Γ ⊢[PRAAx] nonnegative (ap2 (multiplyF f g) p (multiplyData f g x y)) := by
  let s := GaussianFastValueCut.exponent (multiplyModulus f g x y) p
  let a := ap2 f s x
  let b := ap2 g s y
  exact GaussianRationalNonnegativeProducts.congr
    ((multiply_at f g x y p).eqTrans (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical a b))).eqSymm
    (nonnegative_mul a b hf hg)

end LeanProofs.IPRA.Analysis.GaussianRationalNonnegativeFractions

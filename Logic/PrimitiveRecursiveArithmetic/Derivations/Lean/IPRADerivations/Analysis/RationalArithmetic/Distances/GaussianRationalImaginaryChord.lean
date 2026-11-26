import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalNormSquareTransport
import IPRADerivations.Analysis.Trigonometry.Sine.GaussianNamedSineFromExponential

/-!
# The real sine and squared imaginary chord of a rational sample

The real embedding of a complex sample's imaginary part equals the
literal sine multiplier applied to its conjugate difference. The
squared norm of the conjugate difference equals the square of twice
that real sine.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalImaginaryChord

open_ipra
open ComplexLogarithmRemainder (mul scale normSq im re)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianNamedSineFromExponential (multiplier)
open GaussianRationalNormSquareTransport (value actual_squared_norm)
open GaussianRationalConjugation (point point_represents)
open GaussianRationalHorner (qadd qmul canonical_unique qmul_canonical qadd_canonical qmul_represents
  qadd_represents positive_product represents_congr ofGaussian_represents scalar_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qnormSq_represents qsub_represents qnegative_represents
  bounded bounded_to_cleared bounded_of_cleared)
open GaussianRationalReciprocal (conjugate re_conjugate im_conjugate qone)
open GaussianRationalDistanceOrder (reversed_difference)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRootAlgebra (sub equal equal_of_values equal_refl re_mul im_mul re_add im_add re_sub im_sub re_scale im_scale
  re_neg im_neg)
open RationalGaussianEmbedding (embed embed_canonical embed_from_representation native)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sine (u : PTm n) : PTm n := embed (sndT u)
def twiceSine (u : PTm n) : PTm n := qadd (sine u) (sine u)

ipra_subst sine

ipra_subst twiceSine

theorem sine_recode (u : PTm n) :
    Γ ⊢[PRAAx] qmul multiplier (qsub u (point u)) ≐ sine u := by
  let a := rawGaussian u
  let E := rawDen u
  let hE := raw_den_positive (Γ := Γ) u
  let h2 : Γ ⊢[PRAAx] le one two := le_succ_self one
  let k := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  let b := sub a (conjugate a)
  have d := qsub_represents u (point u) a (conjugate a) E hE (raw_represents u)
    (point_represents _ _ _ hE (raw_represents u))
  have h := qmul_represents multiplier _ k b two E h2 hE (ofGaussian_represents _ _ h2) d
  have e : Γ ⊢[PRAAx] equal (mul k b) (scale two (native (im a))) := by
    dsimp only [k,b]
    apply equal_of_values <;> simp only [re_mul,im_mul,re_sub,im_sub,re_scale,im_scale,re_conjugate,
      im_conjugate,re_neg,im_neg,imaginaryCode,native,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  have target := GaussianRationalHorner.represents_rescale _ _ E two
    (embed_from_representation _ _ _ (raw_represents (Γ := Γ) u).andE₂)
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (embed_canonical _) (positive_product _ _ h2 hE)
    (represents_congr (.eqRefl _) e (.eqRefl _) h)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _) target)

theorem sine_bound (u A : PTm n) (hu : Γ ⊢[PRAAx] bounded u A one) :
    Γ ⊢[PRAAx] bounded (sine u) A one := by
  let a := rawGaussian u
  let E := rawDen u
  let hE := raw_den_positive (Γ := Γ) u
  have m : Γ ⊢[PRAAx] le (normSq (native (im a))) (normSq a) := by
    refine le_of_eq_add (d := normSq (native (re a))) ?_
    apply deriveNat
    simp only [IPRA.Q.mk_add,map_add,ComplexLogarithmRemainder.normSq_eval,native,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact bounded_of_cleared _ _ _ _ _ hE (le_refl one)
    (embed_from_representation _ _ _ (raw_represents (Γ := Γ) u).andE₂)
    (le_trans (le_mul_mono (le_refl _) m) (bounded_to_cleared _ _ _ _ _ hE (le_refl one) (raw_represents u) hu))

theorem conjugate_chord_square (u : PTm n) :
    Γ ⊢[PRAAx] value (qsub u (point u)) ≐ qmul (twiceSine u) (twiceSine u) := by
  let a := rawGaussian u
  let E := rawDen u
  let hE := raw_den_positive (Γ := Γ) u
  let b := sub a (conjugate a)
  let c := native (im a)
  let d := ComplexLogarithmRemainder.add c c
  have h := qsub_represents u (point u) a (conjugate a) E hE (raw_represents u)
    (point_represents _ _ _ hE (raw_represents u))
  have nr := embed_from_representation _ _ _ (qnormSq_represents _ _ _ hE h)
  have s := embed_from_representation _ _ _ (raw_represents (Γ := Γ) u).andE₂
  have db := qadd_represents _ _ _ _ _ hE s s
  have prod := qmul_represents (twiceSine u) (twiceSine u) d d E E hE hE db db
  have same : Γ ⊢[PRAAx] equal (native (ZT.ofNat (normSq b))) (mul d d) := by
    dsimp only [b,c,d]
    apply equal_of_values <;> simp only [re_mul,im_mul,re_add,im_add,re_sub,im_sub,re_conjugate,im_conjugate,native,
      ComplexLogarithmRemainder.normSq_eval,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact (actual_squared_norm _).eqTrans (canonical_unique _ _ _ _ (embed_canonical _) (qmul_canonical _ _)
    (positive_product _ _ hE hE) (represents_congr (.eqRefl _) same (.eqRefl _) nr) prod)

theorem reverse_chord_square (a b : PTm n) : Γ ⊢[PRAAx] value (qsub a b) ≐ value (qsub b a) := by
  let q := qsub a b
  let y := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have h := raw_represents (Γ := Γ) q
  have rev := represents_congr (reversed_difference a b) (equal_refl _) (.eqRefl _) (qnegative_represents _ _ _ h)
  have normEq := ComplexLogarithmRemainder.normSq_neg (Γ := Γ) y
  have nr := qnormSq_represents (qsub b a) _ E hE rev
  have e : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (normSq (ComplexLogarithmRemainder.neg y))) (ZT.ofNat (normSq y)) := by
    apply ZT.derive
    simpa [ZT.toZ_ofNat] using natEq normEq
  exact (actual_squared_norm _).eqTrans ((canonical_unique _ _ _ _ (embed_canonical _) (embed_canonical _)
    (positive_product _ _ hE hE) (embed_from_representation _ _ _ (qnormSq_represents _ _ _ hE h))
    (embed_from_representation _ _ _ (scalar_congr (.eqRefl _) e (.eqRefl _) nr))).eqTrans
      (actual_squared_norm _).eqSymm)

end LeanProofs.IPRA.Analysis.GaussianRationalImaginaryChord

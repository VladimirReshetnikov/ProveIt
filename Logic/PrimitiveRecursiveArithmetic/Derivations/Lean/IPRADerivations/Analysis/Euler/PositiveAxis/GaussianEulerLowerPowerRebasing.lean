import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerPowerCoefficients
import IPRADerivations.Analysis.Polynomials.GaussianInverseBinomialRows

/-!
# Exact lower-power multiplier and reciprocal harmonic samples

At A>=1 the actual doubled multiplier of 1/A-1, multiplied by A,
is literally the negative natural 2 pred(A). At every original harmonic
query the reciprocal fraction has the literal negated sample. These
are the finite code identities needed after the actual log power law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerRebasing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerPowerCoefficients (lowerMultiplier)
open GaussianRationalNaturalScale (naturalPoint natScale natural_point_represents)
open GaussianRationalHorner (qmul qadd canonical_unique qmul_represents qadd_represents represents_congr)
open GaussianRationalConjugation (point point_represents)
open GaussianRationalMetric (qnegative qnegative_represents)
open ComplexLogarithmRemainder (oneCode scale mul add neg)
open GaussianRationalReciprocal (conjugate re_conjugate im_conjugate)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_add im_add re_sub im_sub re_neg im_neg re_scale im_scale re_one im_one)
open RationalHarmonicInterval (common interval numerator horizon at_common common_value)
open RationalGaussianEmbedding (embed native)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponent (A : PTm n) : PTm n := two*pred A
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) : Syn.subst σ (exponent A) = exponent (Syn.subst σ A) := by simp [exponent]

theorem multiplier_times_A (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    qmul (lowerMultiplier A) (naturalPoint A) ≐ qnegative (naturalPoint (exponent A)) := by
  let s := GaussianRootAlgebra.sub oneCode (scale A oneCode)
  let g := ComplexLogarithmRemainder.neg (scale (exponent A) oneCode)
  have c := GaussianEulerIntegrandName.coefficient_represents (Γ := Γ) oneCode A hA
  have sum := qadd_represents _ _ _ _ A hA c (point_represents _ _ _ hA c)
  have product := qmul_represents _ _ _ _ A one hA (le_refl one) sum (natural_point_represents A)
  have same : Γ ⊢[PRAAx] equal (mul (add s (conjugate s)) (scale A oneCode)) (scale A g) := by
    have e := natEq (pos_of_eq_succ ((eq_add_of_le hA).eqTrans (by ipra_ring)))
    apply equal_of_values
    · simp only [re_mul,im_mul,re_add,im_add,re_conjugate,im_conjugate,s,g,re_sub,im_sub,re_scale,im_scale,re_neg,im_neg,re_one,im_one]
      unfold exponent
      ipra_simps
      rw [e]
      ring
    · simp only [im_mul,re_add,im_add,re_conjugate,im_conjugate,s,g,re_sub,im_sub,re_scale,im_scale,re_neg,im_neg,re_one,im_one]
      ipra_simps
      ring
  have cancelled := GaussianRationalHorner.represents_cancel _ g one A hA
    (represents_congr (.eqRefl _) same (mul_comm _ _) product)
  exact canonical_unique _ _ g one (GaussianRationalHorner.qmul_canonical _ _) (GaussianRationalMetric.qnegative_canonical _) (le_refl one)
    cancelled (qnegative_represents _ _ _ (natural_point_represents (exponent A)))

theorem reciprocal_interval (a b Q : PTm n) : Γ ⊢[PRAAx]
    qnegative (embed (interval a b Q)) ≐ embed (interval b a Q) := by
  let L := horizon a b Q+horizon b a Q
  let F := Products.fact L
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have e1 := at_common (Γ := Γ) a b Q L (le_add_right _ _)
  have e2 := at_common (Γ := Γ) b a Q L (le_add_left _ _)
  have left := qnegative_represents _ _ _
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (common_value (Γ := Γ) a b Q L))
  have right := RationalGaussianEmbedding.embed_from_representation _ _ _ (common_value (Γ := Γ) b a Q L)
  have same : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.neg (native (numerator a b Q L))) (native (numerator b a Q L)) := by
    apply equal_of_values
    · simp only [re_neg,native,ComplexLogarithmRemainder.eval_re_code]
      simp only [numerator,ZT.toZ]
      ring
    · simp only [im_neg,native,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  have mid := canonical_unique _ _ _ F (GaussianRationalMetric.qnegative_canonical _) (RationalGaussianEmbedding.embed_canonical _) hF
    (represents_congr (.eqRefl _) same (.eqRefl _) left) right
  have start := GaussianInverseBinomialRows.negative_congr (RationalGaussianRealPart.embed_congr e1).eqSymm
  exact start.eqTrans (mid.eqTrans (RationalGaussianRealPart.embed_congr e2))

theorem reciprocal_sample (p a b : PTm n) : Γ ⊢[PRAAx]
    qnegative (GaussianHarmonicLogarithmName.sample p a b) ≐ GaussianHarmonicLogarithmName.sample p b a :=
  (GaussianInverseBinomialRows.negative_congr (GaussianHarmonicLogarithmName.sample_at p a b)).eqTrans
    ((reciprocal_interval a b _).eqTrans (GaussianHarmonicLogarithmName.sample_at p b a).eqSymm)

theorem actual_lower_multiplier_integer_rebasing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ qmul (lowerMultiplier (var 0)) (naturalPoint (var 0)) ≐ qnegative (naturalPoint (exponent (var 0)))) :=
  closeUniv 1 (.impI (multiplier_times_A _ Prf.hyp0))
theorem actual_reciprocal_harmonic_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qnegative (GaussianHarmonicLogarithmName.sample (var 0) (var 1) (var 2)) ≐ GaussianHarmonicLogarithmName.sample (var 0) (var 2) (var 1)) :=
  closeUniv 3 (reciprocal_sample _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerRebasing

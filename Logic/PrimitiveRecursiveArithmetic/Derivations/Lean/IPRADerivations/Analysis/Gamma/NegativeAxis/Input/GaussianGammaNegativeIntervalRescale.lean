import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling

/-!
# Rescale the original negative-interval encoding

Rescaling the rational displacement preserves the interval and the
literal rational shift product. The original reciprocal Gamma names
retain their independently constructed apartness certificates.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianGammaEncodingRescaling (rescaled_source original_C7_rescale fraction_rescale)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaEulerHeadShift (linear)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalNative (argument data product negative_source)
open GaussianGammaReciprocalInverse (gammaF gammaHeight original_gamma_inverse)
open GaussianGammaRepeatedShift (risingProduct linearBody linear_at)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_to_diagonal)
open GaussianRationalHorner (positive_product)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_neg im_neg re_scale im_scale re_one im_one)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianGammaC7Name.nameF
local notation "pd" => GaussianGammaC7Name.data

theorem guard_rescale (a b D : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] guard (D*a) (D*b) := by
  refine .andI (positive_product _ _ hD ha.andE₁) ?_
  change Γ ⊢[PRAAx] le (succ (D*a)) (D*b)
  ipra_le 𝔞 D*sl ha.andE₂+sl hD

theorem scaled_argument (a b D N : PTm n) : Γ ⊢[PRAAx]
    equal (scale D (argument a b N)) (argument (D*a) (D*b) N) := by
  apply equal_of_values <;>
    simp only [argument, arg, GaussianGammaLocalPoleGuards.center, GaussianGammaPoleZeros.poleNumerator,
      re_add, im_add, re_neg, im_neg, re_scale, im_scale, re_one, im_one] <;>
    ipra_simps <;> ring

theorem original_rescale (a b D N : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF (data (D*a) (D*b) N) (data a b N) := by
  let z := argument a b N
  let w := argument (D*a) (D*b) N
  let R := succ (succ N)
  have hz := negative_source a b N ha
  have hw := negative_source (D*a) (D*b) N (guard_rescale a b D ha hD)
  have code := GaussianGammaInputProperness.original_C7_proper (scale D z) w R (D*b)
    (rescaled_source z R b D hz.andE₁ hD) (scaled_argument a b D N)
  have rescaled := original_C7_rescale z R b D hz.andE₁ hD
  have same := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ code) rescaled
  have left := (original_gamma_inverse w R (D*b) one (D*b) hw).andE₁
  have right := (original_gamma_inverse z R b one b hz).andE₁
  exact GaussianNameReciprocal.names_equivalent P P (gammaHeight w R (D*b) (D*b)) (gammaHeight z R b b)
    (pd w R (D*b)) (pd z R b) left.andE₁ right.andE₁ left.andE₂ right.andE₂
    (cross_to_diagonal _ _ _ _ same)

private theorem linear_rescale (z w b D i : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (he : Γ ⊢[PRAAx] equal (scale D z) w) :
    Γ ⊢[PRAAx] linear w (D*b) i ≐ linear z b i := by
  have same : Γ ⊢[PRAAx] equal (translated w (D*b) i) (scale D (translated z b i)) := by
    apply equal_of_values
    · have e := ZT.toZ_eq he.andE₁
      simp only [translated, re_add, re_scale, re_one] at e ⊢
      ipra_simps
      linear_combination -e
    · have e := ZT.toZ_eq he.andE₂
      simp only [translated, im_add, im_scale, im_one] at e ⊢
      ipra_simps
      linear_combination -e
  exact (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (positive_product _ _ hD hb) same).eqTrans
    (fraction_rescale (translated z b i) b D hb hD)

theorem rising_product_rescale (z w b D j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] equal (scale D z) w) :
    Γ ⊢[PRAAx] risingProduct w (D*b) j ≐ risingProduct z b j := by
  apply GaussianRationalFiniteProduct.product_congr_bounded linearBody linearBody j
    (GaussianGammaShiftTrajectory.data w (D*b)) (GaussianGammaShiftTrajectory.data z b)
  refine .allI (.impI ?_)
  let a := Syn.shift z
  let c := Syn.shift w
  let B := Syn.shift b
  let E := Syn.shift D
  let J := Syn.shift j
  let i : PTm (n+1) := var 0
  let Δ := lt i J :: Γ.map Fm.shift
  have bs : Δ ⊢[PRAAx] le one B := by simpa [Fm.shift, Syn.shift, Δ, B] using hb.shift.wk
  have ds : Δ ⊢[PRAAx] le one E := by simpa [Fm.shift, Syn.shift, Δ, E] using hD.shift.wk
  have es : Δ ⊢[PRAAx] equal (scale E a) c := by
    simpa [Fm.shift, Syn.shift, Δ, E, a, c] using he.shift.wk
  have move := (linear_at c (E*B) i).eqTrans ((linear_rescale a c B E i bs ds es).eqTrans (linear_at a B i).eqSymm)
  simpa only [GaussianRationalFiniteSum.termsEqual, GaussianGammaShiftTrajectory.subst_data,
    PTm.subst_mul, Syn.shift, a, c, B, E, J, i, Δ] using move

theorem original_product_rescale (a b D N : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx] product (D*a) (D*b) N ≐ product a b N :=
  rising_product_rescale _ _ _ _ _ (le_trans ha.andE₁ (le_of_lt ha.andE₂)) hD (scaled_argument a b D N)

theorem actual_original_negative_interval_Gamma_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ le one (var 2)) ⟶
        crossEquivalent gammaF gammaF (data (var 2*var 0) (var 2*var 1) (var 3)) (data (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (original_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_negative_interval_product_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ le one (var 2)) ⟶
        product (var 2*var 0) (var 2*var 1) (var 3) ≐ product (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (original_product_rescale _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalRescale

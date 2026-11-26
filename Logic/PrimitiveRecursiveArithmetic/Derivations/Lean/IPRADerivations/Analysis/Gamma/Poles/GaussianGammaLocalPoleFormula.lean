import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleMultiplier
import IPRADerivations.Analysis.Gamma.GaussianGammaRadiusOverlap

/-!
# The original local Gamma formula on the punctured disk

The actual C22 product factors into the step, signed factorial and
normalized local factors. Their checked rational inverse gives the
original Gamma value at -n+h/B from the value at the actual native
terminal argument 1+h/B. An exact encoded rational step supplies all
required margins by a computed integer certificate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaLocalPoleFormula

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaLocalPoleGuards (center terminal localMargin center_Gamma_domain terminal_Gamma_domain)
open GaussianGammaPoleMultiplier
  (multiplier actual_pole_multiplier_inverse signedInverseFactorial inverseFactorProduct)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRepeatedShift (risingProduct original_C22)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular gamma_product gammaHeight)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl)
open GaussianRationalHorner (positive_product qmul ofGaussian)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (normSq normSq_scale bounded scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def resultF : PR 2 := multiplyF constantF gammaF
def resultData (h B j D : PTm n) : PTm n :=
  multiplyData constantF gammaF (multiplier h B j) (gammaData (terminal h B j) two B D)
def regularMultiplier (h B j : PTm n) : PTm n := qmul (signedInverseFactorial j) (inverseFactorProduct h B j)
def regularData (h B j D : PTm n) : PTm n :=
  multiplyData constantF gammaF (regularMultiplier h B j) (gammaData (terminal h B j) two B D)
def clearedData (h B j D : PTm n) : PTm n :=
  multiplyData constantF gammaF (ofGaussian h B) (gammaData (center h B j) (succ j) B D)

theorem original_C24_margin (h B A S D j : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) : Γ ⊢[PRAAx]
    crossEquivalent gammaF resultF (gammaData (center h B j) (succ j) B D) (resultData h B j D) := by
  let z := center h B j
  let w := terminal h B j
  let R := succ j
  let Q := GaussianGammaC7Name.nameF
  let x := GaussianGammaC7Name.data z R B
  let y := GaussianGammaC7Name.data w two B
  let yLarge := GaussianGammaC7Name.data w (R+succ j) B
  let g := gammaData w two B D
  let c := risingProduct z B (succ j)
  let e := multiplier h B j
  let F := GaussianGammaRepeatedShift.resultF
  let u := multiplyData constantF Q c y
  let uLarge := multiplyData constantF Q c yLarge
  let v := resultData h B j D
  have hl := center_Gamma_domain h B A S D j hb ha hd hm
  have hr := terminal_Gamma_domain h B A S D j hb ha hd hm.andE₁ hm.andE₂.andE₁
  have ht := GaussianGammaShiftTrajectory.point_source z R B (succ j) hl.andE₁
  have hq : Γ ⊢[PRAAx] pointCN Q x := GaussianGammaC7Name.name_regular z R B hl.andE₁
  have hs : Γ ⊢[PRAAx] pointCN Q y := GaussianGammaC7Name.name_regular w two B hr.andE₁
  have htQ : Γ ⊢[PRAAx] pointCN Q yLarge := GaussianGammaC7Name.name_regular w (R+succ j) B ht
  have hg : Γ ⊢[PRAAx] pointCN gammaF g := gamma_regular w two B A D hr
  have hc := constant_regular (Γ := Γ) c
  have he := constant_regular (Γ := Γ) e
  have hv : Γ ⊢[PRAAx] pointCN resultF v := multiply_fast _ _ _ _ he hg
  have hu : Γ ⊢[PRAAx] pointCN F u := multiply_fast _ _ _ _ hc hs
  have shiftRadius : Γ ⊢[PRAAx] crossEquivalent F F uLarge u :=
    GaussianGammaAdjacentCutoff.multiply_cross constantF constantF Q Q c c yLarge y hc hc htQ hs
      (cross_refl _ _ hc) (GaussianGammaRadiusOverlap.original_P_overlap w (R+succ j) two B ht hr.andE₁)
  have c22 : Γ ⊢[PRAAx] crossEquivalent Q F x u := cross_trans _ _ _ _ _ _ (original_C22 z R B j hl.andE₁) shiftRadius
  have transfer := GaussianGammaAdjacentCutoff.multiply_cross Q F resultF resultF x u v v hq hu hv hv
    c22 (cross_refl _ _ hv)
  have cinv := GaussianGammaReciprocalInverse.constant_inverse c e x (actual_pole_multiplier_inverse h B A S D j hb ha hd hm)
  have ginv := cross_trans _ _ _ _ _ _ (gamma_product w two B A D hr)
    (GaussianBoundedInverseApartness.ones_equivalent y x)
  have result := GaussianGammaReciprocalInverse.inverse_pairs constantF Q constantF gammaF
    c y e g x hc hs he hg cinv ginv
  have hOrig := (GaussianGammaReciprocalInverse.original_gamma_inverse z R B A D hl).andE₁
  exact GaussianBoundedInverseApartness.reciprocal_matches_inverse Q resultF (gammaHeight z R B D) x v
    hOrig.andE₁ hv hOrig.andE₂ (cross_trans _ _ _ _ _ _ transfer result)

def punctureDenominator (B : PTm n) : PTm n := two*(B*B)
def punctureUpper (B : PTm n) : PTm n := pred (punctureDenominator B)

theorem puncture_denominator_positive (B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (punctureDenominator B) :=
  positive_product _ _ (le_succ_self one) (positive_product _ _ hb hb)

theorem actual_puncture_certificate (h B : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hu : Γ ⊢[PRAAx] lt (normSq h) (B*B)) :
    Γ ⊢[PRAAx] localMargin h B one (punctureUpper B) (punctureDenominator B) := by
  let D := punctureDenominator B
  let S := punctureUpper B
  let T := monus (B*B) (succ (normSq h))
  have hd := puncture_denominator_positive B hb
  have succ_eq : Γ ⊢[PRAAx] D ≐ S+one :=
    (LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.pos_of_one_le hd).eqTrans (succ_eq_add_one _)
  have sum : Γ ⊢[PRAAx] le (one+S) D := le_of_eq_add (d := ConciseIPRA.PTm.zero)
    (succ_eq.eqTrans (by ipra_ring))
  have exactUpper : Γ ⊢[PRAAx] le (D*D*normSq h) ((S*B)*(S*B)) := by
    have es := natEq succ_eq
    have en := natEq (eq_add_of_le hu)
    have rr : 𝔞 S = 𝔞 D - 1 := by
      ipra_simps
      linear_combination -es
    have nn : 𝔞 (normSq h) = 𝔞 B * 𝔞 B - 1 - 𝔞 T := by
      ipra_simps
      linear_combination -en
    refine le_of_eq_add (d := D*D*T+B*B) ?_
    apply deriveNat
    ipra_simps
    rw [rr,nn]
    unfold D punctureDenominator
    ipra_simps
    ring
  have disk : Γ ⊢[PRAAx] bounded (scale D h) (S*B) :=
    le_congr (normSq_scale D h).eqSymm (.eqRefl _) exactUpper
  have bd : Γ ⊢[PRAAx] le B D :=
    le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right B hb))
      (le_of_eq_add (d := B*B) (by unfold D punctureDenominator; ipra_ring))
  have lower : Γ ⊢[PRAAx] le ((one*B)*(one*B)) (D*D*normSq h) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono bd bd))
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (D*D)) hn))
  exact .andI sum (.andI disk lower)

theorem original_C24_punctured_disk (h B j : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hu : Γ ⊢[PRAAx] lt (normSq h) (B*B)) :
    Γ ⊢[PRAAx] crossEquivalent gammaF resultF
      (gammaData (center h B j) (succ j) B (punctureDenominator B))
      (resultData h B j (punctureDenominator B)) :=
  original_C24_margin h B one (punctureUpper B) (punctureDenominator B) j hb (le_refl _)
    (puncture_denominator_positive B hb) (actual_puncture_certificate h B hb hn hu)

theorem regular_multiplier (h B A S D j : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] qmul (ofGaussian h B) (multiplier h B j) ≐ regularMultiplier h B j := by
  let x := ofGaussian h B
  let y := regularMultiplier h B j
  have inv := GaussianGammaPoleMultiplier.step_inverse h B A S D hb ha hd hm
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical y := GaussianRationalHorner.qmul_canonical _ _
  exact (GaussianReciprocalHorner.qmul_associative x (GaussianRationalReciprocal.reciprocal x) y).eqSymm.eqTrans
    ((qmul_congr inv (.eqRefl _)).eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ can)))

theorem original_cleared_local_formula (h B A S D j : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one A) (hd : Γ ⊢[PRAAx] le one D)
    (hm : Γ ⊢[PRAAx] localMargin h B A S D) :
    Γ ⊢[PRAAx] crossEquivalent resultF resultF (clearedData h B j D) (regularData h B j D) := by
  let x := ofGaussian h B
  let y := multiplier h B j
  let z := qmul x y
  let u := gammaData (center h B j) (succ j) B D
  let v := gammaData (terminal h B j) two B D
  have hl := center_Gamma_domain h B A S D j hb ha hd hm
  have hr := terminal_Gamma_domain h B A S D j hb ha hd hm.andE₁ hm.andE₂.andE₁
  have hx := constant_regular (Γ := Γ) x
  have hy := constant_regular (Γ := Γ) y
  have hu : Γ ⊢[PRAAx] pointCN gammaF u := gamma_regular _ _ _ _ _ hl
  have hv : Γ ⊢[PRAAx] pointCN gammaF v := gamma_regular _ _ _ _ _ hr
  have he := original_C24_margin h B A S D j hb ha hd hm
  have lift := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF resultF
    x x u (resultData h B j D) hx hx hu (multiply_fast _ _ _ _ hy hv) (cross_refl _ _ hx) he
  have merge := GaussianGammaEulerShift.merge_head gammaF x y v hv
  have cond := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (regular_multiplier h B A S D j hb ha hd hm)
  have out := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF gammaF gammaF
    z (regularMultiplier h B j) v v (constant_regular _) (constant_regular _) hv hv cond (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ lift (cross_trans _ _ _ _ _ _ merge out)

theorem actual_original_puncture_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le one (normSq (var 0)) ⟶ lt (normSq (var 0)) (var 1*var 1) ⟶
      localMargin (var 0) (var 1) one (punctureUpper (var 1)) (punctureDenominator (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (actual_puncture_certificate _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_C24_punctured_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (normSq (var 0)) ⟶ lt (normSq (var 0)) (var 1*var 1) ⟶
      crossEquivalent gammaF resultF
        (gammaData (center (var 0) (var 1) (var 2)) (succ (var 2)) (var 1) (punctureDenominator (var 1)))
        (resultData (var 0) (var 1) (var 2) (punctureDenominator (var 1)))) :=
  closeUniv 3 (.impI (.impI (.impI (original_C24_punctured_disk _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_C24_cleared_local_formula_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (normSq (var 0)) ⟶ lt (normSq (var 0)) (var 1*var 1) ⟶
      crossEquivalent resultF resultF
        (clearedData (var 0) (var 1) (var 2) (punctureDenominator (var 1)))
        (regularData (var 0) (var 1) (var 2) (punctureDenominator (var 1)))) :=
  closeUniv 3 (.impI (.impI (.impI (original_cleared_local_formula _ _ _ _ _ _
    hyp2 (le_refl _) (puncture_denominator_positive _ hyp2) (actual_puncture_certificate _ _ hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaLocalPoleFormula

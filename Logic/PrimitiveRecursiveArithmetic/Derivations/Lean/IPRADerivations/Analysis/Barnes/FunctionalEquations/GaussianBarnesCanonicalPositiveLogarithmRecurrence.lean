import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithmRealAxis
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.GaussianBarnesCanonicalHyperfactorialBarnesStep
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalNormalization

/-! The real logarithm of the original Barnes value advances by the original real Log Gamma. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianBarnesCanonicalHyperfactorial (barnesData barnes_source barnes_regular specialLogData logarithm_source)
open GaussianBarnesCanonicalPositiveLogarithm (default_source regular exponential_value)
open GaussianBarnesCanonicalPositiveLogarithmRealAxis (samples_axis)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub re_scale im_scale re_one im_one)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "V" => GaussianBarnesCanonicalValue.nameF

private theorem center_agrees (a b : PTm n) : Γ ⊢[PRAAx]
    equal (GaussianBarnesCanonicalThirdLogarithmRows.center a b) (GaussianBarnesCanonicalHyperfactorial.center a b) := by
  apply equal_of_values <;>
    simp only [GaussianBarnesCanonicalHyperfactorial.center,GaussianBarnesCanonicalThirdLogarithmRows.center,
      re_sub,im_sub,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat] <;>
    (try ipra_simps) <;> ring

theorem exponential_barnes (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (E L) V (exponentialInputData L (ld a b (a+b))) (barnesData a b) := by
  let R := a+b
  let z := GaussianBarnesCanonicalThirdLogarithmRows.center a b
  let w := GaussianBarnesCanonicalHyperfactorial.center a b
  have hs := default_source a b ha hb
  have same := GaussianBarnesCanonicalProperness.proper z w R R b b hs.andE₂ (barnes_source a b hb)
    (GaussianGammaFiniteValueProperness.fraction_equal _ _ _ hb (center_agrees a b))
  exact cross_trans _ _ _ _ _ _ (exponential_value a b R hs) same

theorem recurrence (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent L (addF L G) (ld (a+b) b ((a+b)+b)) (addData (ld a b (a+b)) (specialLogData a b)) := by
  let x := ld a b (a+b)
  let y := specialLogData a b
  let t := ld (a+b) b ((a+b)+b)
  let F := addF L G
  let f := addData x y
  let u := exponentialInputData L x
  let v := exponentialInputData G y
  have hc := le_trans ha (le_add_right a b)
  have hs := default_source a b ha hb
  have ht := default_source (a+b) b hc hb
  have hx := regular _ _ _ hs
  have hy := GaussianBarnesCanonicalHyperfactorialPowerStep.logarithm_regular a b ha hb
  have hh := regular _ _ _ ht
  have hF := add_fast L G x y hx hy
  have ex := exponential_input L x hx
  have ey := exponential_input G y hy
  have ef := exponential_input F f hF
  have step := GaussianBarnesCanonicalHyperfactorialBarnesStep.denominator_step a b ha hb
  have er := GaussianRadiusExponentialName.name_regular G _ _ ey
  have product := GaussianGammaAdjacentCutoff.multiply_cross (E L) V (E G) (E G) u (barnesData a b) v v
    (GaussianRadiusExponentialName.name_regular L _ _ ex) (barnes_regular a b hb) er er
    (exponential_barnes a b ha hb) (cross_refl _ _ er)
  have split := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent L G F
    (U L x) (U G y) (U F f) x y f ex ey ef (cross_refl _ _ hF)
  have fy := GaussianLogGammaEulerPositiveAxis.cofinal_axis_samples a b zero (logarithm_source a b ha hb)
  exact independent_radii_injective L F (U L t) (U F f) t f (exponential_input L t hh) ef
    (samples_axis _ _ _ ht) (GaussianNamedPositiveLogarithmScale.sum_axis L G x y (samples_axis _ _ _ hs) fy)
    (cross_trans _ _ _ _ _ _ (exponential_barnes (a+b) b hc hb)
      (cross_trans _ _ _ _ _ _ step (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ product) split)))

theorem actual_Barnes_real_logarithm_unit_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let a := var 0
     let b := var 1
     (le one a ⋏ le one b) ⟶ crossEquivalent L (addF L G)
       (ld (a+b) b ((a+b)+b)) (addData (ld a b (a+b)) (specialLogData a b))) :=
  closeUniv 2 (.impI (recurrence _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem normalization (b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    crossEquivalent L GaussianNameRingLaws.zeroF (ld b b (b+b)) zero := by
  let x := ld b b (b+b)
  let z := GaussianBarnesCanonicalThirdLogarithmRows.center b b
  let Z := GaussianNameRingLaws.zeroF
  let C := GaussianGammaCanonicalExponent.constantF
  let O := GaussianNameRingLaws.oneF
  let q : PTm n := zero
  let c : PTm n := GaussianRationalReciprocal.qone
  have hs := default_source b b hb hb
  have e : Γ ⊢[PRAAx] equal z ComplexLogarithmRemainder.zeroCode := by
    apply equal_of_values
    · simp [z,GaussianBarnesCanonicalThirdLogarithmRows.center,eval_re_code,
        GaussianRootAlgebra.re_zero,ZT.toZ_sub]
    · simp [z,GaussianBarnesCanonicalThirdLogarithmRows.center,eval_im_code,GaussianRootAlgebra.im_zero]
  have nz := (GaussianRootAlgebra.normSq_equal e).eqTrans ComplexLogarithmRemainder.normSq_zero
  have ev := GaussianBarnesCanonicalNormalization.normalization z (b+b) b hb nz
  have oneName : Γ ⊢[PRAAx] crossEquivalent C O c q := by
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular _)
      (GaussianNameRingLaws.one_fast _)
    refine .allI ?_
    simpa only [c,q,Syn.shift,GaussianRationalReciprocal.subst_qone,PTm.subst_zero] using
      (GaussianGammaCanonicalExponent.constant_at (Γ := Γ.map Fm.shift) (var 0) GaussianRationalReciprocal.qone).eqTrans
        (GaussianNameRingLaws.one_at (var 0) zero).eqSymm
  have rz : Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples Z q := by
    refine .allI ?_
    exact RationalGaussianEmbedding.axis_congr (GaussianNameRingLaws.zero_at (var 0) (Syn.shift q)).eqSymm
      RationalGaussianEmbedding.axis_zero
  exact independent_radii_injective L Z (U L x) one x q (exponential_input _ _ (regular _ _ _ hs))
    (GaussianExponentialInverse.zero_input _ _) (samples_axis _ _ _ hs) rz
    (cross_trans _ _ _ _ _ _ (exponential_value b b (b+b) hs) (cross_trans _ _ _ _ _ _ ev
      (cross_trans _ _ _ _ _ _ oneName (cross_symm _ _ _ _ (GaussianExponentialInverse.zero_exponential_cross one q)))))

theorem actual_Barnes_real_logarithm_at_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (let b := var 0
     le one b ⟶ crossEquivalent L GaussianNameRingLaws.zeroF (ld b b (b+b)) zero) :=
  closeUniv 1 (.impI (normalization _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveLogarithmRecurrence

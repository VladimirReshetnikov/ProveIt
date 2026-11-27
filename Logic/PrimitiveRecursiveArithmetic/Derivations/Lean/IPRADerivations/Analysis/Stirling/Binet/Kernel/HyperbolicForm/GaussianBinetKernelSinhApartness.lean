import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.GaussianBinetKernelFrozenHyperbolic
import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.GaussianBinetKernelSinhOddLower
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialSeparation
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarColumnSelection
import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineReflectionLower
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedFiniteProductApartness

/-!
# Apartness of the original positive-time hyperbolic sine name

At an explicit precision, both exponential samples are compared with
the same even finite cutoff. The lower bound of its exact odd part
survives the sampler errors and gives an actual inverse-name witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelSinhApartness

open_ipra
open GaussianBinetKernelFrozenHyperbolic (fixedExpF fixedExpData fixedSinhF fixedSinhData fixed_exp_input expRadius halfTime)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNameRingLaws (multiply_sample_error product_right_error)
open GaussianNamedDifference (difference_distance name_regular sample_error)
open GaussianPiRationalScale (point point_negate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul canonical canonical_unique represents_congr ofGaussian_represents
  qmul_canonical qadd_represents qmul_represents positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalLowerBounds (lower lower_congr)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative qsub_represents qnegative_represents
  qnegative_canonical qsub_canonical)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr rescale_to)
open GaussianRootAlgebra (equal_of_values re_mul im_mul re_add im_add re_sub im_sub re_neg im_neg re_scale im_scale)
open GaussianScalarExponentialOddTaylor (oddSum)
open GaussianSineProductImaginaryLogDerivative (realNumerator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "difference" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private def negativeHalf : PTm n := point true one two
private def positiveHalf : PTm n := point false one two

private theorem reverse_sub (a b : PTm n) : Γ ⊢[PRAAx] qsub b a ≐ qnegative (qsub a b) := by
  let E := rawDen a*rawDen b
  have hE := positive_product _ _ (raw_den_positive (Γ := Γ) a) (raw_den_positive b)
  have ha := rescale_to a (rawGaussian a) (rawDen a) (rawDen b) E (raw_represents (Γ := Γ) a) (.eqRefl _)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a) E (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have l := qsub_represents _ _ _ _ _ hE hb ha
  have r := qnegative_represents _ _ _ (qsub_represents _ _ _ _ _ hE ha hb)
  apply canonical_unique _ _ _ E (qsub_canonical _ _) (qnegative_canonical _) hE (hrv := r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := l)
  apply equal_of_values <;> simp only [re_sub,im_sub,re_neg,im_neg] <;> ring

private theorem half_double (a : PTm n) (h : Γ ⊢[PRAAx] canonical a) : Γ ⊢[PRAAx] qmul positiveHalf (qadd a a) ≐ a := by
  let E := rawDen a
  let A := rawGaussian a
  have hE := raw_den_positive (Γ := Γ) a
  have h₂ := le_succ_self (Γ := Γ) one
  have ha := raw_represents (Γ := Γ) a
  have l := qmul_represents positiveHalf _ (realNumerator one) _ two E h₂ hE
    (ofGaussian_represents _ _ h₂) (qadd_represents _ _ _ _ _ hE ha ha)
  have r := rescale_to a A E two (two*E) ha (mul_comm _ _)
  apply canonical_unique _ _ _ (two*E) (qmul_canonical _ _) h (positive_product _ _ h₂ hE) (hrv := r)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := l)
  apply equal_of_values <;>
    simp only [re_mul,im_mul,re_scale,im_scale,re_add,im_add,realNumerator,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem symmetric_even_value (q K : PTm n) : Γ ⊢[PRAAx]
    qmul negativeHalf (qsub (scalarSum (qnegative q) (two*K)) (scalarSum q (two*K))) ≐ oddSum q K := by
  let v := qsub (scalarSum q (two*K)) (scalarSum (qnegative q) (two*K))
  have e := qmul_congr (point_negate false one two (le_succ_self (Γ := Γ) one)).eqSymm
    (reverse_sub (scalarSum q (two*K)) (scalarSum (qnegative q) (two*K)))
  exact e.eqTrans ((GaussianScalarColumnSelection.negative_both_product positiveHalf v).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianScalarExponentialOddTaylor.odd_taylor_identity q K)).eqTrans
      (half_double _ (GaussianScalarExponentialOddTaylor.odd_sum_canonical q K))))

def error (A B : PTm n) : PTm n := let y := difference (fixedExpData true A B) (fixedExpData false A B)
  (multiplyModulus constantF (Diff fixedExpF fixedExpF) negativeHalf y+one)+U constantF negativeHalf*(num 8)

private theorem positive_index (A p : PTm n) : Γ ⊢[PRAAx] le one (GaussianRadiusExponentialName.index (expRadius A) p) :=
  GaussianPositiveExponentialSeparation.original_cutoff_positive _ _

private theorem finite_exp_error (s : Bool) (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 fixedExpF p (fixedExpData s A B))
      (scalarSum (halfTime s A B) (two*GaussianRadiusExponentialName.index (expRadius A) p)) one (unit p) := by
  let R := expRadius A
  let q := halfTime s A B
  let K := GaussianRadiusExponentialName.index R p
  let N := two*K
  have hN : Γ ⊢[PRAAx] le K N := by dsimp only [N]; ipra_le 𝔞 K
  have input := fixed_exp_input s A B hB
  have cert := GaussianRadiusExponentialName.bounded_samples_at constantF R q p input.andE₂
  have hq := GaussianRationalReciprocal.bound_congr (constant_at p q) (.eqRefl _) (.eqRefl _) cert
  have raw := GaussianExponentialReference.later_cutoff q R p N hq hN
  have rev := distance_symmetric _ _ _ _ (unit_positive (succ p)) raw
  have coarse := GaussianExponentialReference.dyadic_weaken _ _ one p (succ p) (le_succ_self p) rev
  have read : Γ ⊢[PRAAx] ap2 fixedExpF p (fixedExpData s A B) ≐ scalarSum q K :=
    (GaussianRadiusExponentialName.sample_at constantF R p q).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (constant_at _ _))
  exact distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

theorem sample_odd_error (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 fixedSinhF p (fixedSinhData A B))
      (oddSum (halfTime false A B) (GaussianRadiusExponentialName.index (expRadius A) p)) (error A B) (unit p) := by
  let q := halfTime false A B
  let K := GaussianRadiusExponentialName.index (expRadius A) p
  let N := two*K
  let a := fixedExpData true A B
  let b := fixedExpData false A B
  let y := difference a b
  let F := Diff fixedExpF fixedExpF
  let c := (negativeHalf : PTm n)
  let C := ap2 constantF p c
  have hr (s : Bool) := GaussianRadiusExponentialName.name_regular constantF (expRadius A) (halfTime s A B)
    (fixed_exp_input s A B hB)
  have hF : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN F y := name_regular _ _ _ _ (hr true) (hr false)
  have hpos := unit_positive (Γ := Γ) p
  have base := sample_error fixedExpF fixedExpF a b p (hr true) (hr false)
  have later := difference_distance _ _ _ _ _ _ _ hpos (finite_exp_error true p A B hB) (finite_exp_error false p A B hB)
  have joined := distance_triangle_same _ _ _ _ _ _ hpos base later
  have joined' := distance_congr (.eqRefl _) (.eqRefl _) (show Γ ⊢[PRAAx] num 6+(one+one) ≐ num 8 by ipra_ring)
    (.eqRefl _) joined
  have outer := multiply_sample_error constantF F c y p (constant_regular c) hF
  have inner := product_right_error C _ _ _ _ _ _ hpos joined' (sample_bound F y p hF) (sample_bound constantF c p (constant_regular c))
  have total := distance_triangle_same _ _ _ _ _ _ hpos outer inner
  have hs := point_negate false A (two*B) (positive_product _ _ (le_succ_self one) hB)
  have code := GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl (succ N)) hs.eqSymm
  have exact := (qmul_congr (constant_at p c) (qsub_congr code (.eqRefl _))).eqTrans (symmetric_even_value q K)
  exact distance_congr (.eqRefl _) exact (.eqRefl _) (.eqRefl _) total

def height (A B : PTm n) : PTm n := GaussianRootSchedule.binaryLength ((num 4*B)*(error A B+one))

private theorem radius_first (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (GaussianDominantPairAlgebra.radiusPoint A B)) (ZT.ofNat A) B :=
  GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [GaussianDominantPairAlgebra.radiusNumerator,ComplexLogarithmRemainder.eval_re_code])
    (.eqRefl _) (GaussianDominantPairAlgebra.radius_represents A B hB).andE₁

theorem sinh_apart (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart fixedSinhF (height A B) (fixedSinhData A B) := by
  let h := height A B
  let p := GaussianNameReciprocal.anchor h
  let D := num 4*B
  let K := GaussianRadiusExponentialName.index (expRadius A) p
  let q := halfTime false A B
  let o := oddSum q K
  let v := ap2 fixedSinhF p (fixedSinhData A B)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (by ipra_le 3) hB
  have hb : Γ ⊢[PRAAx] le one (two*B) := positive_product _ _ (le_succ_self one) hB
  have hk := positive_index (Γ := Γ) A p
  let j := monus K one
  have eq : Γ ⊢[PRAAx] K ≐ succ j := (eq_add_of_le hk).eqTrans (by dsimp only [j]; ipra_ring)
  have order : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (GaussianDominantPairAlgebra.radiusPoint two D))
      (fstT (GaussianDominantPairAlgebra.radiusPoint A (two*B))) :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hD hb
      (radius_first _ _ hD) (radius_first _ _ hb)
      (by dsimp only [D]; ipra_le 4*𝔞 B*sl hA)
  have lo := GaussianBinetKernelSinhOddLower.odd_lower A (two*B) j two D hb hD order
  have oddEq : Γ ⊢[PRAAx] o ≐ oddSum q (succ j) := GaussianRationalFiniteSum.sum_index_congr
    GaussianScalarExponentialOddTaylor.oddBody eq (.eqRefl q)
  have anchorLower : Γ ⊢[PRAAx] lower o (two*one) D :=
    lower_congr oddEq.eqSymm (by ipra_ring) (.eqRefl _) lo
  have big : Γ ⊢[PRAAx] le (D*(error A B+one)) (unit h) :=
    (GaussianRootSchedule.binary_length_correct _).andE₁
  have late : Γ ⊢[PRAAx] le (unit h) (unit p) :=
    GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have bd : Γ ⊢[PRAAx] le (error A B*D) (one*unit p) := by
    ipra_le sl big + sl late + 𝔞 D
  have err := distance_radius_mono _ _ _ _ one D (unit_positive p) hD bd (sample_odd_error p A B hB)
  have small := GaussianSineReflectionLower.lower_after_half_error o v one D hD anchorLower
    (distance_symmetric _ _ _ _ hD err)
  have grow : Γ ⊢[PRAAx] le D (unit h) := by ipra_le sl big + 𝔞 D*𝔞 (error A B)
  exact GaussianNamedFiniteProductApartness.weaken_margin v D (unit h) hD grow
    (GaussianRationalLowerBounds.name_lower _ _ _ (le_refl one) hD small)

theorem actual_positive_rational_time_sinh_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 0) ⋏ le one (var 1)) ⟶ GaussianNameReciprocal.apart fixedSinhF (height (var 0) (var 1))
      (fixedSinhData (var 0) (var 1))) :=
  closeUniv 2 (.impI (sinh_apart _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelSinhApartness

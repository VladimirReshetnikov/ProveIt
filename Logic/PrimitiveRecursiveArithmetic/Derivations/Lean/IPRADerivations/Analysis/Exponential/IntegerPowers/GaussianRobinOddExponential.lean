import IPRADerivations.Analysis.Logarithm.Robin.GaussianRobinOddLogarithmName
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant

/-!
# Exponential relation for the original Robin odd logarithm

Addition of the negative-side logarithm to the odd name gives the
positive-side logarithm. The checked local exponential identities
therefore identify the exponential of the odd series after multiplication
by the exact positive rational factor on the negative side.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinOddExponential

open_ipra
open GaussianRobinOddLogarithmName (source negativeArgument log_sources plusData minusData inputs)
open GaussianRobinLogarithmParity (native)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (negativeF negativeData zeroF oneF)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents ofGaussian_canonical qadd qmul qadd_canonical qmul_canonical
    qadd_represents qmul_represents represents_congr canonical_unique positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical rescale_to qmul_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRadiusExponentialName (input)
open GaussianRadiusExponentialName renaming data → expData, nameF → expF
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def oddF : PR 2 := GaussianRobinOddLogarithmName.pointF
def localF : PR 2 := GaussianLocalLogarithmName.pointF
def constantF : PR 2 := GaussianGammaCanonicalExponent.constantF
def plusValue (a b : PTm n) : PTm n :=
  GaussianFiniteLogarithmCompositionTail.linearValue (ofGaussian (native a) b)
def minusValue (a b : PTm n) : PTm n :=
  GaussianFiniteLogarithmCompositionTail.linearValue (ofGaussian (negativeArgument a) b)

theorem sample_radius (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    bounded (GaussianRobinOddLogarithmName.point p a b) (num 3) one := by
  let t := GaussianRobinOddLogarithmName.clock p
  let w := GaussianRobinOddLogarithmName.difference t a b
  let v := GaussianRobinOddLogarithmName.sample p a b
  have hs := log_sources a b h
  have hm := GaussianRationalReciprocal.bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one)
    (GaussianLocalLogarithmName.value_unit_disk t _ _ _ hs.andE₁)
    (GaussianLocalLogarithmName.value_unit_disk t _ _ _ hs.andE₂)
  have hwb : Γ ⊢[PRAAx] bounded w two one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) hm
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := le_of_eq_add (d := num 7) (by ipra_ring)
  have hp := positive_product _ _ h8 (unit_positive p)
  have e := distance_symmetric w v _ _ hp (GaussianRobinOddLogarithmName.rounding_bound p a b h.andE₁)
  have near := distance_radius_mono _ _ one _ one one hp (le_refl one)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm hp) e
  have sum := GaussianReconstructionRoots.norm_from_distance _ _ one one two one
    (le_refl one) (le_refl one) near hwb
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRobinOddLogarithmName.point_at p a b).eqSymm (by ipra_ring) (by ipra_ring) sum

theorem odd_input (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] input oddF (num 3) (inputs a b) := by
  refine .andI (GaussianRobinOddLogarithmName.name_regular a b h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianRobinOddLogarithmName.subst_source] using h.shift
  simpa only [oddF,GaussianRobinOddLogarithmName.point,Syn.shift,
    GaussianRobinOddLogarithmName.subst_inputs,LeanProofs.IPRA.PTm.subst_num] using
    sample_radius (var 0) (Syn.shift a) (Syn.shift b) hs

private theorem zero_at_either_data (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let X := Syn.shift (Syn.shift x)
  let Y := Syn.shift (Syn.shift y)
  have hx := GaussianNameRingLaws.zero_at (Γ := C) (var 0) X
  have hy := GaussianNameRingLaws.zero_at (Γ := C) (var 0) Y
  exact distance_congr (.eqRefl _) (hx.eqTrans hy.eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.point_at zeroF X (var 1) (var 0) (GaussianNameRingLaws.zero_fast X))

theorem complete_difference (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (addF oddF localF) localF
      (addData (inputs a b) (minusData a b)) (plusData a b) := by
  let X := plusData a b
  let Y := minusData a b
  let O := inputs a b
  let D := GaussianRobinOddLogarithmName.logDifferenceF
  let d := GaussianRobinOddLogarithmName.logDifferenceData a b
  let M := negativeF localF
  let m := negativeData Y
  let S := addF M localF
  let s := addData m Y
  have hs := log_sources a b h
  have hx : Γ ⊢[PRAAx] pointCN localF X := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₁
  have hy : Γ ⊢[PRAAx] pointCN localF Y := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₂
  have ho := (odd_input a b h).andE₁
  have hd := GaussianRobinOddLogarithmName.log_difference_name a b h
  have hm := GaussianNameRingLaws.negative_fast localF Y hy
  have hAssoc := GaussianNameRingLaws.add_associative localF M localF X m Y hx hm hy
  have swapped := GaussianNameRingLaws.add_commutative M localF m Y hm hy
  have cancel := cross_trans _ _ _ _ _ _ swapped
    (cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.add_negative localF Y hy) (zero_at_either_data Y X))
  have e := GaussianNameArithmetic.add_equivalent oddF D localF localF O d Y Y ho hd hy hy
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _
      (cross_symm _ _ _ _ (GaussianRobinOddLogarithmName.original_difference_name a b h)))
    (GaussianNameEquivalence.diagonal_refl localF Y)
  have last := GaussianNameArithmetic.add_equivalent localF localF S zeroF X X s X hx hx
    (GaussianNameArithmetic.add_fast _ _ _ _ hm hy) (GaussianNameRingLaws.zero_fast X)
    (GaussianNameEquivalence.diagonal_refl localF X)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ cancel)
  exact cross_trans _ _ _ _ _ _ e (cross_trans _ _ _ _ _ _ hAssoc
    (cross_trans _ _ _ _ _ _ last (GaussianNameRingLaws.add_zero localF X hx)))

theorem local_exponential (z R b : PTm n) (h : Γ ⊢[PRAAx] GaussianLocalLogarithmName.source z R b) :
    Γ ⊢[PRAAx] crossEquivalent (expF localF) constantF
      (expData one (GaussianLocalLogarithmName.data z R b))
      (GaussianFiniteLogarithmCompositionTail.linearValue (ofGaussian z b)) := by
  have u := GaussianLocalLogarithmName.original_exponential_input z R b h
  exact cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianExponentialRadiusIndependence.original_unit_cross _ _ u))
    (cross_trans _ _ _ _ _ _ (GaussianLocalLogarithmExponentialIdentity.source_cross z R b h)
      (GaussianGammaAdjacentCutoff.linear_constant_cross (ofGaussian z b)))

theorem odd_exponential_product (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF (expF oddF) constantF) constantF
      (multiplyData (expF oddF) constantF (expData (num 3) (inputs a b)) (minusValue a b))
      (plusValue a b) := by
  let O := inputs a b
  let X := plusData a b
  let Y := minusData a b
  have hs := log_sources a b h
  have ho := odd_input a b h
  have hx := GaussianExponentialRadiusIndependence.radius_one_input localF X
    (GaussianLocalLogarithmName.original_exponential_input _ _ _ hs.andE₁)
  have hy := GaussianExponentialRadiusIndependence.radius_one_input localF Y
    (GaussianLocalLogarithmName.original_exponential_input _ _ _ hs.andE₂)
  have law := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent
    oddF localF localF (num 3) one one O Y X ho hy hx (complete_difference a b h)
  have eR := GaussianRadiusExponentialName.name_regular _ _ _ ho
  have eL := GaussianRadiusExponentialName.name_regular _ _ _ hy
  have replace := GaussianGammaAdjacentCutoff.multiply_cross (expF oddF) (expF oddF)
    constantF (expF localF) (expData (num 3) O) (expData (num 3) O) (minusValue a b) (expData one Y)
    eR eR (GaussianGammaCanonicalExponent.constant_regular _) eL (cross_refl _ _ eR)
    (cross_symm _ _ _ _ (local_exponential (negativeArgument a) a b hs.andE₂))
  exact cross_trans _ _ _ _ _ _ replace
    (cross_trans _ _ _ _ _ _ law (local_exponential (native a) a b hs.andE₁))

def ratio (a b : PTm n) : PTm n := ofGaussian (native (b+a)) (monus b a)
def inverseFactor (a b : PTm n) : PTm n := ofGaussian (native b) (monus b a)

theorem difference_positive (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] le one (monus b a) := by
  let d := monus b a
  have ab := le_trans (le_of_eq_add (d := a) (by ipra_ring : Γ ⊢[PRAAx] two*a ≐ a+a)) h.andE₂
  have e := eq_add_of_le ab
  have ad : Γ ⊢[PRAAx] le a d :=
    le_of_add_le_add_right (c := a)
      (le_congr (by ipra_ring) (e.eqTrans (add_comm _ _)) h.andE₂)
  have hdd := le_trans h.andE₁ (le_congr e.eqSymm (.eqRefl _) (add_le_add_right d ad))
  have nz : Γ ⊢[PRAAx] neg (d ≐ zero) := by
    refine .impI ?_
    have z : (d ≐ zero) :: Γ ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have dd : (d ≐ zero) :: Γ ⊢[PRAAx] d+d ≐ zero :=
      (congrAdd z z).eqTrans (by ipra_ring)
    exact succ_ne_zero ((monus_zero one).eqSymm.eqTrans (le_congr (.eqRefl _) dd hdd.wk))
  exact le_of_eq_add ((eq_monus_one_add_one nz).eqTrans (add_comm _ _))

private theorem linear_representation (z b s : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (native b) z) (native s)) :
    Γ ⊢[PRAAx] GaussianFiniteLogarithmCompositionTail.linearValue (ofGaussian z b) ≐ ofGaussian (native s) b := by
  let o : PTm n := ComplexLogarithmRemainder.oneCode
  have r1 := rescale_to qone o one b b (ofGaussian_represents (Γ := Γ) o one (le_refl _))
    (one_mul _)
  have r2 := ofGaussian_represents (Γ := Γ) z b hb
  exact canonical_unique _ _ _ _ (qadd_canonical _ _) (ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) he (.eqRefl _) (qadd_represents _ _ _ _ _ hb r1 r2))
    (ofGaussian_represents _ _ hb)

theorem plus_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] plusValue a b ≐ ofGaussian (native (b+a)) b := by
  apply linear_representation _ _ _ hb
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [native,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    (try ipra_simps) <;> ring

theorem minus_fraction (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] minusValue a b ≐ ofGaussian (native (monus b a)) b := by
  apply linear_representation _ _ _ h.andE₁
  have ab := le_trans (le_of_eq_add (d := a) (by ipra_ring : Γ ⊢[PRAAx] two*a ≐ a+a)) h.andE₂
  have e := natEq (eq_add_of_le ab)
  apply GaussianRootAlgebra.equal_of_values
  · simp only [native,negativeArgument,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_neg,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    rw [e]
    ring
  · simp only [native,negativeArgument,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_neg,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one]
    ring

private theorem multiply_real_fractions (a b c d : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] qmul (ofGaussian (native a) b) (ofGaussian (native c) d) ≐ ofGaussian (native (a*c)) (b*d) := by
  have hbd := positive_product _ _ hb hd
  refine canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hbd) hbd
    (represents_congr (.eqRefl _) ?_ (.eqRefl _) (qmul_represents _ _ _ _ _ _ hb hd
      (ofGaussian_represents _ _ hb) (ofGaussian_represents _ _ hd))) (ofGaussian_represents _ _ hbd)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [native,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    (try ipra_simps) <;> ring

theorem factor_inverse (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qmul (minusValue a b) (inverseFactor a b) ≐ qone := by
  let d := monus b a
  let E := b*d
  let o : PTm n := ComplexLogarithmRemainder.oneCode
  have he := positive_product _ _ h.andE₁ (difference_positive a b h)
  have r1 := rescale_to qone o one E E (ofGaussian_represents (Γ := Γ) o one (le_refl _))
    (one_mul _)
  have ea : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (d*b)) (native E) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [native,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,natEq (mul_comm (Γ := Γ) d b),E]
  have r2 := represents_congr (.eqRefl _) ea (.eqRefl _)
    (ofGaussian_represents (native (d*b)) E he)
  exact (qmul_congr (minus_fraction a b h) (.eqRefl _)).eqTrans
    ((multiply_real_fractions d b b d h.andE₁ (difference_positive a b h)).eqTrans
      (canonical_unique _ _ _ _ (ofGaussian_canonical _ _ he) qone_canonical he r2 r1))

theorem factor_quotient (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qmul (plusValue a b) (inverseFactor a b) ≐ ratio a b := by
  let d := monus b a
  have hd := difference_positive a b h
  have he := positive_product _ _ h.andE₁ hd
  have r := rescale_to (ratio a b) (native (b+a)) d b (b*d) (ofGaussian_represents _ _ hd) (mul_comm _ _)
  have ea : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native ((b+a)*b))
      (ComplexLogarithmRemainder.scale b (native (b+a))) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [native,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;>
      ipra_simps <;> ring
  exact (qmul_congr (plus_fraction a b h.andE₁) (.eqRefl _)).eqTrans
    ((multiply_real_fractions (b+a) b b d h.andE₁ hd).eqTrans
      (canonical_unique _ _ _ _ (ofGaussian_canonical _ _ he) (ofGaussian_canonical _ _ hd) he
        (represents_congr (.eqRefl _) ea (.eqRefl _) (ofGaussian_represents _ _ he)) r))

theorem odd_exponential_ratio (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (expF oddF) constantF
      (expData (num 3) (inputs a b)) (ratio a b) := by
  let F := expF oddF
  let C := constantF
  let X := expData (num 3) (inputs a b)
  let u := minusValue a b
  let v := inverseFactor a b
  let w := plusValue a b
  let P := multiplyF C C
  let p := multiplyData C C u v
  let Q := multiplyF F C
  let q := multiplyData F C X u
  have hf : Γ ⊢[PRAAx] pointCN F X := GaussianRadiusExponentialName.name_regular _ _ _ (odd_input a b h)
  have hu : Γ ⊢[PRAAx] pointCN C u := GaussianGammaCanonicalExponent.constant_regular u
  have hv : Γ ⊢[PRAAx] pointCN C v := GaussianGammaCanonicalExponent.constant_regular v
  have hw : Γ ⊢[PRAAx] pointCN C w := GaussianGammaCanonicalExponent.constant_regular w
  have hon := GaussianNameRingLaws.one_fast (Γ := Γ) X
  have inv := GaussianGammaReciprocalInverse.constant_inverse u v X (factor_inverse a b h)
  have step1 := GaussianGammaAdjacentCutoff.multiply_cross F F oneF P X X X p hf hf hon
    (multiply_fast C C u v hu hv) (cross_refl _ _ hf) (cross_symm _ _ _ _ inv)
  have step2 := cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative F C C X u v hf hu hv)
  have step3 := GaussianGammaAdjacentCutoff.multiply_cross Q C C C q w v v
    (multiply_fast F C X u hf hu) hw hv hv (odd_exponential_product a b h) (cross_refl _ _ hv)
  have step4 := GaussianGammaWeierstrassApproximant.constant_product_cross (Γ := Γ) w v
  have step5 := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (factor_quotient a b h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_one F X hf))
    (cross_trans _ _ _ _ _ _ step1 (cross_trans _ _ _ _ _ _ step2
      (cross_trans _ _ _ _ _ _ step3 (cross_trans _ _ _ _ _ _ step4 step5))))

theorem original_Robin_odd_exponential_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent
      (multiplyF (expF oddF) constantF) constantF
      (multiplyData (expF oddF) constantF (expData (num 3) (inputs (var 0) (var 1))) (minusValue (var 0) (var 1)))
      (plusValue (var 0) (var 1))) :=
  closeUniv 2 (.impI (odd_exponential_product _ _ Prf.hyp0))

theorem original_Robin_odd_exponential_ratio_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent (expF oddF) constantF
      (expData (num 3) (inputs (var 0) (var 1))) (ratio (var 0) (var 1))) :=
  closeUniv 2 (.impI (odd_exponential_ratio _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRobinOddExponential

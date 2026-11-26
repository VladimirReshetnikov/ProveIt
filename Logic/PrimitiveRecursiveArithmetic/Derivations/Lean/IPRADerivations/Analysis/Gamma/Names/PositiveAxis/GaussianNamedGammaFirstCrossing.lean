import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerNamedIBPRecurrence

/-!
# The first Gamma crossing for certified real named inputs

For z greater than one half by a certified reciprocal margin, the equality
of the actual Gamma names at z−1/2 and z+1/2 is equivalent to z being
three halves. The proof uses the original recurrence and the reciprocal of
the unshifted positive Gamma value at one computed anchor.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaFirstCrossing

open_ipra
open GaussianNamedGammaHalfShift (source threeHalves minusF minusData plusF plusData minus_source
  minus_half_reflects_one three_halves_gives_minus_one)
open GaussianNamedGamma (nameF data name_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameRingLaws (oneF one_at one_fast multiply_one multiply_one_left multiply_associative)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (anchor apart)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianRationalReciprocal (qone)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents scalar_congr scalar_same_value)
open ComplexLogarithmRemainder (oneCode re normSq scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedRightHalfPlane (marginPoint)
open RationalValueBounds (upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseClock : PTm n := GaussianFastValueCut.exponent (two*num 18) zero

def crossing (f : PR 2) (x A : PTm n) : Fm PTm n :=
  crossEquivalent (nameF (minusF f)) (nameF (plusF f)) (data (minusData x) A) (data (plusData x) A)

def equalsThreeHalves (f : PR 2) (x : PTm n) : Fm PTm n :=
  crossEquivalent f constantF x (ofGaussian (scale (num 3) oneCode) two)

private theorem margin_scalar (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] fstT (marginPoint A) ≐ fraction one A := by
  have h := ofGaussian_represents oneCode A hA
  have oneEq : Γ ⊢[PRAAx] ZT.eq (re oneCode) (ZT.ofNat one) := by
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact RationalNormalForm.well_formed_unique _ _ (ofGaussian_canonical oneCode A hA).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ hA)
    (scalar_same_value _ _ _ _ hA (scalar_congr (.eqRefl _) oneEq (.eqRefl _) h.andE₁)
      (fraction_represents one A hA))

theorem positive_gamma_apart (f : PR 2) (x A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaPositiveLower.source f x A) :
    Γ ⊢[PRAAx] apart (nameF f) inverseClock (data x A) := by
  let p := anchor (inverseClock : PTm n)
  let q := ap2 (nameF f) p (data x A)
  let z := rawGaussian q
  let D := rawDen q
  let V : PTm n := two*num 18
  let U := unit (inverseClock : PTm n)
  have h18 : Γ ⊢[PRAAx] le one (num 18) := le_of_eq_add (d := num 17) (by ipra_ring)
  have paid : Γ ⊢[PRAAx] le V U :=
    le_congr ((congrMul (.eqRefl V) (pw_zero two)).eqTrans (by ipra_ring)) (.eqRefl _)
      (GaussianFastValueCut.query_budget V zero)
  have grown : Γ ⊢[PRAAx] le U (unit p) :=
    GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have raw := GaussianNamedGammaPositiveLower.original_gamma_positive_lower f p x A h
  have lower := upper_congr (margin_scalar (num 18) h18).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  have margin := GaussianNamedRightHalfPlane.half_margin_from_upper q (num 18) (unit p) h18
    (unit_positive p) (le_trans paid grown) lower
  have pole := GaussianGammaRightHalfPlane.real_margin_pole_at z D V zero margin
  have norm := GaussianRootAlgebra.normSq_equal (GaussianGammaEulerHeadLower.translated_zero (Γ := Γ) z D)
  have first : Γ ⊢[PRAAx] le (D*D) (V*V*normSq z) :=
    le_congr (by ipra_ring) (congrMul (.eqRefl _) norm) pole
  have squares : Γ ⊢[PRAAx] le (V*V) (U*U) :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right V paid)) (mul_le_mul_right U paid)
  exact GaussianRationalLowerBounds.lower_from_representation q z D one U (raw_den_positive q)
    (unit_positive _) (raw_represents q)
    (le_congr (by ipra_ring) (.eqRefl _) (le_trans first (mul_le_mul_right (normSq z) squares)))

private theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF constantF x qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (one_fast _) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalReciprocal.subst_qone] using
    (one_at (var 0) (Syn.shift x)).eqTrans (constant_at (var 0) qone).eqSymm

private theorem remove_factor (f k : PR 2) (x z a : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hk : Γ ⊢[PRAAx] pointCN k z) (ha : Γ ⊢[PRAAx] apart k a z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (multiplyF f k) (GaussianNameReciprocal.nameF k)) f
      (multiplyData (multiplyF f k) (GaussianNameReciprocal.nameF k) (multiplyData f k x z)
        (GaussianNameReciprocal.nameData a z)) x := by
  let I := GaussianNameReciprocal.nameF k
  let i := GaussianNameReciprocal.nameData a z
  have hi := GaussianNameReciprocal.name_fast k a z hk ha
  have hm := multiply_fast k I z i hk hi
  have assoc := multiply_associative f k I x z i hf hk hi
  have prod := cross_trans _ _ _ _ _ _ (GaussianNameReciprocal.product_one k a z hk ha)
    (GaussianBoundedInverseApartness.ones_equivalent z x)
  have lifted := multiply_cross f f (multiplyF k I) oneF x x (multiplyData k I z i) x hf hf hm (one_fast x)
    (cross_refl _ _ hf) prod
  exact cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ lifted (multiply_one f x hf))

theorem cancel_right (f g k : PR 2) (x y z a : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hk : Γ ⊢[PRAAx] pointCN k z) (ha : Γ ⊢[PRAAx] apart k a z)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f k) (multiplyF g k) (multiplyData f k x z) (multiplyData g k y z)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  let I := GaussianNameReciprocal.nameF k
  let i := GaussianNameReciprocal.nameData a z
  have hi := GaussianNameReciprocal.name_fast k a z hk ha
  have middle := multiply_cross (multiplyF f k) (multiplyF g k) I I _ _ i i
    (multiply_fast _ _ _ _ hf hk) (multiply_fast _ _ _ _ hg hk) hi hi he (cross_refl _ _ hi)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (remove_factor f k x z a hf hk ha))
    (cross_trans _ _ _ _ _ _ middle (remove_factor g k y z a hg hk ha))

theorem crossing_implies_three_halves (f : PR 2) (x A : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A) (he : Γ ⊢[PRAAx] crossing f x A) :
    Γ ⊢[PRAAx] equalsThreeHalves f x := by
  let L := minusF f
  let u := minusData x
  let G := nameF L
  let v := data u A
  have h := minus_source f x A hs
  have hG := name_regular L u A h.andE₁
  have recurrence := GaussianEulerNamedIBPRecurrence.original_named_Gamma_IBP_recurrence L u A h.andE₁
  have product := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ recurrence)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ he)
      (cross_symm _ _ _ _ (multiply_one_left G v hG)))
  have unitFactor := cancel_right L oneF G u v v inverseClock h.andE₁.andE₁ (one_fast v) hG
    (positive_gamma_apart L u A h) product
  have shifted := minus_half_reflects_one f x hs.andE₁ (cross_trans _ _ _ _ _ _ unitFactor (one_constant v))
  exact cross_trans _ _ _ _ _ _ shifted
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ GaussianNamedGammaHalfShift.three_halves_exact)

theorem three_halves_implies_crossing (f : PR 2) (x A : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A) (he : Γ ⊢[PRAAx] equalsThreeHalves f x) :
    Γ ⊢[PRAAx] crossing f x A := by
  let L := minusF f
  let u := minusData x
  let G := nameF L
  let v := data u A
  have h := minus_source f x A hs
  have hG := name_regular L u A h.andE₁
  have recur := GaussianEulerNamedIBPRecurrence.original_named_Gamma_IBP_recurrence L u A h.andE₁
  have converted : Γ ⊢[PRAAx] crossEquivalent f constantF x threeHalves :=
    cross_trans _ _ _ _ _ _ he
      (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ GaussianNamedGammaHalfShift.three_halves_exact.eqSymm)
  have minusOne := cross_trans _ _ _ _ _ _ (three_halves_gives_minus_one f x hs.andE₁ converted)
    (cross_symm _ _ _ _ (one_constant v))
  have rhs := multiply_cross L oneF G G u v v v h.andE₁.andE₁ (one_fast v) hG hG minusOne (cross_refl _ _ hG)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ recur
    (cross_trans _ _ _ _ _ _ rhs (multiply_one_left G v hG)))

theorem actual_original_named_Gamma_first_crossing_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ Fm.iff (crossing f (var 0) (var 1)) (equalsThreeHalves f (var 0))) :=
  closeUniv 2 (.impI (.andI (.impI (crossing_implies_three_halves f _ _ Prf.hyp1 Prf.hyp0))
    (.impI (three_halves_implies_crossing f _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaFirstCrossing

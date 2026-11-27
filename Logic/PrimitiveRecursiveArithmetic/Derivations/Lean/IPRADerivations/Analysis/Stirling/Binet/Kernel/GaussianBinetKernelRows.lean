import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelPi
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.Lattice.GaussianEulerPositivePowerChartCorrectedImage
import IPRADerivations.Analysis.Gamma.HalfInteger.EulerProducts.GaussianGammaHalfEulerSquare
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# The actual positive Binet kernel rows

The zero-based row i is 2/(t²+4π²(i+1)²). Its observations evaluate the
actual π name at the requested precision, and the original rational
reciprocal is protected by a quantitative positive denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelRows

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq oneCode scale)
open GaussianBinetKernelPi (sample sample_fraction sample_margins sample_bound sample_distance denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianNamedFiniteProductFamily (regularRows subst_regularRows)
open GaussianNameArithmetic (product_distance)
open GaussianNameReciprocal (inverse_difference)
open GaussianNameRingLaws (sum_right_error)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (positive positive_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qadd qmul ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded comparison_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal
  (reciprocal reciprocal_canonical reciprocal_identity normLower norm_positive inverse_bound bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianStirlingConstant (piNumerator piDenominator)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def weight (i : PTm n) : PTm n := num 4*(i*i)
def denominatorLower (i : PTm n) : PTm n := num 16*(i*i)

def denominator (A B i π : PTm n) : PTm n :=
  qadd (qmul (fraction A B) (fraction A B)) (qmul (fraction (weight i) one) (qmul π π))

def nativeNum (A B i u v : PTm n) : PTm n :=
  A*A*(v*v)+(weight i*(u*u))*(B*B)

def nativeDen (B v : PTm n) : PTm n := (B*B)*(v*v)

def value (p i A B : PTm n) : PTm n :=
  qmul (fraction two one) (reciprocal (denominator A B i (sample p)))

ipra_subst value [denominator, weight, one, two]

private theorem denominator_fraction (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] denominator A B i (sample p) ≐
      fraction (nativeNum A B i (piNumerator p) (piDenominator p)) (nativeDen B (piDenominator p)) := by
  let u := piNumerator p
  let v := piDenominator p
  let w := weight i
  have hv := denominator_positive (Γ := Γ) p
  have hvv := positive_product v v hv hv
  have e := sample_fraction (Γ := Γ) p
  have piSquare := (qmul_congr e e).eqTrans (fraction_product u v u v hv hv)
  have weighted := (qmul_congr (.eqRefl (fraction w one)) piSquare).eqTrans
    ((fraction_product w one (u*u) (v*v) (le_refl one) hvv).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul _)))
  have tSquare := fraction_product A B A B hB hB
  exact (qadd_congr tSquare weighted).eqTrans (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum
    (A*A) (B*B) (w*(u*u)) (v*v) (positive_product B B hB hB) hvv)

private theorem lower_positive (i : PTm n) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] le one (denominatorLower i) :=
  positive_product _ _ (by ipra_le 15) (positive_product i i hi hi)

private theorem native_den_positive (p B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (nativeDen B (piDenominator p)) := by
  have h := denominator_positive (Γ := Γ) p
  exact positive_product _ _ (positive_product B B hB hB)
    (positive_product _ _ h h)

private theorem denominator_cleared_lower (p i A B : PTm n) :
    Γ ⊢[PRAAx] le (denominatorLower i*nativeDen B (piDenominator p))
      (nativeNum A B i (piNumerator p) (piDenominator p)) := by
  have hp := (sample_margins (Γ := Γ) p).andE₁
  have mul := le_mul_mono (le_refl (weight i*(B*B))) (le_mul_mono hp hp)
  unfold nativeNum
  refine le_trans ?_ (le_add_left _ _)
  exact le_congr (by unfold denominatorLower nativeDen weight; ipra_ring) (by ipra_ring) mul

private theorem native_num_positive (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] le one (nativeNum A B i (piNumerator p) (piDenominator p)) :=
  le_trans (positive_product _ _ (lower_positive i hi) (native_den_positive p B hB))
    (denominator_cleared_lower p i A B)

theorem denominator_lower (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] normLower (denominator A B i (sample p)) (denominatorLower i) := by
  let N := nativeNum A B i (piNumerator p) (piDenominator p)
  let D := nativeDen B (piDenominator p)
  let R := denominatorLower i
  have hd := native_den_positive p B hB
  have cleared := sq_le_sq (denominator_cleared_lower (Γ := Γ) p i A B)
  have norm : Γ ⊢[PRAAx] normSq (scale N oneCode) ≐ N*N :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have lower := GaussianRationalLowerBounds.lower_from_representation (fraction N D) (scale N oneCode)
    D R one hd (le_refl one) (ofGaussian_represents _ _ hd)
    (le_congr (by ipra_ring)
      (norm.eqSymm.eqTrans (by ipra_ring)) cleared)
  exact GaussianRationalLowerBounds.lower_congr (denominator_fraction p i A B hB).eqSymm
    (.eqRefl _) (.eqRefl _) lower

theorem value_fraction (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] value p i A B ≐ fraction (two*nativeDen B (piDenominator p))
      (nativeNum A B i (piNumerator p) (piDenominator p)) := by
  let N := nativeNum A B i (piNumerator p) (piDenominator p)
  let D := nativeDen B (piDenominator p)
  let w := denominator A B i (sample p)
  have hd := native_den_positive p B hB
  have hn := native_num_positive p i A B hB hi
  have hnorm := norm_positive w (denominatorLower i) (lower_positive i hi) (denominator_lower p i A B hB)
  have prod := (qmul_congr (denominator_fraction p i A B hB) (.eqRefl (fraction D N))).eqTrans
    (GaussianGammaHalfEulerSquare.inverse_fraction N D hn hd)
  have inv := GaussianEulerBetaProductPascal.inverse_unique w (reciprocal w) (fraction D N)
    (reciprocal_canonical w) (ofGaussian_canonical _ _ hn) (reciprocal_identity w hnorm) prod
  exact (qmul_congr (.eqRefl (fraction two one)) inv).eqTrans
    ((fraction_product two one D N (le_refl one) hn).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul _)))

private theorem natural_coefficient_bound (C : PTm n) : Γ ⊢[PRAAx] bounded (fraction C one) C one :=
  GaussianEulerExponentCompactBounds.fraction_bound C one C (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl C))

private theorem natural_multiply_distance (C u v E D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded u v E D) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction C one) u) (qmul (fraction C one) v) (C*E) D :=
  GaussianRationalRoundedPower.distance_mul_left_one hD (natural_coefficient_bound C) h

private theorem inverse_distance (u v R E D : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] normLower u R) (hv : Γ ⊢[PRAAx] normLower v R)
    (h : Γ ⊢[PRAAx] distanceBounded u v E D) :
    Γ ⊢[PRAAx] distanceBounded (reciprocal u) (reciprocal v) E (D*(R*R)) := by
  have left := bounded_product (reciprocal u) (qsub v u) one R E D hR hD
    (inverse_bound u R hR hu) (distance_symmetric u v E D hD h)
  have both := bounded_product (qmul (reciprocal u) (qsub v u)) (reciprocal v) (one*E) (R*D) one R
    (positive_product R D hR hD) hR left (inverse_bound v R hR hv)
  exact bound_congr (inverse_difference u v (norm_positive u R hR hu) (norm_positive v R hR hv)).eqSymm
    (by ipra_ring) (by ipra_ring) both

theorem value_distance (p q i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le one i) :
    Γ ⊢[PRAAx] distanceBounded (value p i A B) (value q i A B) (unit p+unit q) (unit p*unit q) := by
  let x := sample p
  let y := sample q
  let t := fraction A B
  let w := weight i
  let E := unit p+unit q
  let D := unit p*unit q
  let R := denominatorLower i
  let u := denominator A B i x
  let v := denominator A B i y
  have hD := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have hR := lower_positive i hi
  have hh := sample_distance (Γ := Γ) p q
  have x2 := product_distance x y x y E E D (num 5) (num 5) hD hh hh (sample_bound p) (sample_bound q)
  have weighted := natural_multiply_distance w _ _ _ D hD x2
  have den := sum_right_error (qmul t t) _ _ _ D hD weighted
  have inv := inverse_distance u v R _ D hR hD (denominator_lower p i A B hB) (denominator_lower q i A B hB) den
  have ht := positive_product _ _ hD (positive_product R R hR hR)
  have raw := natural_multiply_distance two _ _ _ _ ht inv
  have hs := positive_product (Γ := Γ) i i hi hi
  exact distance_radius_mono _ _ _ _ E D ht hD
    (by
      dsimp only [w, R, D, weight, denominatorLower]
      ipra_le (256*𝔞(i*i)*𝔞(E)*𝔞(unit p*unit q))*sl hs +
        176*𝔞(i*i)*𝔞(E)*𝔞(unit p*unit q)) raw

def inputData (A B : PTm n) : PTm n := pairT A B
def rowData (i A B : PTm n) : PTm n := pairT (succ i) (inputData A B)
def rowBody : PTm 2 := pairT (succ (var 0)) (var 1)
def rowF : PR 2 := PTm.toPR
  (value (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

ipra_subst inputData

ipra_subst rowData

theorem row_at (i A B : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (inputData A B) ≐ rowData i A B := by
  simpa [rowBody, rowData, inst2] using (Prf.eqRefl (rowData i A B) : Γ ⊢[PRAAx] _)

theorem row_sample (p i A B : PTm n) : Γ ⊢[PRAAx] ap2 rowF p (rowData i A B) ≐ value p (succ i) A B := by
  simpa [rowF, rowData, inputData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (value (var 0) (var 1) (var 2) (var 3)) p ![succ i, A, B])

theorem row_regular (i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pointCN rowF (rowData i A B) := by
  refine .allI (.allI ?_)
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ, sh, Fm.shift, Syn.shift, one] using hB.shift.shift
  simpa only [pointCN, Syn.shift, sh, subst_rowData, GaussianEuclideanPointDistance.unit, unit, Δ] using
    distance_congr (row_sample (Γ := Δ) (var 1) (sh i) (sh A) (sh B)).eqSymm
      (row_sample (var 0) (sh i) (sh A) (sh B)).eqSymm (.eqRefl _) (.eqRefl _)
      (value_distance (var 1) (var 0) (succ (sh i)) (sh A) (sh B) hs (zero_lt_succ _))

theorem regular_rows (N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] regularRows rowF rowBody N (inputData A B) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ, sh, Fm.shift, Syn.shift, one] using hB.shift.wk
  have bound := GaussianGammaCompactCutoffSplit.point_data_congr rowF _ _
    (row_at (Γ := Δ) (var 0) (sh A) (sh B)).eqSymm (row_regular (var 0) (sh A) (sh B) hh)
  simpa only [regularRows, Syn.shift, sh, subst_inputData, Δ] using bound

theorem row_positive (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] positive (ap2 rowF p (rowData i A B)) := by
  have value := (row_sample (Γ := Γ) p i A B).eqTrans (value_fraction p (succ i) A B hB (zero_lt_succ i))
  exact positive_congr value.eqSymm
    (GaussianEulerPositivePowerChartOrder.fraction_positive _ _ (native_num_positive p (succ i) A B hB (zero_lt_succ i)))

theorem row_bound (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 rowF p (rowData i A B)) one (num 8*(succ i*succ i)) := by
  let u := denominator A B (succ i) (sample p)
  let R := denominatorLower (succ i)
  let D := num 8*(succ i*succ i)
  have hn := zero_lt_succ (Γ := Γ) i
  have hR := lower_positive _ hn
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (by ipra_le 7) (positive_product _ _ hn hn)
  have raw := bounded_product (fraction two one) (reciprocal u) two one one R (le_refl one) hR
    (natural_coefficient_bound two) (inverse_bound u R hR (denominator_lower p (succ i) A B hB))
  exact bound_congr (row_sample p i A B).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
      (positive_product _ _ (le_refl one) hR) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,R,denominatorLower]; ipra_ring)) raw)

theorem row_majorized (p i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRationalSumMajorant.majorized (ap2 rowF p (rowData i A B))
      (fstT (fraction one (num 8*(succ i*succ i)))) := by
  let D := num 8*(succ i*succ i)
  have hn := zero_lt_succ (Γ := Γ) i
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (by ipra_le 7) (positive_product _ _ hn hn)
  have rep := fraction_first_represents (Γ := Γ) one D hD
  exact GaussianRationalSumMajorant.from_representation _ _ one D hD
    (GaussianRationalL1.nonnegative_of_representation _ _ _ hD rep) rep (row_bound p i A B hB)

def lowerDenominator (T i : PTm n) : PTm n := T*T+num 100*(succ i*succ i)

ipra_subst lowerDenominator

theorem lower_denominator_positive (T i : PTm n) :
    Γ ⊢[PRAAx] le one (lowerDenominator T i) :=
  le_trans (positive_product _ _ (by ipra_le 99) (positive_product _ _ (zero_lt_succ i) (zero_lt_succ i)))
    (le_add_left _ _)

theorem row_lower (p i A B T : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction two (lowerDenominator T i))) (fstT (ap2 rowF p (rowData i A B))) := by
  let u := piNumerator p
  let v := piDenominator p
  let j := succ i
  let N := nativeNum A B j u v
  let D := nativeDen B v
  let L := lowerDenominator T i
  have positive := zero_lt_succ (Γ := Γ) i
  have hn := native_num_positive p j A B hB positive
  have hl := lower_denominator_positive (Γ := Γ) T i
  have hi := (sample_margins (Γ := Γ) p).andE₂
  have tSquare := le_mul_mono (sq_le_sq hT) (le_refl (v*v))
  have piSquare := le_mul_mono (le_mul_mono (le_refl (weight j)) (sq_le_sq hi)) (le_refl (B*B))
  have upper : Γ ⊢[PRAAx] le N (L*D) :=
    le_congr (.eqRefl _) (by dsimp only [L, D, j, lowerDenominator, nativeDen, weight]; ipra_ring)
      (add_le_add₂ tSquare piSquare)
  have exact := (row_sample (Γ := Γ) p i A B).eqTrans (value_fraction p j A B hB positive)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (congrFst exact).eqSymm
    (comparison_of_cleared _ _ two (two*D) L N hl hn
      (fraction_first_represents two L hl) (fraction_first_represents (two*D) N hn)
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right two upper)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelRows

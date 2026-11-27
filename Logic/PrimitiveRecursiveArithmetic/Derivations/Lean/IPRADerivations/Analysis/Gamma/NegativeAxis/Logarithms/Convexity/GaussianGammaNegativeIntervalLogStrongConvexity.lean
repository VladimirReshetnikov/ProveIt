import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.AbsoluteValues.GaussianGammaNegativeIntervalLogAbsolute
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.Convexity.GaussianGammaNegativeIntervalInverseLogConvexity
import IPRADerivations.Analysis.Gamma.Convexity.GaussianGammaNativeStrongLogConvexity

/-!
# Strong log-absolute convexity on a rational negative interval

The positive log-Gamma term contributes the quadratic margin on (1,2).
The logarithm of the inverse shift product contributes a weak chord
inequality. The two inequalities combine at the actual log-absolute
names and their original normalized arithmetic.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogStrongConvexity

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaEulerRationalLogConvexity (center_positive center_denominator_positive)
open GaussianGammaEulerRationalLogOrder (add_order add_interleave)
open GaussianGammaNativeLogConvexityCore (nativeWeightedData)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData inverseLogData name_regular terminal_source)
open GaussianGammaNegativeIntervalProductConvexity (center_guard)
open GaussianHarmonicWeightedQuadraticValue (gapCode)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative distributive)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_data_congr scale_cross)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "L" => GaussianPositiveRationalLogarithm.logF
local notation "G" => productF logGammaF
local notation "V" => productF L

def scaledF : PR 2 := productF nameF

def centerData (a b c N r s : PTm n) : PTm n :=
  productData nameF (weight r s) (nameData (barycenter a c r s) (weight r s*b) N)

def weightedData (a b c N r s : PTm n) : PTm n :=
  addData (productData nameF (succ r) (nameData a b N)) (productData nameF s (nameData c b N))

def margin (a b c r s : PTm n) : PTm n := gapCode (b+a) (b+c) (two*b) r s

def lowerData (a b c N r s : PTm n) : PTm n := addData (margin a b c r s) (centerData a b c N r s)

ipra_subst centerData [weight, barycenter]

ipra_subst weightedData

ipra_subst margin [two]

ipra_subst lowerData

private theorem scale_regular (f : PR 2) (w x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (productF f) (productData f w x) :=
  multiply_fast constantF f (naturalPoint w) x (constant_regular _) h

private theorem center_numerator (a b c r s : PTm n) : Γ ⊢[PRAAx]
    barycenter (b+a) (b+c) r s ≐ weight r s*b+barycenter a c r s := by
  unfold barycenter weight
  ipra_ring

private theorem positive_shifted_center (a b c r s : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) : Γ ⊢[PRAAx]
    crossEquivalent G G
      (productData logGammaF (weight r s) (logGammaData (weight r s*b+barycenter a c r s) (weight r s*b)))
      (productData logGammaF (weight r s) (logGammaData (barycenter (b+a) (b+c) r s) (weight r s*b))) := by
  let W := weight r s
  let D := W*b
  let t := barycenter a c r s
  let p := barycenter (b+a) (b+c) r s
  let x := logGammaData (D+t) D
  let y := logGammaData p D
  have ht := center_guard a b c r s h.andE₁ hc.andE₁ h.andE₂ hc.andE₂
  have hs := terminal_source a b h
  have hx := log_gamma_regular (D+t) D (terminal_source t D ht)
  have hy := log_gamma_regular p D
    (.andI (center_positive (b+a) (b+c) r s hs.andE₁) (center_denominator_positive b r s hs.andE₂))
  have eq := gamma_data_congr _ _ _ _ (center_numerator (Γ := Γ) a b c r s).eqSymm (.eqRefl D)
  have same := GaussianGammaCompactCutoffAlignment.cross_data_congr logGammaF logGammaF x x x y
    (.eqRefl x) eq (cross_refl logGammaF x hx)
  exact scale_cross W W x y (.eqRefl W) hx hy same

theorem strong_convexity_of_inverse (a b c N r s : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (hac : Γ ⊢[PRAAx] le a c)
    (hi : Γ ⊢[PRAAx] realOrder V (addF V V)
      (productData L (weight r s) (inverseLogData (barycenter a c r s) (weight r s*b) N))
      (addData (productData L (succ r) (inverseLogData a b N)) (productData L s (inverseLogData c b N)))) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF scaledF)
      (lowerData a b c N r s) (weightedData a b c N r s) := by
  let W := weight r s
  let D := W*b
  let t := barycenter a c r s
  let P := barycenter (b+a) (b+c) r s
  let q := margin a b c r s
  let x := logGammaData (D+t) D
  let y := logGammaData (b+a) b
  let z := logGammaData (b+c) b
  let X := inverseLogData t D N
  let Y := inverseLogData a b N
  let Z := inverseLogData c b N
  let px := productData logGammaF W x
  let py := productData logGammaF (succ r) y
  let pz := productData logGammaF s z
  let ix := productData L W X
  let iy := productData L (succ r) Y
  let iz := productData L s Z
  let cpos := productData logGammaF W (logGammaData P D)
  have hA := terminal_source a b ha
  have hC := terminal_source c b hc
  have hT := center_guard a b c r s ha.andE₁ hc.andE₁ ha.andE₂ hc.andE₂
  have hpX := log_gamma_regular _ _ (terminal_source t D hT)
  have hpY := log_gamma_regular _ _ hA
  have hpZ := log_gamma_regular _ _ hC
  have hiX : Γ ⊢[PRAAx] pointCN L X := GaussianPositiveRationalLogarithm.name_regular _ _
    (GaussianGammaNegativeIntervalLogAbsolute.inverse_source t D N hT)
  have hiY : Γ ⊢[PRAAx] pointCN L Y := GaussianPositiveRationalLogarithm.name_regular _ _
    (GaussianGammaNegativeIntervalLogAbsolute.inverse_source a b N ha)
  have hiZ : Γ ⊢[PRAAx] pointCN L Z := GaussianPositiveRationalLogarithm.name_regular _ _
    (GaussianGammaNegativeIntervalLogAbsolute.inverse_source c b N hc)
  have cq : Γ ⊢[PRAAx] pointCN C q := constant_regular q
  have cx := scale_regular logGammaF W x hpX
  have cy := scale_regular logGammaF (succ r) y hpY
  have cz := scale_regular logGammaF s z hpZ
  have lx := scale_regular L W X hiX
  have ly := scale_regular L (succ r) Y hiY
  have lz := scale_regular L s Z hiZ
  have hPos : Γ ⊢[PRAAx] source P D :=
    .andI (center_positive (b+a) (b+c) r s hA.andE₁) (center_denominator_positive b r s hA.andE₂)
  have cp := scale_regular logGammaF W (logGammaData P D) (log_gamma_regular _ _ hPos)
  have shifted := positive_shifted_center a b c r s ha hc
  have bound : Γ ⊢[PRAAx] le (b+c) (two*b) := le_congr (add_comm _ _) (by ipra_ring)
    (add_le_add_right b (le_of_lt hc.andE₂))
  have ordered : Γ ⊢[PRAAx] le (b+a) (b+c) :=
    add_le_add_left b hac
  have base := GaussianGammaNativeStrongLogConvexity.strong_convexity (b+a) (b+c) b (two*b) r s
    hA.andE₁ ordered hA.andE₂ bound
  have both := add_order (addF C G) (addF G G) V (addF V V) (addData q cpos)
    (nativeWeightedData (b+a) (b+c) b r s) ix (addData iy iz) base hi
  have split := distributive C logGammaF L (naturalPoint W) x X (constant_regular _) hpX hiX
  have leftReg := scale_regular nameF W (nameData t D N) (name_regular t D N hT)
  have mapped := add_cross C C scaledF (addF G V) q q (centerData a b c N r s) (addData px ix)
    cq cq leftReg (add_fast G V px ix cx lx) (cross_refl C q cq) split
  have shift := add_cross G G V V px cpos ix ix cx cp lx lx shifted (cross_refl V ix lx)
  have next := add_cross C C (addF G V) (addF G V) q q (addData px ix) (addData cpos ix)
    cq cq (add_fast G V px ix cx lx) (add_fast G V cpos ix cp lx) (cross_refl C q cq) shift
  have lhs := cross_trans _ _ _ _ _ _ mapped (cross_trans _ _ _ _ _ _ next
    (cross_symm _ _ _ _ (add_associative C G V q cpos ix cq cp lx)))
  have separate := add_interleave G G V V py pz iy iz cy cz ly lz
  have split_left := distributive C logGammaF L (naturalPoint (succ r)) y Y (constant_regular _) hpY hiY
  have split_right := distributive C logGammaF L (naturalPoint s) z Z (constant_regular _) hpZ hiZ
  have merge := add_cross (addF G V) scaledF (addF G V) scaledF (addData py iy)
    (productData nameF (succ r) (nameData a b N)) (addData pz iz) (productData nameF s (nameData c b N))
    (add_fast G V py iy cy ly) (scale_regular nameF (succ r) _ (name_regular a b N ha))
    (add_fast G V pz iz cz lz) (scale_regular nameF s _ (name_regular c b N hc))
    (cross_symm _ _ _ _ split_left) (cross_symm _ _ _ _ split_right)
  have rhs := cross_trans _ _ _ _ _ _ separate merge
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ lhs rhs both

theorem strong_convexity (a b c N r s : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] realOrder (addF C scaledF) (addF scaledF scaledF)
      (lowerData a b c N r s) (weightedData a b c N r s) :=
  strong_convexity_of_inverse a b c N r s ha hc hac
    (GaussianGammaNegativeIntervalInverseLogConvexity.weighted_order a b c N r s ha hc)

theorem actual_original_negative_interval_strong_log_absolute_convexity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 0) (var 1) ⋏ (guard (var 2) (var 1) ⋏ le (var 0) (var 2))) ⟶
        realOrder (addF C scaledF) (addF scaledF scaledF)
          (lowerData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
          (weightedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (strong_convexity _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogStrongConvexity

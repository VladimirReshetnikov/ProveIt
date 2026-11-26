import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerNormalizedHead
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyRange
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalRatioBinding
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference

/-!
# Differences of finite Euler logarithm heads

Split the original residual family at the numerical index N. The
common initial logarithm and the common residual prefix cancel. The
remaining product uses the original input z times the difference of
the two positive integer logarithms. All equivalences use independent
observations of the actual names.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalizedDifference

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument productF productData rowData)
open GaussianLogGammaEulerFactorSum (residualF residualBody residual_rows residual_at)
open GaussianLogGammaEulerNormalizedHead (product_regular denominatorF denominatorData denominator_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative distributive equivalent_of_envelope through_identity)
open GaussianNamedDifference (name_regular sample_error difference_distance)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "sd" => GaussianNamedFiniteSumFamily.data
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "F" => GaussianLogGammaEulerNormalizedHead.nameF
local notation "head" => GaussianLogGammaEulerNormalizedHead.data

def rangeF : PR 2 := GaussianNamedFiniteSumFamily.nameF G (GaussianNamedFiniteSumFamilyRange.rangeBody residualBody)
def rangeData (A B D neg N r : PTm n) : PTm n :=
  GaussianNamedFiniteSumFamilyRange.rangeData N r (rowData A B D neg)

ipra_subst rangeData

def weightedLogF : PR 2 := multiplyF constantF (diffF logF logF)
def weightedLogData (A B D neg N r : PTm n) : PTm n :=
  multiplyData constantF (diffF logF logF) (argument A B D neg) (diffData (L (N+r) one) (L N one))

def windowF : PR 2 := diffF weightedLogF rangeF
def windowData (A B D neg N r : PTm n) : PTm n :=
  diffData (weightedLogData A B D neg N r) (rangeData A B D neg N r)

ipra_subst windowData [weightedLogData, argument, ZT.subst, ZT.ofNat, one]

theorem range_row_at (A B D neg N i : PTm n) : Γ ⊢[PRAAx]
    inst2 (GaussianNamedFiniteSumFamilyRange.rangeBody residualBody) i (pairT N (rowData A B D neg)) ≐
      P (A+succ (N+i)*D) B (D*succ (N+i)) neg :=
  (GaussianNamedFiniteSumFamilyRange.range_row_at residualBody N i (rowData A B D neg)).eqTrans
    (residual_at (N+i) A B D neg)

theorem range_regular (A B D neg N r : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN rangeF (rangeData A B D neg N r) :=
  GaussianNamedFiniteSumFamilyRange.range_regular G residualBody N r (rowData A B D neg)
    (residual_rows A B D neg (N+r) h)

theorem weighted_log_regular (A B D neg N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN weightedLogF (weightedLogData A B D neg N r) := by
  have hM := le_trans hN (le_add_right N r)
  have hX := GaussianPositiveRationalLogarithm.name_regular (N+r) one (.andI hM (le_refl one))
  have hY := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  exact multiply_fast _ _ _ _ (constant_regular _) (name_regular logF logF _ _ hX hY)

theorem window_regular (A B D neg N r : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN windowF (windowData A B D neg N r) :=
  name_regular _ _ _ _ (weighted_log_regular A B D neg N r hN) (range_regular A B D neg N r h)

private theorem difference_of_differences_at (f g h j : PR 2) (x y u v p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hj : Γ ⊢[PRAAx] pointCN j v) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (diffF (diffF f g) (diffF h j)) p (diffData (diffData x y) (diffData u v)))
      (qsub (qsub (ap2 f p x) (ap2 g p y)) (qsub (ap2 h p u) (ap2 j p v))) (num 18) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have outer := sample_error (diffF f g) (diffF h j) (diffData x y) (diffData u v) p
    (name_regular f g x y hf hg) (name_regular h j u v hh hj)
  have inner := difference_distance _ _ _ _ _ _ _ hp (sample_error f g x y p hf hg) (sample_error h j u v p hh hj)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp outer inner)

private theorem exchange_at (f g h j : PR 2) (x y u v p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hj : Γ ⊢[PRAAx] pointCN j v) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (diffF (diffF f g) (diffF h j)) p (diffData (diffData x y) (diffData u v)))
      (ap2 (diffF (diffF f h) (diffF g j)) p (diffData (diffData x u) (diffData y v))) (num 36) (unit p) := by
  let a := ap2 f p x
  let b := ap2 g p y
  let c := ap2 h p u
  let d := ap2 j p v
  have algebra : Γ ⊢[PRAAx] qsub (qsub a b) (qsub c d) ≐ qsub (qsub a c) (qsub b d) :=
    (GaussianNameArithmetic.sum_difference a c (qnegative b) (qnegative d)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (GaussianCharacteristicEntryNorm.negative_difference b d))
  have left := difference_of_differences_at f g h j x y u v p hf hg hh hj
  have right := difference_of_differences_at f h g j x u y v p hf hh hg hj
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (through_identity _ _ _ _ _ _ _ (unit_positive p) left right algebra)

private theorem exchange (f g h j : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hj : Γ ⊢[PRAAx] pointCN j v) :
    Γ ⊢[PRAAx] crossEquivalent (diffF (diffF f g) (diffF h j)) (diffF (diffF f h) (diffF g j))
      (diffData (diffData x y) (diffData u v)) (diffData (diffData x u) (diffData y v)) := by
  refine equivalent_of_envelope _ _ _ _ (num 36)
    (name_regular _ _ _ _ (name_regular f g x y hf hg) (name_regular h j u v hh hj))
    (name_regular _ _ _ _ (name_regular f h x u hf hh) (name_regular g j y v hg hj)) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have hF : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa only [Δ,sh,Fm.shift,subst_pointCN,Syn.shift] using hf.shift
  have hG : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa only [Δ,sh,Fm.shift,subst_pointCN,Syn.shift] using hg.shift
  have hH : Δ ⊢[PRAAx] pointCN h (sh u) := by simpa only [Δ,sh,Fm.shift,subst_pointCN,Syn.shift] using hh.shift
  have hJ : Δ ⊢[PRAAx] pointCN j (sh v) := by simpa only [Δ,sh,Fm.shift,subst_pointCN,Syn.shift] using hj.shift
  simpa only [Syn.shift,sh,GaussianNamedDifference.subst_data,PTm.subst_num] using
    exchange_at f g h j (sh x) (sh y) (sh u) (sh v) (var 0) hF hG hH hJ

private theorem product_difference (C f g : PR 2) (c x y : PTm n)
    (hc : Γ ⊢[PRAAx] pointCN C c) (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (diffF (multiplyF C f) (multiplyF C g)) (multiplyF C (diffF f g))
      (diffData (multiplyData C f c x) (multiplyData C g c y)) (multiplyData C (diffF f g) c (diffData x y)) := by
  let E := diffF f g
  let d := diffData x y
  let A := multiplyF C f
  let B := multiplyF C g
  let T := multiplyF C E
  let a := multiplyData C f c x
  let b := multiplyData C g c y
  let t := multiplyData C E c d
  have he := name_regular f g x y hf hg
  have hA := multiply_fast C f c x hc hf
  have hB := multiply_fast C g c y hc hg
  have hT := multiply_fast C E c d hc he
  have recover := GaussianGammaRationalRatioBinding.difference_add_recover f g x y hf hg
  have lifted := multiply_cross C C f (addF E g) c c x (addData d y) hc hc hf (add_fast E g d y he hg)
    (cross_refl _ _ hc) (cross_symm _ _ _ _ recover)
  have expand := cross_trans _ _ _ _ _ _ lifted (distributive C E g c d y hc he hg)
  have move := difference_proper A (addF T B) B B a (addData t b) b b hA
    (add_fast T B t b hT hB) hB hB expand (cross_refl _ _ hB)
  exact cross_trans _ _ _ _ _ _ move (GaussianNamedStrictOrderDifference.sum_sub_right T B t b hT hB)

theorem denominator_difference (A B D neg N r : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (diffF denominatorF denominatorF) rangeF
      (diffData (denominatorData A B D neg (N+r)) (denominatorData A B D neg N)) (rangeData A B D neg N r) := by
  let x := rowData A B D neg
  let z := P A B D neg
  let a := sd (N+r) x
  let b := sd N x
  let c := rangeData A B D neg N r
  let u := denominatorData A B D neg (N+r)
  let v := denominatorData A B D neg N
  have hZ := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have hA := GaussianNamedFiniteSumFamily.regular G residualBody (N+r) x (residual_rows A B D neg (N+r) h)
  have hB := GaussianNamedFiniteSumFamily.regular G residualBody N x (residual_rows A B D neg N h)
  have hC := range_regular A B D neg N r h
  have hU := denominator_regular A B D neg (N+r) h
  have hV := denominator_regular A B D neg N h
  have rows := GaussianNamedFiniteSumFamilyRange.range_cross G residualBody N r x (residual_rows A B D neg (N+r) h)
  have split := add_cross G G residualF (addF residualF rangeF) z z a (addData b c)
    hZ hZ hA (add_fast _ _ _ _ hB hC) (cross_refl _ _ hZ) rows
  have grouped := cross_trans _ _ _ _ _ _ split
    (cross_symm _ _ _ _ (add_associative G residualF rangeF z b c hZ hB hC))
  have reversed := cross_trans _ _ _ _ _ _ grouped (add_commutative denominatorF rangeF v c hV hC)
  have replace := difference_proper denominatorF (addF rangeF denominatorF) denominatorF denominatorF
    u (addData c v) v v hU (add_fast _ _ _ _ hC hV) hV hV reversed (cross_refl _ _ hV)
  exact cross_trans _ _ _ _ _ _ replace (GaussianNamedStrictOrderDifference.sum_sub_right rangeF denominatorF c v hC hV)

theorem equivalent (A B D neg N r : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (diffF F F) windowF
      (diffData (head A B D neg (N+r)) (head A B D neg N)) (windowData A B D neg N r) := by
  let M := N+r
  let a := productData A B D neg M
  let b := productData A B D neg N
  let u := denominatorData A B D neg M
  let v := denominatorData A B D neg N
  have hM : Γ ⊢[PRAAx] le one M := le_trans hN (le_add_right N r)
  have hA := product_regular A B D neg M hM
  have hB := product_regular A B D neg N hN
  have hU := denominator_regular A B D neg M h
  have hV := denominator_regular A B D neg N h
  have split := exchange productF denominatorF productF denominatorF a u b v hA hU hB hV
  have product := product_difference constantF logF logF (argument A B D neg) (L M one) (L N one)
    (constant_regular _) (GaussianPositiveRationalLogarithm.name_regular M one (.andI hM (le_refl one)))
    (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one)))
  have reduced := difference_proper (diffF productF productF) weightedLogF (diffF denominatorF denominatorF) rangeF
    (diffData a b) (weightedLogData A B D neg N r) (diffData u v) (rangeData A B D neg N r)
    (name_regular _ _ _ _ hA hB) (weighted_log_regular A B D neg N r hN)
    (name_regular _ _ _ _ hU hV) (range_regular A B D neg N r h) product (denominator_difference A B D neg N r h)
  exact cross_trans _ _ _ _ _ _ split reduced

theorem original_equivalent (A B D neg N r : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (diffF GaussianLogGammaEulerHead.nameF GaussianLogGammaEulerHead.nameF) windowF
      (diffData (GaussianLogGammaEulerHead.data A B D neg (N+r)) (GaussianLogGammaEulerHead.data A B D neg N))
      (windowData A B D neg N r) := by
  have hM := le_trans hN (le_add_right N r)
  have moved := difference_proper GaussianLogGammaEulerHead.nameF F GaussianLogGammaEulerHead.nameF F
    (GaussianLogGammaEulerHead.data A B D neg (N+r)) (head A B D neg (N+r))
    (GaussianLogGammaEulerHead.data A B D neg N) (head A B D neg N)
    (GaussianLogGammaEulerHead.regular A B D neg (N+r) h hM)
    (GaussianLogGammaEulerNormalizedHead.regular A B D neg (N+r) h hM)
    (GaussianLogGammaEulerHead.regular A B D neg N h hN)
    (GaussianLogGammaEulerNormalizedHead.regular A B D neg N h hN)
    (GaussianLogGammaEulerNormalizedHead.equivalent A B D neg (N+r) h hM)
    (GaussianLogGammaEulerNormalizedHead.equivalent A B D neg N h hN)
  exact cross_trans _ _ _ _ _ _ moved (equivalent A B D neg N r h hN)

theorem actual_finite_Euler_logarithm_normalized_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        crossEquivalent (diffF F F) windowF
          (diffData (head (var 0) (var 1) (var 2) (var 3) (var 4+var 5)) (head (var 0) (var 1) (var 2) (var 3) (var 4)))
          (windowData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (equivalent _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_finite_Euler_logarithm_original_difference_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        crossEquivalent (diffF GaussianLogGammaEulerHead.nameF GaussianLogGammaEulerHead.nameF) windowF
          (diffData (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 4+var 5))
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 4)))
          (windowData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (original_equivalent _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNormalizedDifference

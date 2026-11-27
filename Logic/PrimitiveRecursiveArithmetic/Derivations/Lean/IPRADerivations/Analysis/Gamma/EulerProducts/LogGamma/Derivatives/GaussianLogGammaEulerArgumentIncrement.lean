import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.FiniteHeads.GaussianLogGammaEulerNormalizedHead
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyAdd
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupDifferenceTransform
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalRatioBinding
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain

/-!
# Finite Euler logarithm increments in the argument

At a common positive cutoff, the factorial terms cancel. The remaining
increment is the actual rational displacement times the integer
logarithm, minus the sum of differences of the original shifted
logarithm rows. Both ends are compared at independent observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerArgumentIncrement

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (point_data_congr)
open GaussianLogGammaEulerHead (argument productF productData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifference (name_regular)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedFiniteProductFamily (regularRows regular_at subst_regularRows)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyAdd (mixedBody)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qadd represents)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRightHalfPlaneLogarithm (source)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "H" => GaussianLogGammaEulerHead.nameF
local notation "headData" => GaussianLogGammaEulerHead.data
local notation "denominatorF" => GaussianLogGammaEulerHead.sumF
local notation "denominatorData" => GaussianLogGammaEulerHead.sumData
local notation "baseRow" => GaussianLogGammaEulerHead.rowBody
local notation "baseData" => GaussianLogGammaEulerHead.rowData
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "S" => GaussianNamedFiniteSumFamily.nameF
local notation "sd" => GaussianNamedFiniteSumFamily.data

def step (A B neg a b sign D : PTm n) : PTm n :=
  qsub (argument a b D sign) (argument A B D neg)

ipra_subst step [argument, ZT.subst, ZT.ofNat]

theorem step_represents (A B neg a b sign D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] represents (step A B neg a b sign D) (GaussianRootAlgebra.sub (native a b sign) (native A B neg)) D :=
  qsub_represents _ _ _ _ D hD (ofGaussian_represents (native a b sign) D hD)
    (ofGaussian_represents (native A B neg) D hD)

theorem step_ofGaussian (A B neg a b sign D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] step A B neg a b sign D ≐ ofGaussian (GaussianRootAlgebra.sub (native a b sign) (native A B neg)) D :=
  canonical_unique _ _ _ D (qsub_canonical _ _) (ofGaussian_canonical _ _ hD) hD
    (step_represents A B neg a b sign D hD) (ofGaussian_represents _ _ hD)

def rowData (A B neg a b sign D : PTm n) : PTm n :=
  pairT (baseData a b D sign) (baseData A B D neg)

ipra_subst rowData

private def projectedBody (p : PTm 1) : PTm 2 := inst2 baseRow (var 0) (inst1 p (var 1))
private abbrev laterBody := projectedBody (fstT (var 0))
private abbrev earlierBody := projectedBody (sndT (var 0))

def rowBody : PTm 2 := diffData laterBody earlierBody
def rowF : PR 2 := diffF G G
def sumF : PR 2 := S rowF rowBody
def sumData (A B neg a b sign D N : PTm n) : PTm n := sd (succ N) (rowData A B neg a b sign D)
def weightedData (A B neg a b sign D N : PTm n) : PTm n :=
  multiplyData constantF logF (step A B neg a b sign D) (L N one)
def windowF : PR 2 := diffF productF sumF
def windowData (A B neg a b sign D N : PTm n) : PTm n :=
  diffData (weightedData A B neg a b sign D N) (sumData A B neg a b sign D N)

ipra_subst sumData

ipra_subst weightedData [one]

ipra_subst windowData

private theorem first_projection (x y : PTm n) : Γ ⊢[PRAAx] inst1 (fstT (var 0)) (pairT x y) ≐ x := by
  simpa [inst1] using fst_pair (Γ := Γ) x y

private theorem second_projection (x y : PTm n) : Γ ⊢[PRAAx] inst1 (sndT (var 0)) (pairT x y) ≐ y := by
  simpa [inst1] using snd_pair (Γ := Γ) x y

private theorem projected_at (p : PTm 1) (i x y : PTm n) (e : Γ ⊢[PRAAx] inst1 p x ≐ y) :
    Γ ⊢[PRAAx] inst2 (projectedBody p) i x ≐ inst2 baseRow i y := by
  change Γ ⊢[PRAAx] Syn.subst ![i,x] (inst2 baseRow (var 0) (inst1 p (var 1))) ≐ _
  simpa only [subst_inst2,subst_inst1,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    congrInst2 baseRow (.eqRefl i) e

@[simp] private theorem rowBody_at (i x : PTm n) :
    inst2 rowBody i x = diffData (inst2 laterBody i x) (inst2 earlierBody i x) := by
  simp [rowBody,inst2]

theorem row_at (i A B neg a b sign D : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (rowData A B neg a b sign D) ≐ diffData (P (a+i*D) b D sign) (P (A+i*D) B D neg) := by
  let x := baseData a b D sign
  let y := baseData A B D neg
  have ea := (projected_at (Γ := Γ) (fstT (var 0)) i (pairT x y) x (first_projection x y)).eqTrans
    (GaussianLogGammaEulerHead.row_at i a b D sign)
  have eA := (projected_at (Γ := Γ) (sndT (var 0)) i (pairT x y) y (second_projection x y)).eqTrans
    (GaussianLogGammaEulerHead.row_at i A B D neg)
  rw [rowBody_at]
  simpa only [GaussianNamedDifference.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,rowData,x,y] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (diffData (var 0) (var 1) : PTm 2)
      (σ := ![inst2 laterBody i (pairT x y),inst2 earlierBody i (pairT x y)])
      (σ' := ![P (a+i*D) b D sign,P (A+i*D) B D neg])
      (fun i => by fin_cases i; exact ea; exact eA)

private theorem projection_rows (p : PTm 1) (N x y : PTm n) (e : Γ ⊢[PRAAx] inst1 p x ≐ y)
    (h : Γ ⊢[PRAAx] regularRows G baseRow N y) :
    Γ ⊢[PRAAx] regularRows G (projectedBody p) N x ⋏ equalRows G G (projectedBody p) baseRow N x y := by
  let sh (v : PTm n) := Syn.shift v
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have er : Δ ⊢[PRAAx] inst1 p (sh x) ≐ sh y := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,Fm.subst_eq,subst_inst1] using e.shift.wk
  have hr : Δ ⊢[PRAAx] regularRows G baseRow (sh N) (sh y) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_regularRows] using h.shift.wk
  have binding := projected_at p i (sh x) (sh y) er
  have reg := regular_at G baseRow (sh N) (sh y) i hr Prf.hyp0
  exact .andI (.allI (.impI (point_data_congr G _ _ binding.eqSymm reg)))
    (.allI (.impI (cross_data_congr G G _ _ _ _ binding.eqSymm (.eqRefl _) (cross_refl G _ reg))))

private theorem difference_rows (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows G laterBody N x) (k : Γ ⊢[PRAAx] regularRows G earlierBody N x) :
    Γ ⊢[PRAAx] regularRows rowF rowBody N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hp : Δ ⊢[PRAAx] regularRows G laterBody (Syn.shift N) (Syn.shift x) := by
    simpa only [Δ,Fm.shift,Syn.shift,subst_regularRows] using h.shift.wk
  have hm : Δ ⊢[PRAAx] regularRows G earlierBody (Syn.shift N) (Syn.shift x) := by
    simpa only [Δ,Fm.shift,Syn.shift,subst_regularRows] using k.shift.wk
  rw [rowBody_at]
  exact name_regular G G _ _ (regular_at G laterBody _ _ _ hp Prf.hyp0)
    (regular_at G earlierBody _ _ _ hm Prf.hyp0)

private theorem recovered_rows (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows G laterBody N x) (k : Γ ⊢[PRAAx] regularRows G earlierBody N x) :
    Γ ⊢[PRAAx] equalRows (addF rowF G) G (mixedBody rowBody earlierBody) laterBody N x x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hp : Δ ⊢[PRAAx] regularRows G laterBody (Syn.shift N) (Syn.shift x) := by
    simpa only [Δ,Fm.shift,Syn.shift,subst_regularRows] using h.shift.wk
  have hm : Δ ⊢[PRAAx] regularRows G earlierBody (Syn.shift N) (Syn.shift x) := by
    simpa only [Δ,Fm.shift,Syn.shift,subst_regularRows] using k.shift.wk
  rw [GaussianNamedFiniteSumFamilyAdd.inst2_mixedBody,rowBody_at]
  exact GaussianGammaRationalRatioBinding.difference_add_recover G G _ _
    (regular_at G laterBody _ _ _ hp Prf.hyp0) (regular_at G earlierBody _ _ _ hm Prf.hyp0)

private theorem projected_later (A B neg a b sign D N : PTm n) (h : Γ ⊢[PRAAx] source a D sign) :
    Γ ⊢[PRAAx] regularRows G laterBody (succ N) (rowData A B neg a b sign D) ⋏
      equalRows G G laterBody baseRow (succ N) (rowData A B neg a b sign D) (baseData a b D sign) :=
  projection_rows (fstT (var 0)) _ _ _ (first_projection _ _) (GaussianLogGammaEulerHead.sum_rows a b D sign N h)

private theorem projected_earlier (A B neg a b sign D N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] regularRows G earlierBody (succ N) (rowData A B neg a b sign D) ⋏
      equalRows G G earlierBody baseRow (succ N) (rowData A B neg a b sign D) (baseData A B D neg) :=
  projection_rows (sndT (var 0)) _ _ _ (second_projection _ _) (GaussianLogGammaEulerHead.sum_rows A B D neg N h)

theorem rows_regular (A B neg a b sign D N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign) :
    Γ ⊢[PRAAx] regularRows rowF rowBody (succ N) (rowData A B neg a b sign D) :=
  difference_rows _ _ (projected_later A B neg a b sign D N k).andE₁ (projected_earlier A B neg a b sign D N h).andE₁

theorem sum_regular (A B neg a b sign D N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign) :
    Γ ⊢[PRAAx] pointCN sumF (sumData A B neg a b sign D N) :=
  GaussianNamedFiniteSumFamily.regular rowF rowBody _ _ (rows_regular A B neg a b sign D N h k)

theorem weighted_regular (A B neg a b sign D N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN productF (weightedData A B neg a b sign D N) :=
  multiply_fast constantF logF _ _ (constant_regular _)
    (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one)))

theorem window_regular (A B neg a b sign D N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN windowF (windowData A B neg a b sign D N) :=
  name_regular _ _ _ _ (weighted_regular A B neg a b sign D N hN) (sum_regular A B neg a b sign D N h k)

theorem denominator_increment (A B neg a b sign D N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign) :
    Γ ⊢[PRAAx] crossEquivalent (diffF denominatorF denominatorF) sumF
      (diffData (denominatorData a b D sign N) (denominatorData A B D neg N))
      (sumData A B neg a b sign D N) := by
  let M := succ N
  let x := rowData A B neg a b sign D
  let s := sumData A B neg a b sign D N
  let v := denominatorData A B D neg N
  let u := denominatorData a b D sign N
  let d := sd M x
  let U := S G earlierBody
  let V := S G laterBody
  let W := S (addF rowF G) (mixedBody rowBody earlierBody)
  have hp := projected_later A B neg a b sign D N k
  have hm := projected_earlier A B neg a b sign D N h
  have hs := rows_regular A B neg a b sign D N h k
  have hr := recovered_rows M x hp.andE₁ hm.andE₁
  have left := GaussianNamedFiniteSumFamilyCongruence.family_sum_cross G G laterBody baseRow M x _ hp.andE₂
  have right := GaussianNamedFiniteSumFamilyCongruence.family_sum_cross G G earlierBody baseRow M x _ hm.andE₂
  have foldRows := GaussianNamedFiniteSumFamilyCongruence.family_sum_cross (addF rowF G) G
    (mixedBody rowBody earlierBody) laterBody M x x hr
  have split := GaussianNamedFiniteSumFamilyAdd.family_add_cross rowF G rowBody earlierBody M x hs hm.andE₁
  have sumOk := sum_regular A B neg a b sign D N h k
  have earlierOk := GaussianNamedFiniteSumFamily.regular G earlierBody M x hm.andE₁
  have hU := GaussianLogGammaEulerHead.sum_regular a b D sign N k
  have hV := GaussianLogGammaEulerHead.sum_regular A B D neg N h
  have move := GaussianNamedGammaHalfShift.add_cross sumF sumF U denominatorF s s d v
    sumOk sumOk earlierOk hV (cross_refl _ _ sumOk) right
  have folded := cross_trans (addF sumF U) W V (addData s d) d d (cross_symm W (addF sumF U) _ _ split) foldRows
  have cancel := cross_trans denominatorF (addF sumF U) (addF sumF denominatorF) u (addData s d) (addData s v)
    (cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ folded left)) move
  have swapped := difference_proper denominatorF (addF sumF denominatorF) denominatorF denominatorF
    u (addData s v) v v hU (add_fast _ _ _ _ sumOk hV) hV hV cancel (cross_refl _ _ hV)
  exact cross_trans _ _ _ _ _ _ swapped (GaussianNamedStrictOrderDifference.sum_sub_right sumF denominatorF s v sumOk hV)

theorem product_increment (A B neg a b sign D N : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (diffF productF productF) productF
      (diffData (productData a b D sign N) (productData A B D neg N))
      (weightedData A B neg a b sign D N) := by
  let z := argument A B D neg
  let w := argument a b D sign
  let d := step A B neg a b sign D
  let m := L N one
  let u := productData a b D sign N
  let v := productData A B D neg N
  let s := weightedData A B neg a b sign D N
  let E := addF constantF constantF
  let T := multiplyF E logF
  let t := multiplyData E logF (addData d z) m
  have hz := constant_regular (Γ := Γ) z
  have hw := constant_regular (Γ := Γ) w
  have hd := constant_regular (Γ := Γ) d
  have hm := GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))
  have ew : Γ ⊢[PRAAx] qadd d z ≐ w :=
    (GaussianReciprocalHorner.qadd_commutative d z).eqTrans
      (GaussianRationalLinearProduct.add_sub_right z w (ofGaussian_canonical (native a b sign) D hD))
  have eq := cross_data_congr E constantF (addData d z) (addData d z) (qadd d z) w (.eqRefl _) ew
    (GaussianGammaEulerShift.constant_sum_cross d z)
  have fold := multiply_cross E constantF logF logF (addData d z) w m m
    (add_fast _ _ _ _ hd hz) hw hm hm eq (cross_refl _ _ hm)
  have split := GaussianNameRingLaws.right_distributive constantF constantF logF d z m hd hz hm
  have linked := cross_trans productF T (addF productF productF) u t (addData s v)
    (cross_symm T productF _ _ fold) split
  have hu := GaussianLogGammaEulerNormalizedHead.product_regular a b D sign N hN
  have hv := GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN
  have hs := weighted_regular A B neg a b sign D N hN
  have aligned := difference_proper productF (addF productF productF) productF productF
    u (addData s v) v v hu (add_fast _ _ _ _ hs hv) hv hv linked (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ aligned (GaussianNamedStrictOrderDifference.sum_sub_right productF productF s v hs hv)

theorem original_equivalent (A B neg a b sign D N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (diffF H H) windowF
      (diffData (headData a b D sign N) (headData A B D neg N)) (windowData A B neg a b sign D N) := by
  let c := L (fact N) one
  let u := productData a b D sign N
  let v := productData A B D neg N
  let x := denominatorData a b D sign N
  let y := denominatorData A B D neg N
  let E := addF logF productF
  let d := diffData (addData c u) (addData c v)
  let e := diffData x y
  have hc := GaussianPositiveRationalLogarithm.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hu := GaussianLogGammaEulerNormalizedHead.product_regular a b D sign N hN
  have hv := GaussianLogGammaEulerNormalizedHead.product_regular A B D neg N hN
  have hx := GaussianLogGammaEulerHead.sum_regular a b D sign N k
  have hy := GaussianLogGammaEulerHead.sum_regular A B D neg N h
  have plus := add_fast logF productF c u hc hu
  have minus := add_fast logF productF c v hc hv
  have split := GaussianBohrMollerupDifferenceTransform.exchange E denominatorF E denominatorF
    (addData c u) x (addData c v) y plus hx minus hy
  have factors := cross_trans (diffF E E) (diffF productF productF) productF d (diffData u v)
    (weightedData A B neg a b sign D N)
    (GaussianBohrMollerupDifference.cancel_common logF productF productF c u v hc hu hv)
    (product_increment A B neg a b sign D N h.andE₂ hN)
  have reduced := difference_proper (diffF E E) productF (diffF denominatorF denominatorF) sumF
    d (weightedData A B neg a b sign D N) e (sumData A B neg a b sign D N)
    (name_regular _ _ _ _ plus minus) (weighted_regular A B neg a b sign D N hN)
    (name_regular _ _ _ _ hx hy) (sum_regular A B neg a b sign D N h k) factors
    (denominator_increment A B neg a b sign D N h k)
  exact cross_trans (diffF H H) _ windowF _ _ _ split reduced

theorem actual_finite_Euler_logarithm_argument_increment_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 0) (var 6) (var 2) ⋏ source (var 3) (var 6) (var 5)) ⟶ le one (var 7) ⟶
        crossEquivalent (diffF H H) windowF
          (diffData (headData (var 3) (var 4) (var 6) (var 5) (var 7))
            (headData (var 0) (var 1) (var 6) (var 2) (var 7)))
          (windowData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (.impI (original_equivalent _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerArgumentIncrement

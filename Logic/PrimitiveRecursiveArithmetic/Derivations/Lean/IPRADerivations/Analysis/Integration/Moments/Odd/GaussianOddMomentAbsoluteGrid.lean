import IPRADerivations.Analysis.Integration.Moments.Odd.GaussianOddMomentSignedGrid
import IPRADerivations.Analysis.Integration.Moments.Odd.GaussianOddMomentAbsoluteMetric
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartOrder

/-!
# Literal absolute odd Gaussian quadratures on finite grids

The actual absolute clients take the real absolute value of the
signed row observations. A checked nonnegative decay representative
bounds the change from the original positive row. Reflection gives
identical absolute values on the reflected panel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddMomentAbsoluteGrid

open_ipra
open GaussianOddMomentIntegrand (degree clock)
open GaussianOddMomentSignedGrid (evaluatorF literal_positive_at)
open GaussianOddSymmetricQuadrature (fixedData)
open GaussianOddMomentAbsoluteMetric (absolute absolute_congr absolute_distance absolute_of_positive absolute_negative)
open GaussianRationalHorner (positive_product qmul_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCompactRiemannName (inside grid sampleBody sampleData quadrature sample_body_at)
open GaussianEulerIntegerMomentIntegrand (monomial)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_at)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData)
open GaussianEulerDecayOrder (signedTime)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRealArithmetic (positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def absTerm (side : Bool) (p t x : PTm n) : PTm n := absolute (ap3 (evaluatorF side) p t x)
def absF (side : Bool) : PR 3 := PTm.toPR (absTerm side (var 0) (var 1) (var 2))
ipra_subst absTerm

theorem abs_at (side : Bool) (p t x : PTm n) : Γ ⊢[PRAAx]
    ap3 (absF side) p t x ≐ absTerm side p t x := by
  simpa only [absF,ap3,subst_absTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    using toPR_eq (Γ := Γ) (absTerm side (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem abs_reflected (p t x : PTm n) : Γ ⊢[PRAAx] ap3 (absF true) p t x ≐ ap3 (absF false) p t x :=
  (abs_at true p t x).eqTrans ((absolute_congr (GaussianOddMomentSignedGrid.reflected_row p t x)).eqTrans
    ((absolute_negative _).eqTrans (abs_at false p t x).eqSymm))

theorem absolute_grid_reflected (p M a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature (absF true) p M a C E x ≐ quadrature (absF false) p M a C E x := by
  have cells : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (sampleBody (absF true))
      (sampleBody (absF false)) M (sampleData p M a C E x) (sampleData p M a C E x) := by
    refine .allI (.impI ?_)
    let i : PTm (n+1) := var 0
    let p' := Syn.shift p
    let M' := Syn.shift M
    let a' := Syn.shift a
    let C' := Syn.shift C
    let E' := Syn.shift E
    let x' := Syn.shift x
    have step : lt i M' :: Γ.map Fm.shift ⊢[PRAAx] inst2 (sampleBody (absF true)) i (sampleData p' M' a' C' E' x') ≐
        inst2 (sampleBody (absF false)) i (sampleData p' M' a' C' E' x') :=
      (sample_body_at _ i p' M' a' C' E' x').eqTrans ((abs_reflected p' (grid i M' a' C' E') x').eqTrans
        (sample_body_at _ i p' M' a' C' E' x').eqSymm)
    simpa only [GaussianRationalFiniteSum.termsEqual,GaussianCompactRiemannName.subst_sampleData,Syn.shift,
      i,p',M',a',C',E',x'] using step
  exact qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ cells)

def numerator (a c : PTm n) : PTm n := c*(a*a)
def denominator (b d : PTm n) : PTm n := d*(b*b)
abbrev representativeF : PR 2 := multiplyF constantF positiveF
def representativeData (N a b c d : PTm n) : PTm n := multiplyData constantF positiveF (monomial (degree N) a b)
  (positiveData (signedTime (numerator a c) (denominator b d)))

theorem monomial_positive (N a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] positive (monomial (degree N) a b) :=
  GaussianPositiveRealArithmetic.positive_power _ _ (GaussianEulerPositivePowerChartOrder.fraction_positive a b hb)

theorem row_positive_reference (N a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] crossEquivalent GaussianOddMomentIntegrand.nameF representativeF
      (GaussianOddMomentIntegrand.data N a b c d) (representativeData N a b c d) := by
  let A := numerator a c
  let B := denominator b d
  let m := monomial (degree N) a b
  let X := decayData A B
  let Y := positiveData (signedTime A B)
  have dB : Γ ⊢[PRAAx] le one B := positive_product _ _ hd (positive_product _ _ hb hb)
  have left : Γ ⊢[PRAAx] pointCN decayF X := GaussianEulerPositiveScalingIntegrand.decay_regular A B
  have right : Γ ⊢[PRAAx] pointCN positiveF Y := GaussianRealExponentialPositiveRepresentative.positive_regular _
  have w : Γ ⊢[PRAAx] pointCN constantF m := constant_regular _
  have e := GaussianEulerDecayOrder.original_decay_nonnegative_representative A B dB
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF decayF positiveF m m X Y w w left right
    (cross_refl _ _ w) (cross_symm _ _ _ _ e)

theorem representative_sample (p N a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    positive (ap2 representativeF p (representativeData N a b c d)) := by
  let m := monomial (degree N) a b
  let x := signedTime (numerator a c) (denominator b d)
  let y := positiveData x
  let k := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF positiveF m y) p
  have atP := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF positiveF m y p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qmul_congr (GaussianGammaCanonicalExponent.constant_at k m) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  have hp := GaussianPositiveRealArithmetic.positive_multiply _ _ (monomial_positive N a b hb)
    (GaussianRealExponentialPositiveRepresentative.sample_nonnegative x k)
  exact GaussianPositiveRealArithmetic.positive_congr atP.eqSymm hp

theorem literal_positive_axis (p t N c d : PTm n) (hb : Γ ⊢[PRAAx] le one (sndT t))
    (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (ap3 (evaluatorF false) p t (fixedData N c d)) := by
  have dB := positive_product (Γ := Γ) d (sndT t*sndT t) hd (positive_product _ _ hb hb)
  have decay := GaussianEulerDecayRealSamples.original_observation_axis (clock p N (fstT t) (sndT t) c d)
    (numerator (fstT t) c) (denominator (sndT t) d) dB
  exact RationalGaussianEmbedding.axis_congr (literal_positive_at p t N c d).eqSymm
    (RationalGaussianEmbedding.axis_multiply _ _ (monomial_positive N (fstT t) (sndT t) hb).andE₁
      (by simpa only [GaussianEulerDecayRealSamples.observation,numerator,denominator] using decay))

theorem row_absolute_distance (p t N c d : PTm n) (hb : Γ ⊢[PRAAx] le one (sndT t))
    (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap3 (evaluatorF false) p t (fixedData N c d)) (ap3 (absF false) p t (fixedData N c d)) (num 4) (unit p) := by
  let a := fstT t
  let b := sndT t
  let V := unit p
  let x := fixedData N c d
  let D := representativeData N a b c d
  let R := ap2 representativeF p D
  let A := ap3 (evaluatorF false) p t x
  have hV : Γ ⊢[PRAAx] le one V := unit_positive p
  have atP := (literal_positive_at (Γ := Γ) p t N c d).eqTrans (GaussianOddMomentIntegrand.sample_at p N a b c d).eqSymm
  have old := cross_at _ _ _ _ p p (row_positive_reference N a b c d hb hd)
  have near : Γ ⊢[PRAAx] distanceBounded A R two V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hV hV) hV
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))
      (distance_congr atP.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) old)
  have rc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical R := GaussianNameArithmetic.multiply_canonical _ _ _ _ _
  have fixes := absolute_of_positive R rc (representative_sample p N a b c d hb)
  have absNear := distance_congr (.eqRefl _) fixes (.eqRefl _) (.eqRefl _) (absolute_distance _ _ _ _ hV near)
  exact distance_congr (.eqRefl _) (abs_at false p t x).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ R _ two two V hV near (distance_symmetric _ _ _ _ hV absNear))

theorem absolute_grid_distance (p M a C E N c d : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (quadrature (evaluatorF false) p M a C E (fixedData N c d))
      (quadrature (absF false) p M a C E (fixedData N c d)) (num 4*C) (E*unit p) := by
  let X := fixedData N c d
  let f := sampleBody (evaluatorF false)
  let g := sampleBody (absF false)
  let Y := sampleData p M a C E X
  have cells : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.termsDistance f g M Y Y (num 4) (unit p) := by
    refine .allI (.impI ?_)
    let i : PTm (n+1) := var 0
    let p' := Syn.shift p
    let M' := Syn.shift M
    let a' := Syn.shift a
    let C' := Syn.shift C
    let E' := Syn.shift E
    let N' := Syn.shift N
    let c' := Syn.shift c
    let d' := Syn.shift d
    let X' := fixedData N' c' d'
    let t := grid i M' a' C' E'
    let Δ := lt i M' :: Γ.map Fm.shift
    have ha' : Γ.map Fm.shift ⊢[PRAAx] le one a' := by simpa [a',Fm.shift,Syn.shift] using ha.shift
    have hE' : Γ.map Fm.shift ⊢[PRAAx] le one E' := by simpa [E',Fm.shift,Syn.shift] using hE.shift
    have hM' : Γ.map Fm.shift ⊢[PRAAx] le one M' := by simpa [M',Fm.shift,Syn.shift] using hM.shift
    have hd' : Γ.map Fm.shift ⊢[PRAAx] le one d' := by simpa [d',Fm.shift,Syn.shift] using hd.shift
    have ht : Δ ⊢[PRAAx] inside a' C' E' t :=
      GaussianCompactRiemannName.grid_inside i M' a' C' E' ha'.wk hE'.wk hM'.wk (le_of_lt Prf.hyp0)
    have e := distance_congr (sample_body_at (Γ := Δ) _ i p' M' a' C' E' X').eqSymm
      (sample_body_at (Γ := Δ) _ i p' M' a' C' E' X').eqSymm (.eqRefl _) (.eqRefl _)
      (row_absolute_distance p' t N' c' d' ht.andE₂.andE₁ hd'.wk)
    simpa only [GaussianRationalRiemannRefinement.termsDistance,GaussianCompactRiemannName.subst_sampleData,
      GaussianOddSymmetricQuadrature.subst_fixedData,GaussianCoefficientNameBounds.subst_unit,PTm.subst_num,
      f,g,X,Y,Δ,i,p',M',a',C',E',N',c',d',X',Syn.shift] using e
  have hEM : Γ ⊢[PRAAx] le one (E*M) := positive_product _ _ hE hM
  have hP : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hEM hP
    (GaussianRationalRiemannRefinement.weight_bound C E M hE hM)
    (GaussianRationalRiemannRefinement.sum_distance f g M Y Y (num 4) (unit p) hP cells)
  have b := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference (GaussianRationalRiemannRefinement.weight C E M) _ _).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hEM hP) (positive_product _ _ hE hP)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) b

theorem actual_odd_Gaussian_absolute_grid_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (quadrature (absF true) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      quadrature (absF false) (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (absolute_grid_reflected _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianOddMomentAbsoluteGrid

import IPRADerivations.Analysis.GaussianBinetExponentialRectangleResolvent
import IPRADerivations.Analysis.GaussianBinetWeightedResolvent

/-!
# Cofinal comparison of the actual rectangle and weighted resolvent

The error estimates are summed along the original column program.
The unit-grid width cancels its panel count, leaving a rate uniform
in the unit mesh. The checked weighted resolvent identifies the
limit with the canonical Stirling unit difference.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleEvaluation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetExponentialRectangle (data matrix outerBody swap_weighted_grid)
open GaussianBinetExponentialRectangleResolvent (numerator column_resolvent)
open GaussianBinetExponentialRectangleShift (realNumerator)
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianBinetWeightedResolventGrid (gridData rowBody subst_gridData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction subst_fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (column columnFirst columnSumBody column_sum_at)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative subst_qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_one im_one)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def rectangle (p X Y D sign R T N M : PTm n) : PTm n :=
  qmul (fraction T N) (sum outerBody N (data p (qnegative (argument X Y D sign)) (R*T) T N M))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p R K T L : PTm n) :
    Syn.subst σ (numerator p R K T L) = numerator (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ K)
      (Syn.subst σ T) (Syn.subst σ L) := by
  simp [numerator,GaussianBinetExponentialIntegral.uniformCost,one,two]

theorem finite_error (p X Y D sign R K L N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hM : Γ ⊢[PRAAx] le one M) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+one)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (rectangle (p+N) X Y D sign R (D*L) N M)
      (GaussianBinetWeightedResolventGrid.value X Y D sign M)
      (numerator p R K (D*L) L) (unit p*unit L) := by
  let T := D*L
  let z := qnegative (argument X Y D sign)
  let d := data (p+N) z (R*T) T N M
  let c := fraction T N
  let w := fraction one M
  let f := columnSumBody matrix
  let x := pairT N d
  let g := rowBody
  let y := gridData X Y D sign M
  let B := numerator p R K T L
  let U := unit p*unit L
  have hU : Γ ⊢[PRAAx] le one U := positive_product _ _ (unit_positive p) (unit_positive L)
  have rows : Γ ⊢[PRAAx] termsDistance (multiplyBody f) g M (pairT c x) y B U := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hm.shift.wk
    have hm' : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have ls : Δ ⊢[PRAAx] le (s L) (s p) := by simpa [Δ,s,Fm.shift,Syn.shift] using hL.shift.wk
    have ns : Δ ⊢[PRAAx] le ((s R+one)*(s D*s L)) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ps : Δ ⊢[PRAAx] le (unit (s p)) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpN.shift.wk
    let Ts := s D*s L
    let cs := fraction Ts (s N)
    let zs := qnegative (argument (s X) (s Y) (s D) (s sign))
    let ds := data (s p+s N) zs (s R*Ts) Ts (s N) (s M)
    let xs := pairT (s N) ds
    let ys := gridData (s X) (s Y) (s D) (s sign) (s M)
    have left := (multiply_body_at (Γ := Δ) f cs (var 0) xs).eqTrans
      (qmul_congr (.eqRefl cs) (column_sum_at matrix (var 0) (s N) ds))
    have right := GaussianBinetWeightedResolventGrid.row_at (Γ := Δ) (s X) (s Y) (s D) (s sign) (s M) (var 0)
    have est := column_resolvent (Γ := Δ) (var 0) (s p) (s X) (s Y) (s D) (s sign) (s R) (s K) (s L)
      (s N) (s M) hs ms hm' (le_of_lt Prf.hyp0) ls ns ps
    have read : Δ ⊢[PRAAx] distanceBounded (inst2 (multiplyBody f) (var 0) (pairT cs xs))
        (inst2 g (var 0) ys) (numerator (s p) (s R) (s K) Ts (s L)) (unit (s p)*unit (s L)) :=
      distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) est
    simpa only [termsDistance,Syn.shift,s,Δ,c,x,y,d,z,T,B,U,cs,xs,ys,ds,zs,Ts,
      subst_fraction,GaussianBinetExponentialRectangle.subst_data,subst_gridData,subst_pairT,subst_qnegative,
      GaussianLogGammaEulerRepresentation.subst_argument,subst_numerator,GaussianCoefficientNameBounds.subst_unit,
      PTm.subst_add,PTm.subst_mul] using read
  have summed : Γ ⊢[PRAAx] distanceBounded (qmul c (columnFirst matrix N M d)) (sum g M y) (M*B) U :=
    distance_congr (sum_multiply f c M x) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (sum_distance (multiplyBody f) g M (pairT c x) y B U hU rows)
  have hw : Γ ⊢[PRAAx] bounded w one M :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one M hM).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded one M hM)
  have weighted : Γ ⊢[PRAAx] distanceBounded (qmul w (qmul c (columnFirst matrix N M d)))
      (qmul w (sum g M y)) (one*(M*B)) (M*U) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w _ _).eqSymm
      (.eqRefl _) (.eqRefl _) (bounded_product _ _ one M (M*B) U hM hU hw summed)
  have again : Γ ⊢[PRAAx] rectangle (p+N) X Y D sign R T N M ≐ qmul w (qmul c (columnFirst matrix N M d)) :=
    (swap_weighted_grid (p+N) z (R*T) T N M).eqTrans
      ((qmul_associative _ _ _).eqSymm.eqTrans
        ((qmul_congr (qmul_commutative c w) (.eqRefl _)).eqTrans (qmul_associative _ _ _)))
  have ew : Γ ⊢[PRAAx] w ≐ GaussianRationalNormalizedTelescope.weight M := by
    apply GaussianGammaFiniteValueProperness.fraction_equal _ _ M hM
    apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  have result : Γ ⊢[PRAAx] qmul w (sum g M y) ≐ GaussianBinetWeightedResolventGrid.value X Y D sign M :=
    qmul_congr ew (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hM hU) hU
    (le_of_eq_add (d := zero) (by dsimp only [B,U,T]; ipra_ring))
    (distance_congr again.eqSymm result (.eqRefl _) (.eqRefl _) weighted)

def observationCost (R K T : PTm n) : PTm n := num 20*T+two*K*GaussianBinetExponentialIntegral.uniformCost (R+one) T
def tailCost (K : PTm n) : PTm n := two*K*num 20

theorem cofinal_error (p r X Y D sign R K L N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hM : Γ ⊢[PRAAx] le one M) (hL : Γ ⊢[PRAAx] le L r)
    (hN : Γ ⊢[PRAAx] le ((R+one)*(D*L)) N) (hrN : Γ ⊢[PRAAx] le (unit r) N)
    (ht : Γ ⊢[PRAAx] le (tailCost K*unit p) (unit L))
    (ho : Γ ⊢[PRAAx] le (observationCost R K (D*L)*unit p) (unit r)) :
    Γ ⊢[PRAAx] distanceBounded (rectangle (r+N) X Y D sign R (D*L) N M)
      (GaussianBinetWeightedResolventGrid.value X Y D sign M) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have h := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive L)
  apply distance_radius_mono _ _ _ _ _ _ h hp _ (finite_error r X Y D sign R K L N M hz hm hM hL hN hrN)
  dsimp only [observationCost,tailCost] at ht ho
  dsimp only [numerator]
  ipra_le 𝔞(unit r)*sl ht+𝔞(unit L)*sl ho

theorem original_resolvent_rate (p r X Y D sign R K L N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hM : Γ ⊢[PRAAx] le (unit p) M)
    (hmesh : Γ ⊢[PRAAx] le (GaussianBinetLogCellGrid.requiredMesh X Y D zero) M)
    (hL : Γ ⊢[PRAAx] le L r)
    (hN : Γ ⊢[PRAAx] le ((R+one)*(D*L)) N) (hrN : Γ ⊢[PRAAx] le (unit r) N)
    (ht : Γ ⊢[PRAAx] le (tailCost K*unit p) (unit L))
    (ho : Γ ⊢[PRAAx] le (observationCost R K (D*L)*unit p) (unit r)) :
    Γ ⊢[PRAAx] distanceBounded (rectangle (r+N) X Y D sign R (D*L) N M)
      (ap2 GaussianBinetStirlingUnitDifference.nameF p (GaussianBinetStirlingUnitDifference.data X Y D sign))
      (two+GaussianBinetWeightedResolvent.budget X Y D sign) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (cofinal_error p r X Y D sign R K L N M hz hm (le_trans (unit_positive p) hM) hL hN hrN ht ho)
    (GaussianBinetWeightedResolvent.finite_error p X Y D sign M hz.andE₁ hmesh hM)

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleEvaluation

import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangle
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialRectangleShift

/-!
# Quantitative evaluation of the other Binet rectangle order

Each fixed unit column is the same weighted complex Laplace
quadrature at the shifted parameter z+j/M, with an observation
error proportional to the horizon and independent of the mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleColumn

open_ipra
open GaussianBinetExponentialRectangle (data matrix entry_at)
open GaussianBinetExponentialRectangleShift (realNumerator shifted_source original_product)
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (column columnBody column_entry)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bounded_product bound_congr bounded_negative)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "FX" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "LV" => GaussianBinetExponentialIntegralGrid.value
local notation "LP" => GaussianBinetLaplaceExponential.nameF
local notation "LD" => GaussianBinetLaplaceExponential.data

theorem weight_bound (j M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] bounded (tagWeight j M) two one := by
  have hU : Γ ⊢[PRAAx] bounded (fraction j M) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ hM (le_congr (.eqRefl _) (one_mul _).eqSymm hj)
  have hH : Γ ⊢[PRAAx] bounded (fraction one two) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (le_succ_self one)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (le_succ_self one))
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one)
      hH (bounded_negative _ _ _ (le_refl one) hU))

theorem weighted_entry (i j p X Y D sign R T N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] distanceBounded
      (inst3 matrix i j (data p (qnegative (argument X Y D sign)) (R*T) T N M))
      (qmul (tagWeight j M)
        (ap2 LP p (LD (realNumerator X D M j) (M*Y) (M*D) sign (R+one) T (T*i) N)))
      (num 20) (unit p) := by
  let q := qnegative (argument X Y D sign)
  let za := ap2 LP p (LD X Y D sign R T (T*i) N)
  let de := GaussianEulerDecayMesh.observation ((T*i)*j) (N*M) p
  let w := tagWeight j M
  let v := ap2 LP p (LD (realNumerator X D M j) (M*Y) (M*D) sign (R+one) T (T*i) N)
  have hT : Γ ⊢[PRAAx] le (T*i) (T*N) :=
    le_congr (mul_comm i T) (mul_comm N T) (mul_le_mul_right T hi)
  have hp := unit_positive (Γ := Γ) p
  have base : Γ ⊢[PRAAx] distanceBounded v (qmul za de) (num 10) (unit p) :=
    original_product p X Y D sign R T (T*i) N M j hz hN hT hM hj
  have eq : Γ ⊢[PRAAx] inst3 matrix i j (data p q (R*T) T N M) ≐ qmul w (qmul za de) :=
    (entry_at i j p q (R*T) T N M).eqTrans
      (GaussianRationalPowerAlgebra.commute_nested za w de)
  exact distance_congr eq.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance w _ _ two (num 10) (unit p) hp
      (weight_bound j M hM hj) (distance_symmetric _ _ _ _ hp base))

theorem column_error (j p X Y D sign R T N M : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (fraction T N) (column matrix j N (data p (qnegative (argument X Y D sign)) (R*T) T N M)))
      (qmul (tagWeight j M) (LV p (qnegative (argument (realNumerator X D M j) (M*Y) (M*D) sign)) ((R+one)*T) T N))
      (num 20*T) (unit p) := by
  let z := qnegative (argument X Y D sign)
  let A := realNumerator X D M j
  let Y' := M*Y
  let D' := M*D
  let q := qnegative (argument A Y' D' sign)
  let S := (R+one)*T
  let d := data p z (R*T) T N M
  let x := sampleData p N one T one (pairT q S)
  let f := sampleBody FX
  let w := tagWeight j M
  let V := unit p
  have hv := unit_positive (Γ := Γ) p
  have rows : Γ ⊢[PRAAx] termsDistance (columnBody matrix) (multiplyBody f) N (pairT j d) (pairT w x) (num 20) V := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by
      simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have hn : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have hm : Δ ⊢[PRAAx] le one (s M) := (Order.shift_one_le hM).wk
    have hj' : Δ ⊢[PRAAx] le (s j) (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hj.shift.wk
    let zs := qnegative (argument (s X) (s Y) (s D) (s sign))
    let As := realNumerator (s X) (s D) (s M) (s j)
    let qs := qnegative (argument As (s M*s Y) (s M*s D) (s sign))
    let Ss := (s R+one)*s T
    let ds := data (s p) zs (s R*s T) (s T) (s N) (s M)
    let ws := tagWeight (s j) (s M)
    let xs := sampleData (s p) (s N) one (s T) one (pairT qs Ss)
    have l := column_entry (Γ := Δ) matrix (var 0) (s j) ds
    have r := (multiply_body_at (Γ := Δ) f ws (var 0) xs).eqTrans
      (qmul_congr (.eqRefl ws) (GaussianBinetExponentialIntegralGrid.cell_at (var 0) (s p) qs Ss (s T) (s N)))
    have est := weighted_entry (Γ := Δ) (var 0) (s j) (s p) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s M)
      hs hn (le_of_lt (Γ := Δ) Prf.hyp0) hm hj'
    have read : Δ ⊢[PRAAx] distanceBounded (inst2 (columnBody matrix) (var 0) (pairT (s j) ds))
        (inst2 (multiplyBody f) (var 0) (pairT ws xs)) (num 20) (unit (s p)) :=
      distance_congr l.eqSymm r.eqSymm (.eqRefl _) (.eqRefl _) est
    simpa only [termsDistance,Syn.shift,s,Δ,d,z,A,Y',D',q,S,w,x,f,V,
      ds,zs,xs,qs,As,Ss,ws,GaussianBinetExponentialRectangle.subst_data,
      GaussianCompactRiemannName.subst_sampleData,subst_pairT,GaussianBinetExponentialRectangleShift.realNumerator,
      GaussianBinetWeightedExponentialAlgebra.subst_tagWeight,GaussianLogGammaEulerRepresentation.subst_argument,
      GaussianRationalMetric.subst_qnegative,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_add,PTm.subst_num,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using read
  have comp : Γ ⊢[PRAAx] distanceBounded (column matrix j N d) (qmul w (sum f N x)) (N*num 20) V :=
    distance_congr (.eqRefl _) (sum_multiply f w N x) (.eqRefl _) (.eqRefl _)
      (sum_distance (columnBody matrix) (multiplyBody f) N (pairT j d) (pairT w x) (num 20) V hv rows)
  let c := fraction T N
  have hc : Γ ⊢[PRAAx] bounded c T N :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point T N hN).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded T N hN)
  have scale : Γ ⊢[PRAAx] distanceBounded (qmul c (column matrix j N d)) (qmul c (qmul w (sum f N x)))
      (T*(N*num 20)) (N*V) :=
    GaussianRationalRoundedPower.distance_mul_left hN hv hc comp
  have ew : Γ ⊢[PRAAx] c ≐ GaussianRationalRiemannRefinement.weight T one N :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul _).eqSymm
  have target : Γ ⊢[PRAAx] qmul c (qmul w (sum f N x)) ≐ qmul w (LV p q S T N) :=
    (GaussianRationalPowerAlgebra.commute_nested c w (sum f N x)).eqTrans
      (qmul_congr (.eqRefl _) (qmul_congr ew (.eqRefl _)))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN hv) hv
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) target (.eqRefl _) (.eqRefl _) scale)

end LeanProofs.IPRA.Analysis.GaussianBinetExponentialRectangleColumn

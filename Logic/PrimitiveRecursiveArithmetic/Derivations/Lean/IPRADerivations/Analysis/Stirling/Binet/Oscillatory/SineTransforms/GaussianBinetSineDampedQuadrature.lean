import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineRealDampedPanels
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineFrozenPiTerm
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Rectangles.GaussianBinetOscillatorySineRows
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# The actual damped sine quadrature evaluates a frozen Binet row

Sum the real-decay sine panels on their original common mesh. The
other side is exactly the divided half difference of two finite
Laplace quadratures. At a frozen π clock the result is the original
Binet kernel row, with explicit mesh and horizon errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineDampedQuadrature

open_ipra
open GaussianBinetArctangentResolvent (pole)
open GaussianBinetCosinePrimitive (endpoint)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianBinetSineDampedPanels (multiplier shiftedPanel)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4 field5 sampleBody sampleData)
open GaussianEulerDecayMesh (observation)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum sum_multiply)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance leftSum weight weight_bound)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F
local notation "G" => GaussianBinetSineRealDampedPanels.value

def panelData (s : Bool) (p X D A B R U T N : PTm n) : PTm n :=
  sampleData p N one T one (pairT (qnegative (pole s X zero D zero A B)) ((R+U)*T))
def shiftedData (p X D A B R U T N : PTm n) : PTm n :=
  pairT (multiplier A B) (pairT (panelData true p X D A B R U T N) (panelData false p X D A B R U T N))
def shiftedBody : PTm 2 := multiplyBody (differenceBody f f)
def shiftedValue (p X D A B R U T N : PTm n) : PTm n := leftSum shiftedBody N (shiftedData p X D A B R U T N) T one

def evaluated (j p X D A B U T N : PTm n) : PTm n := G p X D A B (T*j) N U T
def body : PTm 2 :=
  let d : PTm 2 := var 1
  evaluated (var 0) (field0 d) (field1 d) (field2 d) (fstT (sndT (field5 d)))
    (sndT (sndT (field5 d))) (fstT (field5 d)) (field3 d) (field4 d)
def data (p X D A B U T N : PTm n) : PTm n := sampleData p X D T N (pairT U (pairT A B))
def value (p X D A B U T N : PTm n) : PTm n := leftSum body N (data p X D A B U T N) T one

ipra_subst panelData [one]
ipra_subst shiftedData
ipra_subst evaluated [GaussianBinetSineRealDampedPanels.value, quotient, one]
ipra_subst data
ipra_subst value [one]

private theorem shifted_at (j p X D A B R U T N : PTm n) : Γ ⊢[PRAAx]
    inst2 shiftedBody j (shiftedData p X D A B R U T N) ≐ shiftedPanel p X zero D zero A B (T*j) N R U T := by
  let c := multiplier A B
  let a := panelData true p X D A B R U T N
  let b := panelData false p X D A B R U T N
  have read := multiply_body_at (Γ := Γ) (differenceBody f f) c j (pairT a b)
  have d := difference_body_at (Γ := Γ) f f j a b
  exact read.eqTrans (qmul_congr (.eqRefl _) (d.eqTrans (qsub_congr
    (GaussianBinetExponentialIntegralGrid.cell_at j p _ ((R+U)*T) T N)
    (GaussianBinetExponentialIntegralGrid.cell_at j p _ ((R+U)*T) T N))))

private theorem observation_congr {a a' b b' p p' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hp : Γ ⊢[PRAAx] p ≐ p') : Γ ⊢[PRAAx] observation a b p ≐ observation a' b' p' := by
  simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,p]) (σ' := ![a',b',p']) (fun i => by fin_cases i; exact ha; exact hb; exact hp)

private theorem endpoint_congr {p p' a a' b b' R R' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') (hR : Γ ⊢[PRAAx] R ≐ R') : Γ ⊢[PRAAx] endpoint p a b R one ≐ endpoint p' a' b' R' one := by
  simpa only [GaussianBinetOscillatorySineRows.subst_endpoint,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (endpoint (var 0) (var 1) (var 2) (var 3) one : PTm 4)
      (σ := ![p,a,b,R]) (σ' := ![p',a',b',R']) (fun i => by fin_cases i; exact hp; exact ha; exact hb; exact hR)

private theorem evaluated_congr (j : PTm n) {p p' X X' D D' A A' B B' U U' T T' N N' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hX : Γ ⊢[PRAAx] X ≐ X') (hD : Γ ⊢[PRAAx] D ≐ D')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hU : Γ ⊢[PRAAx] U ≐ U') (hT : Γ ⊢[PRAAx] T ≐ T')
    (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx] evaluated j p X D A B U T N ≐ evaluated j p' X' D' A' B' U' T' N' := by
  have a := congrMul hT (.eqRefl j)
  have eq : Γ ⊢[PRAAx] GaussianRationalReciprocal.reciprocal (coefficient A B (polarity true)) ≐
      GaussianRationalReciprocal.reciprocal (coefficient A' B' (polarity true)) := by
    simpa only [GaussianRationalReciprocal.subst_reciprocal,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (GaussianRationalReciprocal.reciprocal (var 0)) (GaussianBinetImaginaryExponentialScale.coefficient_congr true hA hB)
  exact qmul_congr (observation_congr (congrMul hX a) (congrMul hD hN) hp)
    (qmul_congr eq (endpoint_congr hp (congrMul a hA) (congrMul hN hB) (congrMul hU hT)))

theorem row_at (j p X D A B U T N : PTm n) : Γ ⊢[PRAAx]
    inst2 body j (data p X D A B U T N) ≐ evaluated j p X D A B U T N := by
  let d := data p X D A B U T N
  have read : inst2 body j d = evaluated j (field0 d) (field1 d) (field2 d) (fstT (sndT (field5 d)))
      (sndT (sndT (field5 d))) (fstT (field5 d)) (field3 d) (field4 d) := by
    simp only [body,inst2,subst_evaluated,GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,
      GaussianCompactRiemannName.subst_field2,GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,
      GaussianCompactRiemannName.subst_field5,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [read]
  have last : Γ ⊢[PRAAx] field5 d ≐ pairT U (pairT A B) := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have tail := (congrSnd last).eqTrans (snd_pair _ _)
  exact evaluated_congr j (GaussianCompactRiemannName.field0_at _ _ _ _ _ _) (GaussianCompactRiemannName.field1_at _ _ _ _ _ _)
    (GaussianCompactRiemannName.field2_at _ _ _ _ _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd tail).eqTrans (snd_pair _ _)) ((congrFst last).eqTrans (fst_pair _ _))
    (GaussianCompactRiemannName.field3_at _ _ _ _ _ _) (GaussianCompactRiemannName.field4_at _ _ _ _ _ _)

private theorem cell_error (j p X D A B R U T N : PTm n)
    (hz : Γ ⊢[PRAAx] source X zero D zero R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le A (U*B)) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 shiftedBody j (shiftedData p X D A B R U T N)) (inst2 body j (data p X D A B U T N))
      (B*num 28) (unit p) :=
  distance_congr (shifted_at j p X D A B R U T N).eqSymm (row_at j p X D A B U T N).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBinetSineRealDampedPanels.real_panel_error p X D A B (T*j) N R U T hz hA hB hN hU
      (le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)))

theorem quadrature_error (p X D A B R U T N : PTm n)
    (hz : Γ ⊢[PRAAx] source X zero D zero R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le A (U*B)) : Γ ⊢[PRAAx]
    distanceBounded (shiftedValue p X D A B R U T N) (value p X D A B U T N)
      (T*(B*num 28)) (unit p) := by
  let x := shiftedData p X D A B R U T N
  let y := data p X D A B U T N
  let E := B*num 28
  let H := unit p
  let w := weight T one N
  have rows : Γ ⊢[PRAAx] termsDistance shiftedBody body N x y E H := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    have z : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) := by simpa [Δ,s,Syn.shift,Fm.shift] using hz.shift
    have a : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Syn.shift,Fm.shift] using hA.shift
    have b : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Syn.shift,Fm.shift] using hB.shift
    have n' : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Syn.shift,Fm.shift] using hN.shift
    have u : Δ ⊢[PRAAx] le (s A) (s U*s B) := by simpa [Δ,s,Syn.shift,Fm.shift] using hU.shift
    simpa only [x,y,E,H,s,Δ,Syn.shift,subst_shiftedData,subst_data,PTm.subst_mul,LeanProofs.IPRA.PTm.subst_num,
      GaussianCoefficientNameBounds.subst_unit] using
      cell_error (var 0) (s p) (s X) (s D) (s A) (s B) (s R) (s U) (s T) (s N) z.wk a.wk b.wk n'.wk u.wk (le_of_lt Prf.hyp0)
  have hH := unit_positive (Γ := Γ) p
  have hW := positive_product _ _ (le_refl (Γ := Γ) one) hN
  let l := sum shiftedBody N x
  let r := sum body N y
  have dif : Γ ⊢[PRAAx] distanceBounded l r (N*E) H := sum_distance _ _ _ _ _ _ _ hH rows
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul w l) (qmul w r) (T*(N*E)) ((one*N)*H) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w l r).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product w _ T (one*N) (N*E) H hW hH (weight_bound T one N (le_refl one) hN) dif)
  exact distance_radius_mono _ _ (T*(N*E)) ((one*N)*H) (T*E) H (positive_product _ _ hW hH) hH
    (le_of_eq_add (d := zero) (by ipra_ring)) scaled

theorem readback (p X D A B R U L N : PTm n) : Γ ⊢[PRAAx]
    shiftedValue (p+N) X D A B R U (D*L) N ≐ GaussianBinetSineDampedTransform.value p X zero D zero A B R U L N := by
  let T := D*L
  let c := multiplier A B
  let w := weight T one N
  let a := panelData true (p+N) X D A B R U T N
  let b := panelData false (p+N) X D A B R U T N
  let s := sum (differenceBody f f) N (pairT a b)
  exact (qmul_congr (.eqRefl w) (sum_multiply (differenceBody f f) c N (pairT a b))).eqTrans
    ((GaussianRationalPowerAlgebra.commute_nested w c s).eqTrans
       ((qmul_congr (.eqRefl c) (weighted_difference f f N a b T one).eqSymm).eqTrans
        (qmul_associative _ _ _)))

def frozenValue (p k i A B U L N : PTm n) : PTm n :=
  qmul (fraction two one) (value (p+N) (realNumerator k i) (realDenominator k) A B U (realDenominator k*L) N)

theorem frozen_kernel_error (p k i A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source (realNumerator k i) zero (realDenominator k) zero R)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le A (U*B))
    (hm : Γ ⊢[PRAAx] le (realDenominator k) (K*realNumerator k i)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(realDenominator k*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let T := realDenominator k*L
    let H := unit p*unit L
    let Q := unit (p+N)
    Γ ⊢[PRAAx] distanceBounded (frozenValue p k i A B U L N) (GaussianBinetKernelRows.value k i A B)
      (two*(T*(B*num 28))*H+(two*(B*GaussianBinetArctangentCosineLaplace.error p R U K T L))*Q) (Q*H) := by
  let X := realNumerator k i
  let D := realDenominator k
  let T := D*L
  let Q := unit (p+N)
  let H := unit p*unit L
  let m : PTm n := fraction two one
  let e := T*(B*num 28)
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive _
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have hBnd : Γ ⊢[PRAAx] GaussianRationalMetric.bounded m two one :=
    GaussianEulerExponentCompactBounds.fraction_bound two one two (le_refl one) (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
  have first := distance_symmetric _ _ _ _ hQ
    (quadrature_error (p+N) X D A B R U T N hz hA hB (le_trans (unit_positive p) hpN) hU)
  have mread : Γ ⊢[PRAAx] qmul m (shiftedValue (p+N) X D A B R U T N) ≐ GaussianBinetSineFrozenPiTerm.value p k i A B R U L N :=
    qmul_congr (.eqRefl _) (readback p X D A B R U L N)
  have bridge := distance_congr (.eqRefl _) mread (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance m _ _ two e Q hQ hBnd first)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hQ hH bridge
    (GaussianBinetSineFrozenPiTerm.finite_error p k i A B R U K L N hz hA hB hU hm hL hN hpN)

end LeanProofs.IPRA.Analysis.GaussianBinetSineDampedQuadrature

import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedExponentialAlgebra
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStrip
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPrimitiveEvaluationPascal

/-!
# The actual weighted exponential quadrature on the unit panel

The positive grid coordinate is `1+u`. The exact readback subtracts
one, so the leftmost sample is the original decay at zero. The finite
forward telescope has its literal elementary endpoint and a quantified
mesh and observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialGrid

open_ipra
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianBinetWeightedExponentialAlgebra
  (tagWeight primitiveCoefficient leftCoefficient rightCoefficient panelScale integrationScale inverseScale correction cap)
open GaussianCompactRiemannName (sampleBody sampleData quadrature sample_body_at grid)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation observation_numerator_congr observation_rescale)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qzero qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative qnegative_canonical qsub_canonical)
open GaussianRationalParameterTelescope (localRows forward_at)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianRationalSyntheticDivision (qone qmul_congr qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def rowValue (p a b j N : PTm n) : PTm n := qmul (tagWeight j N) (observation (a*j) (b*N) p)
def evaluatorTerm (p t x : PTm n) : PTm n := rowValue p (fstT x) (sndT x) (tagNumerator t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def value (p N a b : PTm n) : PTm n := quadrature evaluatorF p N one one one (pairT a b)

def primitiveValue (p a b j N : PTm n) : PTm n := qmul (primitiveCoefficient a b j N) (observation (a*j) (b*N) p)
def primitiveData (p a b N : PTm n) : PTm n := pairT p (pairT (pairT a b) N)
def primitiveBody : PTm 2 := primitiveValue (fstT (var 1)) (fstT (fstT (sndT (var 1))))
  (sndT (fstT (sndT (var 1)))) (var 0) (sndT (sndT (var 1)))

def endpoint (p a b : PTm n) : PTm n :=
  qmul (inverseScale a b) (qsub (qmul (rightCoefficient a b) (observation a b p)) (leftCoefficient a b))

def meshCost (a b : PTm n) : PTm n := (three*cap a b+num 6)*(a*a)
def observationCost (a b : PTm n) : PTm n := num 20*cap a b
def rowError (p a b N : PTm n) : PTm n := meshCost a b*unit p+observationCost a b*(N*N)
def rowDen (p N : PTm n) : PTm n := (N*N)*unit p

ipra_subst value [one]
ipra_subst rowValue
ipra_subst evaluatorTerm
ipra_subst primitiveValue
ipra_subst primitiveData
ipra_subst endpoint
ipra_subst rowError [meshCost, observationCost, three, two, one]
ipra_subst rowDen

private theorem row_congr (p a b j j' N N' : PTm n)
    (hj : Γ ⊢[PRAAx] j ≐ j') (hN : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] rowValue p a b j N ≐ rowValue p a b j' N' := by
  simpa only [subst_rowValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,a,b,j,N]) (σ' := ![p,a,b,j',N'])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact hj; exact hN)

theorem evaluator_at (p t a b : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (pairT a b) ≐ rowValue p a b (tagNumerator t) (sndT t) := by
  have e : Γ ⊢[PRAAx] ap3 evaluatorF p t (pairT a b) ≐ evaluatorTerm p t (pairT a b) := by
    simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,pairT a b]
  exact e.eqTrans (by
    simpa only [evaluatorTerm,subst_rowValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
        (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![p,fstT (pairT a b),sndT (pairT a b),tagNumerator t,sndT t])
        (σ' := ![p,a,b,tagNumerator t,sndT t])
        (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _; exact .eqRefl _))

theorem cell_at (i p N a b : PTm n) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i (sampleData p N one one one (pairT a b)) ≐ rowValue p a b i N := by
  let t := grid i N one one one
  have hd : Γ ⊢[PRAAx] sndT t ≐ N := (snd_pair _ _).eqTrans (one_mul N)
  have hn : Γ ⊢[PRAAx] fstT t ≐ i+N := (fst_pair _ _).eqTrans (by ipra_ring)
  have ht : Γ ⊢[PRAAx] tagNumerator t ≐ i := (congrMonus hn hd).eqTrans (add_monus i N)
  exact (sample_body_at evaluatorF i p N one one one _).eqTrans
    ((evaluator_at p t a b).eqTrans (row_congr p a b _ _ _ _ ht hd))

private theorem primitive_at (j p a b N : PTm n) :
    Γ ⊢[PRAAx] inst2 primitiveBody j (primitiveData p a b N) ≐ primitiveValue p a b j N := by
  let x := primitiveData p a b N
  have hi : Γ ⊢[PRAAx] sndT x ≐ pairT (pairT a b) N := snd_pair _ _
  have hr := (congrFst hi).eqTrans (fst_pair (pairT a b) N)
  have proof := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (primitiveValue (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT x,fstT (fstT (sndT x)),sndT (fstT (sndT x)),j,sndT (sndT x)]) (σ' := ![p,a,b,j,N])
    (fun i => by
      fin_cases i
      exact fst_pair _ _
      exact (congrFst hr).eqTrans (fst_pair _ _)
      exact (congrSnd hr).eqTrans (snd_pair _ _)
      exact .eqRefl _
      exact (congrSnd hi).eqTrans (snd_pair _ _))
  simpa only [primitiveBody,inst2,subst_primitiveValue,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,x] using proof

theorem zero_observation (b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] observation zero b p ≐ qone := by
  let z := decayPoint zero b
  have hz : Γ ⊢[PRAAx] z ≐ qzero :=
    (GaussianInverseBinomialRows.negative_congr (GaussianCompactZeroWidth.zero_fraction b hb)).eqTrans
      GaussianEulerBetaPrimitiveEvaluationPascal.negative_zero
  exact (GaussianRadiusExponentialName.sample_at constantF (GaussianNameBounds.U constantF z) p z).eqTrans
    ((GaussianNameConjugation.scalar_sum_congr _ ((constant_at _ z).eqTrans hz)).eqTrans
      (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

private theorem decay_bound (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (observation a b p) three one := by
  refine .orE (zero_or_succ a) ?_ ?_
  · exact bound_congr ((observation_numerator_congr a zero b p Prf.hyp0).eqTrans (zero_observation b p hb.wk)).eqSymm
      (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
        (by dsimp only [three]; ipra_le 2) GaussianRationalReciprocal.qone_bounded)
  · have ha : (a ≐ succ (pred a)) :: Γ ⊢[PRAAx] le one a :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    exact GaussianEulerDecayIncrement.decay_observation_uniform_bound a b p ha hb.wk

private theorem adjacent_decay (a b j N p : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) (haN : Γ ⊢[PRAAx] le a N) :
    Γ ⊢[PRAAx] distanceBounded (observation (a*succ j) (b*N) p)
      (qmul (observation (a*j) (b*N) p) (qsub qone (fraction a (b*N))))
      (three*a*a*unit p+num 20*(N*N)) (rowDen p N) := by
  let d := b*N
  let U := unit p
  let x := a*j
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ hb hN
  have hNd : Γ ⊢[PRAAx] le N d := le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N hb)
  have had := le_trans haN hNd
  have raw : Γ ⊢[PRAAx] distanceBounded (observation (a*succ j) d p)
      (qmul (observation x d p) (qsub qone (fraction a d))) (three*a*a*U+num 20*(d*d)) (d*d*U) := by
    refine .orE (zero_or_succ x) ?_ ?_
    · have e : (x ≐ zero) :: Γ ⊢[PRAAx] x ≐ zero := Prf.hyp0
      have nex : (x ≐ zero) :: Γ ⊢[PRAAx] a*succ j ≐ a :=
        ((by dsimp only [x]; ipra_ring : (x ≐ zero) :: Γ ⊢[PRAAx] a*succ j ≐ x+a).eqTrans
          ((congrAdd e (.eqRefl a)).eqTrans (zero_add a)))
      have qz := (observation_numerator_congr x zero d p e).eqTrans (zero_observation d p hd.wk)
      let v := qsub qone (fraction a d)
      have ep : (x ≐ zero) :: Γ ⊢[PRAAx] qmul (observation x d p) v ≐ v :=
        (qmul_congr qz (.eqRefl v)).eqTrans
          ((qmul_commutative qone v).eqTrans (qmul_one_right v (qsub_canonical _ _)))
      have hz : (x ≐ zero) :: Γ ⊢[PRAAx] le one (d*d*U) :=
        positive_product _ _ (positive_product _ _ hd.wk hd.wk) (unit_positive p)
      exact distance_congr (observation_numerator_congr _ _ _ _ nex).eqSymm ep.eqSymm (.eqRefl _) (.eqRefl _)
        (distance_radius_mono _ _ _ _ _ _ hz hz
          (le_of_eq_add (d := (two*a*a*U+num 18*(d*d))*(d*d*U)) (by dsimp only [three]; ipra_ring))
          (GaussianEulerDecayAddition.original_decay_linear_remainder a d p hd.wk had.wk))
    · have e : (x ≐ succ (pred x)) :: Γ ⊢[PRAAx] le one x :=
        Order.zero_lt_of_eq_succ Prf.hyp0
      have next : (x ≐ succ (pred x)) :: Γ ⊢[PRAAx]
          observation (x*d+a*d) (d*d) p ≐ observation (a*succ j) d p :=
        (observation_numerator_congr (x*d+a*d) ((a*succ j)*d) (d*d) p (by dsimp only [x]; ipra_ring)).eqTrans
        (observation_rescale (a*succ j) d d p hd.wk hd.wk)
      exact distance_congr next (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (GaussianEulerDecayIncrement.decay_linear_increment x d a d p e hd.wk ha.wk hd.wk had.wk)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hd hd) (unit_positive p))
    (positive_product _ _ (positive_product _ _ hN hN) (unit_positive p))
    (by dsimp only [rowDen,three]; ipra_le 3*𝔞(a*a)*𝔞(U*U)*sl (sq_le_sq hNd)) raw

private theorem correction_bound (a b N p : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (correction a b N) (two*a*a*unit p) (rowDen p N) := by
  let d := b*N*N
  have hd := positive_product (Γ := Γ) _ _ (positive_product _ _ hb hN) hN
  have hden := positive_product _ _ (positive_product _ _ hN hN) (unit_positive p)
  have lo := mul_le_mul_right N (mul_le_mul_right N hb)
  have r := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point (two*a*a) d hd).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded (two*a*a) d hd)
  exact bounded_radius_mono _ _ _ _ _ hd hden
    (le_congr (by dsimp only [rowDen]; ipra_ring) (by ipra_ring)
      (mul_le_mul_right (two*a*a*unit p) lo)) r

private theorem subtract_error (x v A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x) (hv : Γ ⊢[PRAAx] bounded v A D) :
    Γ ⊢[PRAAx] distanceBounded (qsub x v) x A D :=
  distance_congr (.eqRefl _) (GaussianRationalLinearProduct.qadd_zero_right x hx) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.sum_right_error x (qnegative v) qzero A D hD
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMpr (bounded_negative v A D hD hv)))

theorem local_step (j p a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (haN : Γ ⊢[PRAAx] le a N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (primitiveValue p a b (succ j) N) (primitiveValue p a b j N))
      (qmul (panelScale a b N) (rowValue p a b j N)) (rowError p a b N) (rowDen p N) := by
  let x := observation (a*j) (b*N) p
  let y := observation (a*succ j) (b*N) p
  let c := primitiveCoefficient a b j N
  let d := primitiveCoefficient a b (succ j) N
  let s := qsub qone (fraction a (b*N))
  let t := qmul (panelScale a b N) (tagWeight j N)
  let corr := correction a b N
  let W := rowDen p N
  let cost := three*a*a*unit p+num 20*(N*N)
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ (positive_product _ _ hN hN) (unit_positive p)
  have hd := GaussianBinetWeightedExponentialAlgebra.coefficient_bound a b (succ j) N hN hj
  have first := GaussianApproximateInverseDistance.multiply_distance d y (qmul x s) (cap a b) cost W hW hd
    (adjacent_decay a b j N p ha hb hN haN)
  have diff := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hW first
    (GaussianRationalPowerDifference.distance_refl_zero (qmul c x) W hW)
  have convert (u v : PTm n) : Γ ⊢[PRAAx] qmul u (qmul x v) ≐ qmul x (qmul u v) :=
    GaussianRationalPowerAlgebra.commute_nested u x v
  have model : Γ ⊢[PRAAx] qsub (qmul d (qmul x s)) (qmul c x) ≐ qmul x (qsub t corr) := (qsub_congr (convert d s) (qmul_commutative c x)).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference x (qmul d s) c).eqTrans
      (qmul_congr (.eqRefl x) (GaussianBinetWeightedExponentialAlgebra.local_coefficient a b j N hb hN)))
  have stepEq : Γ ⊢[PRAAx] qmul x t ≐ qmul (panelScale a b N) (rowValue p a b j N) :=
    (qmul_commutative x t).eqTrans (qmul_associative _ _ _)
  have second := GaussianApproximateInverseDistance.multiply_distance x (qsub t corr) t three
    (two*a*a*unit p) W hW (decay_bound (a*j) (b*N) p (positive_product _ _ hb hN))
    (subtract_error t corr _ _ hW (qmul_canonical _ _) (correction_bound a b N p hb hN))
  exact distance_congr (.eqRefl _) stepEq (by dsimp only [rowError,meshCost,observationCost,cost,three]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hW (distance_congr (.eqRefl _) model (.eqRefl _) (.eqRefl _) diff) second)

theorem finite_error (p N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hN : Γ ⊢[PRAAx] le one N) (haN : Γ ⊢[PRAAx] le a N) :
    Γ ⊢[PRAAx] distanceBounded (value p N a b) (endpoint p a b)
      (b*rowError p a b N) (N*unit p) := by
  let f := sampleBody evaluatorF
  let x := primitiveData p a b N
  let y := sampleData p N one one one (pairT a b)
  let c := panelScale a b N
  let E := rowError p a b N
  let W := rowDen p N
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ (positive_product _ _ hN hN) (unit_positive p)
  have rows : Γ ⊢[PRAAx] localRows primitiveBody f N x y c E W := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have as' : Δ ⊢[PRAAx] le one (s a) := (Order.shift_one_le ha).wk
    have bs : Δ ⊢[PRAAx] le one (s b) := (Order.shift_one_le hb).wk
    have ns : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have an : Δ ⊢[PRAAx] le (s a) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using haN.shift.wk
    have next := qsub_congr (primitive_at (Γ := Δ) (succ (var 0)) (s p) (s a) (s b) (s N))
      (primitive_at (var 0) (s p) (s a) (s b) (s N))
    have rr := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) f (panelScale (s a) (s b) (s N)) (var 0)
      (sampleData (s p) (s N) one one one (pairT (s a) (s b)))).eqTrans
      (qmul_congr (.eqRefl _) (cell_at (var 0) (s p) (s N) (s a) (s b)))
    simpa only [localRows,GaussianRationalRiemannRefinement.termsDistance,Syn.shift,s,Δ,x,y,c,E,W,f,
      subst_primitiveData,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      GaussianBinetWeightedExponentialAlgebra.subst_panelScale,subst_rowError,subst_rowDen,
      forward_at,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr next.eqSymm rr.eqSymm (.eqRefl _) (.eqRefl _)
        (local_step (var 0) (s p) (s a) (s b) (s N) as' bs ns an Prf.hyp0)
  have raw := GaussianRationalParameterTelescope.local_error primitiveBody f N x y c E W hW rows
  have er : Γ ⊢[PRAAx] inst2 primitiveBody N x ≐ qmul (rightCoefficient a b) (observation a b p) :=
    (primitive_at N p a b N).eqTrans (qmul_congr (GaussianBinetWeightedExponentialAlgebra.right_read a b N hN)
      (observation_rescale a b N p hb hN))
  have el : Γ ⊢[PRAAx] inst2 primitiveBody zero x ≐ leftCoefficient a b :=
    (primitive_at zero p a b N).eqTrans ((qmul_congr (GaussianBinetWeightedExponentialAlgebra.left_read a b N hN)
      ((observation_numerator_congr (a*zero) zero (b*N) p (by ipra_ring)).eqTrans
        (zero_observation (b*N) p (positive_product _ _ hb hN)))).eqTrans
        (qmul_one_right _ (qsub_canonical _ _)))
  have scale_at : Γ ⊢[PRAAx] qmul (integrationScale a b) (value p N a b) ≐ qmul c (sum f N y) := by
    have ew : Γ ⊢[PRAAx] GaussianRationalRiemannRefinement.weight one one N ≐ fraction one N :=
      GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul N)
    exact ((qmul_associative (integrationScale a b) (GaussianRationalRiemannRefinement.weight one one N) (sum f N y)).eqSymm).eqTrans
      (qmul_congr ((qmul_congr (.eqRefl _) ew).eqTrans
        (GaussianBinetWeightedExponentialAlgebra.scale_factorization a b N hb hN)) (.eqRefl _))
  have back : Γ ⊢[PRAAx] le one (two*a*a) := positive_product _ _ (positive_product _ _ (le_succ_self one) ha) ha
  have inv : Γ ⊢[PRAAx] bounded (inverseScale a b) b one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ back
      (le_congr (one_mul b) (mul_comm _ _) (mul_le_mul_right b back))
  have prec := distance_congr scale_at.eqSymm (qsub_congr er el) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ hW raw)
  have z := GaussianApproximateInverseDistance.multiply_distance (inverseScale a b) _ _ b (N*E) W hW inv prec
  have left : Γ ⊢[PRAAx] qmul (inverseScale a b) (qmul (integrationScale a b) (value p N a b)) ≐ value p N a b :=
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr
      (GaussianBinetWeightedExponentialAlgebra.inverse_product a b ha hb) (.eqRefl _))).eqTrans
      ((qmul_commutative qone _).eqTrans (qmul_one_right _ (qmul_canonical _ _)))
  exact distance_radius_mono _ _ _ _ _ _ hW (positive_product _ _ hN (unit_positive p))
    (le_of_eq_add (d := zero) (by dsimp only [E,W,rowDen]; ipra_ring))
    (distance_congr left (.eqRefl _) (.eqRefl _) (.eqRefl _) z)

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialGrid

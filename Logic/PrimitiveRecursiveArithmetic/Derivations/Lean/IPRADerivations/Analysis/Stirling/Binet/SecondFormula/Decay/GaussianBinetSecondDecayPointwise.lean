import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.Stirling.Binet.ExponentialIntegrals.GaussianBinetExponentialPanel
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentQuadratureBound
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelPi

/-!
# The original arctangent times a frozen second Binet decay row

At half rate H/J ≥ m, one factor of the decay controls the linear
arctangent bound. The other half-rate decay remains in a positive
scalar envelope. The bounds apply at the physical tag zero as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayPointwise

open_ipra
open GaussianBinetExponentialPanel (sample)
open GaussianBinetSecondDecayEnvelope (envelope fraction_majorized)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayPoint)
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianStirlingConstant (piNumerator piDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product qadd qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSumMajorant (majorized majorized_multiply majorized_add majorized_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def halfDecay (p a b H J : PTm n) : PTm n := observation (a*H) (b*J) p
def fullDecay (p a b H J : PTm n) : PTm n := observation (two*(a*H)) (b*J) p
def angle (p X Y D sign a b : PTm n) : PTm n :=
  ap2 GaussianBinetArctangentQuadrature.nameF p (GaussianBinetArctangentQuadrature.data X Y D sign a b)
def row (p X Y D sign a b H J : PTm n) : PTm n := qmul (angle p X Y D sign a b) (fullDecay p a b H J)
def rowEnvelope (p m K T a b H J : PTm n) : PTm n :=
  RationalArithmetic.add (RationalArithmetic.multiply (fraction (two*K) m) (envelope p (a*H) (b*J)))
    (fraction (num 10*K*T) (unit p))

ipra_subst row [angle, fullDecay, two]

ipra_subst rowEnvelope [two]

def frozenPiNumerator (m k : PTm n) : PTm n := m*piNumerator k

theorem frozen_pi_rate (m k : PTm n) : Γ ⊢[PRAAx]
    le one (piDenominator k) ⋏ le (m*piDenominator k) (frozenPiNumerator m k) :=
  by
    let J := piDenominator k
    let H := piNumerator k
    have h₁ : Γ ⊢[PRAAx] le J (two*J) :=
      le_congr (one_mul J) (.eqRefl _) (mul_le_mul_right J (le_succ_self one))
    have h₂ : Γ ⊢[PRAAx] le J H := le_trans h₁ (GaussianBinetKernelPi.sample_margins k).andE₁
    exact .andI (GaussianBinetKernelPi.denominator_positive k)
      (le_congr (mul_comm J m) (mul_comm H m) (mul_le_mul_right m h₂))

private theorem doubled_argument (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qadd (decayPoint a b) (decayPoint a b) ≐ decayPoint (two*a) b := by
  have read : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.fraction (a*b+a*b) (b*b) ≐
      GaussianPositiveRationalLogarithm.fraction (two*a) b :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel b (two*a) b hb hb)
  exact (GaussianEulerDecayAddition.decay_point_add a b a b hb hb).eqTrans
    (GaussianInverseBinomialRows.negative_congr read)

private theorem exponential_input_congr (R x y : PTm n) (e : Γ ⊢[PRAAx] x ≐ y)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF R x) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF R y := by
  simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
    using Prf.eqSubst1 (GaussianRadiusExponentialName.input constantF (Syn.shift R) (var 0)) e
      (by simpa only [GaussianRadiusExponentialName.subst_input,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h)

theorem squared_decay (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (observation (two*a) b p) (qmul (observation a b p) (observation a b p))
      (num 10) (unit p) := by
  let x := decayPoint a b
  let y := decayPoint (two*a) b
  let R := GaussianNameBounds.U constantF x
  let S := GaussianNameBounds.U constantF y
  have hX := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF x (constant_regular x)
  have hY := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF y (constant_regular y)
  have e := doubled_argument a b hb
  have read : Γ ⊢[PRAAx] sample p (qadd x x) S ≐ sample p y S :=
    congrAp2 GaussianBinetExponentialPanel.expoF (.eqRefl p) (congrPairT (.eqRefl S) e)
  have nonpos := GaussianBinetLaplaceScalarMajorant.decay_nonpositive a b hb
  exact distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBinetExponentialPanel.product_sample p x x R R S hX hX
      (exponential_input_congr S y (qadd x x) e.eqSymm hY) nonpos nonpos)

theorem angle_half_bound (p X Y D sign a b H J m K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hb : Γ ⊢[PRAAx] le one b) (hJ : Γ ⊢[PRAAx] le one J)
    (hm : Γ ⊢[PRAAx] le one m) (hRate : Γ ⊢[PRAAx] le (m*J) H) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hclock : Γ ⊢[PRAAx] le (two*(a*H)) (unit p)) :
    Γ ⊢[PRAAx] bounded (qmul (angle p X Y D sign a b) (halfDecay p a b H J)) (two*K) m := by
  let v := angle p X Y D sign a b
  let w := halfDecay p a b H J
  have hX := hz.andE₁.andE₁
  have d := positive_product _ _ hb hX
  have s := positive_product _ _ hb hJ
  have av := GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb
  refine .orE (zero_or_succ a) ?_ ?_
  · let Δ := (a ≐ zero) :: Γ
    have az : Δ ⊢[PRAAx] a*D ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl D)).eqTrans (by ipra_ring)
    have hv : Δ ⊢[PRAAx] bounded v zero (b*X) := bound_congr (.eqRefl _) az (.eqRefl _) av.wk
    have hw := GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound (Γ := Δ) p (a*H) (b*J) s.wk
    have hp := unit_positive (Γ := Δ) p
    have prod := bounded_product v w zero (b*X) (unit p+one) (unit p) d.wk hp hv hw
    exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ d.wk hp) hm.wk
      (by ipra_le 2*𝔞(K)*𝔞(b)*𝔞(X)*𝔞(unit p)) prod
  · let Δ := (a ≐ ConciseIPRA.PTm.succ (pred a)) :: Γ
    have ha : Δ ⊢[PRAAx] le one a := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have hH : Δ ⊢[PRAAx] le one H := le_trans (positive_product _ _ hm.wk hJ.wk) hRate.wk
    have hA := positive_product _ _ ha hH
    have hw := GaussianBinetSecondDecayEnvelope.inverse_linear p (a*H) (b*J) hA s.wk hclock.wk
    have prod := bounded_product v w (a*D) (b*X) (two*(b*J)) (a*H) d.wk hA av.wk hw
    exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ d.wk hA) hm.wk
      (by ipra_le 2*𝔞(a)*𝔞(b)*𝔞(m)*𝔞(J)*sl hK.wk+2*𝔞(a)*𝔞(b)*𝔞(K)*𝔞(X)*sl hRate.wk) prod

theorem row_majorized (p X Y D sign a b H J m K T : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hb : Γ ⊢[PRAAx] le one b) (hJ : Γ ⊢[PRAAx] le one J)
    (hm : Γ ⊢[PRAAx] le one m) (hRate : Γ ⊢[PRAAx] le (m*J) H) (hK : Γ ⊢[PRAAx] le D (K*X))
    (ht : Γ ⊢[PRAAx] le a (T*b)) (hclock : Γ ⊢[PRAAx] le (two*(a*H)) (unit p)) :
    Γ ⊢[PRAAx] majorized (row p X Y D sign a b H J) (rowEnvelope p m K T a b H J) := by
  let v := angle p X Y D sign a b
  let w := halfDecay p a b H J
  let f := fullDecay p a b H J
  let o := qmul v f
  let z := qmul (qmul v w) w
  have hp := unit_positive (Γ := Γ) p
  have hbJ := positive_product _ _ hb hJ
  have dx := positive_product _ _ hb hz.andE₁.andE₁
  have direct : Γ ⊢[PRAAx] bounded v (K*T) one :=
    bounded_radius_mono _ _ _ _ _ dx (le_refl one)
      (by ipra_le 𝔞(D)*sl ht+𝔞(T)*𝔞(b)*sl hK)
      (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb)
  have close : Γ ⊢[PRAAx] distanceBounded o z (num 10*K*T) (unit p) :=
    distance_congr (.eqRefl _) (qmul_associative v w w).eqSymm (by ipra_ring) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance v f (qmul w w) (K*T) (num 10) (unit p) hp
        direct (squared_decay p (a*H) (b*J) hbJ))
  have lead := majorized_multiply _ _ _ _
    (fraction_majorized _ _ _ hm (angle_half_bound p X Y D sign a b H J m K hz hb hJ hm hRate hK hclock))
    (GaussianBinetSecondDecayEnvelope.decay_majorized p (a*H) (b*J) hbJ)
  have error := fraction_majorized (qsub o z) (num 10*K*T) (unit p) hp close
  exact majorized_congr (GaussianRationalLinearProduct.add_sub_right z o (qmul_canonical v f)) (.eqRefl _)
    (majorized_add _ _ _ _ lead error)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayPointwise

import IPRADerivations.Analysis.GaussianGammaDigammaPositiveTerms
import IPRADerivations.Analysis.GaussianGammaLogHarmonicName

/-!
# Finite Euler reciprocal-sum slopes and the native digamma

For x=a/b, the Euler logarithmic slope at cutoff N is implemented as
log N − Σ_{0≤j≤N}1/(x+j). Its comparison to the original digamma
has the independent rate (a+2)/N plus the two observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaEulerDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry)
open GaussianGammaDigammaPositiveTerms (last_term_bound)
open GaussianGammaFiniteApproximantName (logF log_regular)
open GaussianGammaLogHarmonicName (fixedF fixed_regular sum_sample_at)
open GaussianNameRingLaws (three)
open GaussianNamedDifference (difference_distance)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper_mono radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "SF" => GaussianGammaDigammaSeries.nameF
local notation "sd" => GaussianGammaDigammaSeries.data
local notation "GF" => GaussianGammaCanonicalExponent.gammaF

def nameF : PR 2 := GaussianNamedDifference.nameF logF constantF
def data (a b N : PTm n) : PTm n := GaussianNamedDifference.data N (reciprocalSum a b (succ N))
def budget (a N : PTm n) : PTm n := GaussianGammaDigammaSeries.budget a N+num 17

def rateCoefficient (a : PTm n) : PTm n := a+two

@[simp] theorem subst_rateCoefficient {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (rateCoefficient a) = rateCoefficient (Syn.subst σ a) := by simp [rateCoefficient]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (data a b N) = data (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a N : PTm n) :
    Syn.subst σ (budget a N) = budget (Syn.subst σ a) (Syn.subst σ N) := by simp [budget]

theorem name_regular (a b N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] pointCN nameF (data a b N) :=
  GaussianNamedDifference.name_regular _ _ _ _ (log_regular N hN) (constant_regular _)

private theorem gamma_comparison (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 fixedF p N) (ap2 GF p zero) (unit p+two*N) (N*unit p) := by
  let g := GammaEulerConstantName.gammaSample p zero
  let f := GammaEulerConstantName.fixedSample p N
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have h := GammaEulerConstantName.C2_samples N p p zero hN
  have e : Γ ⊢[PRAAx] RationalValueBounds.radius f g (U+two*N) (N*U) := by
    refine radius_of_upper _ _ _ _ ?_ ?_
    · exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hN hp) hp) h.andE₂
        (le_of_eq_add (d := zero) (by unfold U GammaEulerConstantName.unit GaussianCoefficientNameBounds.unit; ipra_ring))
    · exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) h.andE₁
        (le_of_eq_add (d := U*U*U) (by unfold U GammaEulerConstantName.unit GaussianCoefficientNameBounds.unit; ipra_ring))
  exact distance_congr (RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.fixedF p N).eqSymm
    (GaussianGammaCanonicalExponent.gamma_sample_at p).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hN hp) e)

theorem log_sample_error (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logF p N) (qadd (ap2 negativeGammaF p negativeGammaData) (harmonicPoint N))
      (unit p+num 8*N) (N*unit p) := by
  let g := ap2 GF p (zero : PTm n)
  let f := ap2 fixedF p N
  let l := ap2 logF p N
  let h := harmonicPoint N
  let m := ap2 negativeGammaF p (negativeGammaData : PTm n)
  let T := unit p
  let D := N*T
  let r := (GaussianRationalHorner.qzero : PTm n)
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have px := GaussianNameRingLaws.add_sample_error fixedF logF N N p (fixed_regular N hN) (log_regular N hN)
  have hf := distance_congr (sum_sample_at p N hN) (.eqRefl _) (.eqRefl _) (.eqRefl _) px
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical l :=
    RationalGaussianNameEmbedding.sample_canonical GammaMeshRobinLogBridge.meshLogF p N
  have h1 := difference_distance (qadd f l) h f f three zero T hp
    (distance_symmetric _ _ _ _ hp hf) (GaussianRationalPowerDifference.distance_refl_zero f T hp)
  have h2 := difference_distance h h f g zero (T+two*N) D hd
    (GaussianRationalPowerDifference.distance_refl_zero h D hd) (gamma_comparison p N hN)
  have left := distance_congr (GaussianRationalSyntheticDivision.qadd_sub_cancel f l hc) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ ((three+zero)*N) D hp hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) h1)
  have neg := GaussianNameRingLaws.negative_sample_error GF zero p (GaussianGammaCanonicalExponent.gamma_regular (Γ := Γ))
  have nRaw := GaussianNameRingLaws.sum_left_error _ _ h three T hp (distance_symmetric _ _ _ _ hp neg)
  have law : Γ ⊢[PRAAx] qadd (qsub r g) h ≐ qsub h g :=
    (qadd_congr (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qadd_commutative _ _)
  have last := distance_radius_mono _ _ _ _ (three*N) D hp hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring))
    (distance_congr law (.eqRefl _) (.eqRefl _) (.eqRefl _) nRaw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd left h2) last)

private theorem final_reciprocal_error (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (reciprocalSum a b (succ N)) (reciprocalSum a b N) one N := by
  let A := reciprocalSum a b N
  let B := fraction b (index a b N)
  have e : Γ ⊢[PRAAx] reciprocalSum a b (succ N) ≐ qadd A B :=
    (GaussianRationalFiniteSum.sum_succ reciprocalBody N (pairT a b)).eqTrans (qadd_congr (.eqRefl _) (reciprocal_entry a b N))
  have pos := (GaussianGammaDigammaFiniteSum.row_source a b N hs).andE₁
  have exactDiff := (qsub_congr e (.eqRefl A)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel A B (GaussianRationalHorner.ofGaussian_canonical _ _ pos))
  exact GaussianRationalReciprocal.bound_congr exactDiff.eqSymm (.eqRefl _) (.eqRefl _) (last_term_bound a b N hs hN)

set_option maxHeartbeats 850000 in
theorem cutoff_error (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 SF p (sd a b N)) (ap2 nameF p (data a b N))
      (two*unit p+num 17*N) (N*unit p) := by
  let T := unit p
  let D := N*T
  let L := ap2 logF p N
  let h := harmonicPoint N
  let g := ap2 negativeGammaF p (negativeGammaData : PTm n)
  let u := reciprocalSum a b N
  let v := reciprocalSum a b (succ N)
  let C := GaussianGammaDigammaSeries.partialValue a b N
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have lift (x y A : PTm n) (d : Γ ⊢[PRAAx] distanceBounded x y A T) : Γ ⊢[PRAAx]
      distanceBounded x y (A*N) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) d
  have left := GaussianNameRingLaws.add_sample_error negativeGammaF constantF negativeGammaData C p
    (negativeGamma_regular (Γ := Γ)) (constant_regular C)
  have law : Γ ⊢[PRAAx] qadd g C ≐ qsub (qadd g h) u :=
    (GaussianRationalSumAlgebra.qadd_associative g h (qnegative u)).eqSymm
  have e1 := lift _ _ _ (distance_congr (.eqRefl _) ((qadd_congr (.eqRefl _) (constant_at p C)).eqTrans law) (.eqRefl _) (.eqRefl _) left)
  have eTail := distance_radius_mono _ _ _ _ T D hN hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring))
    (distance_symmetric _ _ _ _ hN (final_reciprocal_error a b N hs hN))
  have e2 := difference_distance (qadd g h) L u v (T+num 8*N) T D hd
    (distance_symmetric _ _ _ _ hd (log_sample_error p N hN)) eTail
  have right := GaussianNamedDifference.sample_error logF constantF N v p (log_regular N hN) (constant_regular v)
  have e3 := lift _ _ _ (distance_symmetric _ _ _ _ hp
    (distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p v)) (.eqRefl _) (.eqRefl _) right))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd e1 e2) e3)

theorem sample_error (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b)) (ap2 nameF p (data a b N))
      (GaussianNamedLipschitzRate.diagonalNumerator (rateCoefficient a) N (budget a N) p)
      (GaussianNamedLipschitzRate.diagonalDenominator N p) := by
  have hp := positive_product _ _ hN (unit_positive p)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget rateCoefficient GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (GaussianGammaDigammaSeries.sample_error p a b N hs hN) (cutoff_error p a b N hs hN))

set_option maxHeartbeats 850000 in
theorem original_rate (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate DF nameF (dd a b) (data a b N) (rateCoefficient a) N := by
  apply GaussianNamedLipschitzRate.independent_rate DF nameF _ _ (rateCoefficient a) N (budget a N) hN
    (GaussianGammaDigammaNative.name_regular a b hs) (name_regular a b N hN)
  refine .allI ?_
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 DF (var 0) (Syn.shift (dd a b))) (ap2 nameF (var 0) (Syn.shift (data a b N)))
    (GaussianNamedLipschitzRate.diagonalNumerator (Syn.shift (rateCoefficient a)) (Syn.shift N) (Syn.shift (budget a N)) (var 0))
    (GaussianNamedLipschitzRate.diagonalDenominator (Syn.shift N) (var 0))
  simp only [Syn.shift,GaussianGammaDigammaNative.subst_data,subst_data,subst_budget,subst_rateCoefficient]
  exact sample_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) hh hn

theorem actual_original_finite_euler_digamma_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le one (var 2) ⟶ independentRate DF nameF (dd (var 0) (var 1))
      (data (var 0) (var 1) (var 2)) (var 0+two) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_rate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaEulerDerivative

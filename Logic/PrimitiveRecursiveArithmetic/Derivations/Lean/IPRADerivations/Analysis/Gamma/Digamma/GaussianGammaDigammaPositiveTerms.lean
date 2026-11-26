import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaSeriesTerms
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageWeights

/-!
# The positive-term digamma series

Each original term 1/k − 1/(x+k), for k≥1, equals x/[k(k+x)].
The explicit first term −1/x gives the paper's positive-term form.
The cutoff N omits one more reciprocal than the difference form, so
its independent rate has coefficient a+1 for x=a/b.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaPositiveTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry row_source)
open GaussianGammaDigammaSeries (partialValue)
open GaussianGammaDigammaSeriesTerms (subtract_add_exchange)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open GaussianNameArithmetic (addData)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "SF" => GaussianGammaDigammaSeries.nameF
local notation "sd" => GaussianGammaDigammaSeries.data

def termBody : PTm 2 := fraction (fstT (var 1))
  (succ (var 0)*index (fstT (var 1)) (sndT (var 1)) (succ (var 0)))
def positiveSum (a b N : PTm n) : PTm n := GaussianRationalFiniteSum.sum termBody N (pairT a b)
def correction (a b N : PTm n) : PTm n := qsub (positiveSum a b N) (fraction b a)
def data (a b N : PTm n) : PTm n := addData negativeGammaData (correction a b N)
def budget (a N : PTm n) : PTm n := GaussianGammaDigammaSeries.budget a N+num 6

def rateCoefficient (a : PTm n) : PTm n := a+one

@[simp] theorem subst_rateCoefficient {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (rateCoefficient a) = rateCoefficient (Syn.subst σ a) := by simp [rateCoefficient]

@[simp] theorem subst_positiveSum {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (positiveSum a b N) = positiveSum (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [positiveSum]
@[simp] theorem subst_correction {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (correction a b N) = correction (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [correction]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (data a b N) = data (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a N : PTm n) :
    Syn.subst σ (budget a N) = budget (Syn.subst σ a) (Syn.subst σ N) := by simp [budget]

theorem term_value (a b k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] qsub (fraction one k) (fraction b (index a b k)) ≐ fraction a (k*index a b k) := by
  let c := index a b k
  let d := k*c
  have hc : Γ ⊢[PRAAx] le one c := le_trans ha (le_add_right _ _)
  have hd := positive_product _ _ hk hc
  have e := GaussianStirlingRationalTelescopers.fraction_same one k c d hk hd (by unfold d; ipra_ring)
  have f := GaussianStirlingRationalTelescopers.fraction_same b c (k*b) d hc hd (by unfold d; ipra_ring)
  have g := GaussianEulerPositivePowerChartImageWeights.fraction_difference (k*b) c d hd (le_add_left _ _)
  exact (qsub_congr e f).eqTrans (g.eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _
    (add_monus a (k*b)) (.eqRefl _)))

theorem term_at (a b j : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] inst2 termBody j (pairT a b) ≐
      qsub (reciprocalPoint j) (fraction b (index a b (succ j))) := by
  let k := succ j
  have exactRead : Γ ⊢[PRAAx] inst2 termBody j (pairT a b) ≐ fraction a (k*index a b k) := by
    change Γ ⊢[PRAAx] Syn.subst ![j,pairT a b] termBody ≐ _
    simp only [termBody,GaussianPositiveRationalLogarithm.subst_fraction,GaussianGammaDigammaFiniteSum.subst_index,
      PTm.subst_mul,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,ConciseIPRA.PTm.subst_succ]
    exact GaussianCompactRiemannName.fraction_congr _ _ _ _ (fst_pair _ _)
      (congrMul (.eqRefl _) (congrAdd (fst_pair _ _) (congrMul (.eqRefl _) (snd_pair _ _))))
  exact exactRead.eqTrans ((term_value a b k ha (zero_lt_succ j)).eqSymm.eqTrans
    (qsub_congr (GaussianGammaDigammaStep.unit_step_value k (zero_lt_succ j)) (.eqRefl _)))

def sumLaw (a b N : PTm n) : Fm PTm n :=
  positiveSum a b N ≐ qsub (harmonicPoint N) (GaussianRationalFiniteSum.sum (shiftBody reciprocalBody) N (pairT a b))
@[simp] theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    (sumLaw a b N).subst σ = sumLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [sumLaw]

private theorem sum_base (a b : PTm n) : Γ ⊢[PRAAx] sumLaw a b zero :=
  (GaussianRationalFiniteSum.sum_zero termBody _).eqTrans ((qsub_congr GaussianGammaEulerHeadQuadratic.harmonic_zero
    (GaussianRationalFiniteSum.sum_zero (shiftBody reciprocalBody) _)).eqTrans GaussianRationalDeflationError.qsub_zero_zero).eqSymm

private theorem sum_step (a b j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (ih : Γ ⊢[PRAAx] sumLaw a b j) :
    Γ ⊢[PRAAx] sumLaw a b (succ j) := by
  let x := pairT a b
  let r := shiftBody reciprocalBody
  have step :
      Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum r (succ j) x ≐ qadd (GaussianRationalFiniteSum.sum r j x) (fraction b (index a b (succ j))) := by
    refine (GaussianRationalFiniteSum.sum_succ r j x).eqTrans (qadd_congr (.eqRefl _) ?_)
    simpa only [r,inst2_shiftBody] using reciprocal_entry a b (succ j)
  exact (GaussianRationalFiniteSum.sum_succ termBody j x).eqTrans
    ((qadd_congr ih (term_at a b j ha)).eqTrans
      ((subtract_add_exchange (harmonicPoint j) (GaussianRationalFiniteSum.sum r j x) (reciprocalPoint j) (fraction b (index a b (succ j)))).eqTrans
        (qsub_congr (harmonic_point_increment j).eqSymm step.eqSymm)))

theorem positive_sum_exact (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] sumLaw a b N := by
  have shift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using sum_base (Γ := Γ) a b
    · simpa only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        sum_step (Syn.shift a) (Syn.shift b) (var 0) shift.wk Prf.hyp0
  simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem correction_exact (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] correction a b N ≐ qsub (partialValue a b N) (fraction b (index a b N)) := by
  let x := pairT a b
  let H := harmonicPoint N
  let P := GaussianRationalFiniteSum.sum (shiftBody reciprocalBody) N x
  let Q := reciprocalSum a b N
  let inv := fraction b a
  let endp := fraction b (index a b N)
  have h0 : Γ ⊢[PRAAx] index a b zero ≐ a := by unfold index; ipra_ring
  have first := (reciprocal_entry (Γ := Γ) a b zero).eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) h0)
  have split : Γ ⊢[PRAAx] reciprocalSum a b (succ N) ≐ qadd inv P :=
    (GaussianRationalFiniteSum.sum_shift_first _ _ _).eqTrans (qadd_congr first (.eqRefl _))
  have last : Γ ⊢[PRAAx] reciprocalSum a b (succ N) ≐ qadd Q endp :=
    (GaussianRationalFiniteSum.sum_succ reciprocalBody N x).eqTrans (qadd_congr (.eqRefl _) (reciprocal_entry a b N))
  have c := (qsub_congr (positive_sum_exact a b N ha) (.eqRefl inv)).eqTrans
    ((GaussianRationalInverseQuadraticAlgebra.subtract_sum H P inv).eqTrans
      (qsub_congr (.eqRefl H) (GaussianReciprocalHorner.qadd_commutative P inv)))
  exact c.eqTrans ((qsub_congr (.eqRefl H) (split.eqSymm.eqTrans last)).eqTrans
    (GaussianRationalInverseQuadraticAlgebra.subtract_sum H Q endp).eqSymm)

theorem last_term_bound (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (fraction b (index a b N)) one N := by
  let c := index a b N
  have h := row_source a b N hs
  have near := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point b c h.andE₁).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded b c h.andE₁)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ b c one N h.andE₁ hN (by unfold c index; ipra_le 𝔞 a) near


private theorem partial_distance (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (partialValue a b N) (correction a b N) one N := by
  let x := partialValue a b N
  let y := fraction b (index a b N)
  let z := (GaussianRationalHorner.qzero : PTm n)
  have dy : Γ ⊢[PRAAx] distanceBounded y z one N :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalReconstruction.qsub_zero_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ (row_source a b N hs).andE₁)).eqSymm
      (.eqRefl _) (.eqRefl _) (last_term_bound a b N hs hN)
  have raw := GaussianNamedDifference.difference_distance x x z y zero one N hN
    (GaussianRationalPowerDifference.distance_refl_zero x N hN) (distance_symmetric _ _ _ _ hN dy)
  exact distance_congr (GaussianRationalReconstruction.qsub_zero_right x (GaussianRationalMetric.qsub_canonical _ _))
    (correction_exact a b N hs.andE₁).eqSymm (by ipra_ring) (.eqRefl _) raw

private theorem raw_sample_error (p v : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 SF p (addData negativeGammaData v))
      (qadd (ap2 negativeGammaF p negativeGammaData) v) three (unit p) :=
  distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at _ _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.add_sample_error negativeGammaF constantF negativeGammaData v p negativeGamma_regular (constant_regular _))

theorem cutoff_distance (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 SF p (sd a b N)) (ap2 SF p (data a b N))
      (unit p+num 6*N) (N*unit p) := by
  let T := unit p
  let D := N*T
  let h := ap2 negativeGammaF p (negativeGammaData : PTm n)
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hN hp
  have lift (x y A : PTm n) (h : Γ ⊢[PRAAx] distanceBounded x y A T) : Γ ⊢[PRAAx]
      distanceBounded x y (A*N) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) h
  have left := lift _ _ _ (raw_sample_error p (partialValue a b N))
  have right := lift _ _ _ (distance_symmetric _ _ _ _ hp (raw_sample_error p (correction a b N)))
  have mid := GaussianNameRingLaws.sum_right_error h _ _ one N hN (partial_distance a b N hs hN)
  have mid' := distance_radius_mono _ _ _ _ T D hN hd (le_of_eq_add (d := zero) (by unfold D; ipra_ring)) mid
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd left mid') right)

theorem sample_error (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 DF p (dd a b)) (ap2 SF p (data a b N))
      (GaussianNamedLipschitzRate.diagonalNumerator (rateCoefficient a) N (budget a N) p)
      (GaussianNamedLipschitzRate.diagonalDenominator N p) := by
  have hp := positive_product _ _ hN (unit_positive p)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget rateCoefficient GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (GaussianGammaDigammaSeries.sample_error p a b N hs hN) (cutoff_distance p a b N hs hN))

set_option maxHeartbeats 800000 in
theorem original_rate (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate DF SF (dd a b) (data a b N) (rateCoefficient a) N := by
  apply GaussianNamedLipschitzRate.independent_rate DF SF _ _ (rateCoefficient a) N (budget a N) hN
    (GaussianGammaDigammaNative.name_regular a b hs)
    (GaussianNameArithmetic.add_fast _ _ _ _ negativeGamma_regular (constant_regular _))
  refine .allI ?_
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 DF (var 0) (Syn.shift (dd a b))) (ap2 SF (var 0) (Syn.shift (data a b N)))
    (GaussianNamedLipschitzRate.diagonalNumerator (Syn.shift (rateCoefficient a)) (Syn.shift N) (Syn.shift (budget a N)) (var 0))
    (GaussianNamedLipschitzRate.diagonalDenominator (Syn.shift N) (var 0))
  simp only [Syn.shift,GaussianGammaDigammaNative.subst_data,subst_data,subst_budget,subst_rateCoefficient]
  exact sample_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) hh hn

theorem actual_original_positive_term_digamma_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le one (var 2) ⟶
      GaussianNamedInverseRate.independentRate DF SF (dd (var 0) (var 1)) (data (var 0) (var 1) (var 2))
        (var 0+one) (var 2)) :=
  closeUniv 3 (.impI (.impI (original_rate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaPositiveTerms

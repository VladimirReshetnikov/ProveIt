import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogRoundedTail
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference

/-!
# A fixed finite interval of the original Barnes logarithmic rows

The name retimes the original quotient-rounded row sum. The computed
precision pays for every retained row, so different observation clocks
give a regular name with a radius uniform in the two endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLog

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalLogTail (source tailDenominator tail_denominator_positive tail_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "value" => GaussianBarnesCanonicalLogRoundedTail.value
local notation "roundUnit" => DyadicComplexLogarithm.unit

def gain (N r : PTm n) : PTm n := r*(num 5*(N+r))
def clock (p N r : PTm n) : PTm n := exponent (gain N r) p
def sample (p z R B N r : PTm n) : PTm n := value (clock p N r) z R B N r
def data (z R B N r : PTm n) : PTm n := pairT (pairT z R) (pairT B (pairT N r))

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1))) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2)

def radius (R : PTm n) : PTm n := one+boundNumerator R

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p N r : PTm n) :
    Syn.subst σ (clock p N r) = clock (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [clock,gain]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B N r : PTm n) :
    Syn.subst σ (sample p z R B N r) =
      sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [sample]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    Syn.subst σ (data z R B N r) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [data]

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (radius R) = radius (Syn.subst σ R) := by simp [radius,one]

theorem sample_at (p z R B N r : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B N r) ≐ sample p z R B N r := by
  let d := pairT N r
  let a := pairT z R
  let b := pairT B d
  let x := data z R B N r
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐
      sample p (fstT (fstT x)) (sndT (fstT x)) (fstT (sndT x))
        (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (sample (var 0) (fstT (fstT (var 1))) (sndT (fstT (var 1))) (fstT (sndT (var 1)))
        (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2) ![p,x]
  have left : Γ ⊢[PRAAx] fstT x ≐ a := fst_pair a b
  have right : Γ ⊢[PRAAx] sndT x ≐ b := snd_pair a b
  have part := (congrSnd right).eqTrans (snd_pair B d)
  have eqZ := (congrFst left).eqTrans (fst_pair z R)
  have eqR := (congrSnd left).eqTrans (snd_pair z R)
  have eqB := (congrFst right).eqTrans (fst_pair B d)
  have eqN := (congrFst part).eqTrans (fst_pair N r)
  have eqLen := (congrSnd part).eqTrans (snd_pair N r)
  refine raw.eqTrans ?_
  ipra_congr (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p,eqZ,eqR,eqB,eqN,eqLen]

theorem clock_monotone (p q N r : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (clock p N r) (clock q N r) :=
  add_le_add_right _ h

theorem clock_budget (A p N r v : PTm n) (hA : Γ ⊢[PRAAx] le A (gain N r))
    (late : Γ ⊢[PRAAx] le (clock p N r) v) :
    Γ ⊢[PRAAx] le (A*unit p) (roundUnit v) :=
  le_trans (le_mul_mono hA (le_refl (unit p))) (le_trans (query_budget (gain N r) p)
    (unit_monotone (le_trans late (le_add_right v (num 4)))))

theorem later_rounding (p v z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (late : Γ ⊢[PRAAx] le (clock p N r) v) :
    Γ ⊢[PRAAx] distanceBounded (value v z R B N r) (sample p z R B N r) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive _) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (clock_budget _ p N r _ (le_refl _) (le_refl _)))
    (GaussianBarnesCanonicalLogRoundedTail.ordered_distance _ _ z R B N r h late)

theorem observations (p q z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B N r) (sample q z R B N r)
      (unit p+unit q) (unit p*unit q) := by
  have pos := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  refine .orE (le_total p q) ?_ ?_
  · have near := later_rounding p (clock q N r) z R B N r h.wk (clock_monotone p q N r Prf.hyp0)
    exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) pos.wk
      (le_of_eq_add (d := unit p*unit p) (by ipra_ring))
      (distance_symmetric _ _ _ _ (unit_positive p) near)
  · have near := later_rounding q (clock p N r) z R B N r h.wk (clock_monotone q p N r Prf.hyp0)
    exact distance_radius_mono _ _ _ _ _ _ (unit_positive q) pos.wk
      (le_of_eq_add (d := unit q*unit q) (by ipra_ring)) near

theorem regular (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B N r) := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    distance_congr (sample_at (var 1) (sh z) (sh R) (sh B) (sh N) (sh r)).eqSymm
      (sample_at (var 0) (sh z) (sh R) (sh B) (sh N) (sh r)).eqSymm (.eqRefl _) (.eqRefl _)
      (observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh N) (sh r) hs)

theorem rounding_gain (N r : PTm n) : Γ ⊢[PRAAx] le (r*(two*(N+r))) (gain N r) :=
  le_mul_mono (le_refl r) (mul_le_mul_right (N+r) (le_of_eq_add (d := num 3) (by ipra_ring)))

theorem rounded_bound (v z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (paid : Γ ⊢[PRAAx] le (r*(two*(N+r))) (roundUnit v)) :
    Γ ⊢[PRAAx] bounded (value v z R B N r) (radius R) one := by
  let exactSum := GaussianBarnesCanonicalLogTail.value z B N r (DyadicComplexLogarithm.precision v)
  have hD := tail_denominator_positive N h.andE₂.andE₁
  have exactBound : Γ ⊢[PRAAx] bounded exactSum (boundNumerator R) one :=
    bounded_radius_mono _ _ _ _ _ hD (le_refl one)
      (mul_le_mul_left (boundNumerator R) hD)
      (tail_bound z R B N r _ h)
  have approx : Γ ⊢[PRAAx] distanceBounded (value v z R B N r) exactSum one one :=
    distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive v) (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) paid)
      (GaussianBarnesCanonicalLogRoundedTail.rounding_error v z R B N r h)
  exact bound_congr (.eqRefl _) (by unfold radius; ipra_ring) (by ipra_ring)
    (norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) approx exactBound)

theorem sample_bound (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z R B N r)) (radius R) one := by
  let A := r*(two*(N+r))
  have paid := clock_budget A ConciseIPRA.PTm.zero N r (clock p N r)
    (rounding_gain (Γ := Γ) N r) (clock_monotone _ _ N r (zero_le p))
  have e : Γ ⊢[PRAAx] A*unit ConciseIPRA.PTm.zero ≐ A :=
    (congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)
  exact bound_congr (sample_at p z R B N r).eqSymm (.eqRefl _) (.eqRefl _)
    (rounded_bound _ z R B N r h (le_congr e (.eqRefl _) paid))

theorem exponential_input (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input nameF (radius R) (data z R B N r) := by
  refine .andI (regular z R B N r h) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) :=
    by simpa [Fm.shift,sh,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_data,subst_radius,sh,Syn.shift,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    sample_bound (var 0) (sh z) (sh R) (sh B) (sh N) (sh r) hs

theorem actual_Barnes_finite_log_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianRadiusExponentialName.input nameF (radius (var 1)) (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (exponential_input _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLog

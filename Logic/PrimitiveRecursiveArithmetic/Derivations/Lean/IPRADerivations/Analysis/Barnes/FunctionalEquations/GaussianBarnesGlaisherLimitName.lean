import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesGlaisherEndpointRate

/-!
# The cofinal name of the Glaisher logarithm

Each actual observation reads the literal Glaisher approximant at a
primitive-recursive cutoff. The certified independent-clock rate to the
finite approximant at `N ≥ 2` has leading radius `2/N^2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherLimitName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesGlaisherInterval (sample square square_positive sample_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack_removal_at precision)
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "F" => GaussianBarnesGlaisherFinite.nameF
local notation "d" => GaussianBarnesGlaisherFinite.data
local notation "recode" => GaussianFastValueCut.recode

def cutoff (p : PTm n) : PTm n := two+unit p
def rawF : PR 2 := PTm.toPR (sample (var 0) (cutoff (var 0)) : PTm 2)
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data : PTm n := GaussianFastValueCut.nameData two zero
def clock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
def observation (p : PTm n) : PTm n := ap2 nameF p data

@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (cutoff p) = cutoff (Syn.subst σ p) := by simp [cutoff]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (data : PTm n) = (data : PTm m) := by simp [data]

theorem cutoff_admitted (p : PTm n) : Γ ⊢[PRAAx] le two (cutoff p) := le_add_right _ _
theorem cutoff_monotone {p q : PTm n} (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (cutoff p) (cutoff q) :=
  by
    have h' := unit_monotone h
    unfold cutoff
    ipra_le sl h'

theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (clock p) := le_add_right _ _

theorem cutoff_later (p : PTm n) : Γ ⊢[PRAAx] le p (cutoff p) :=
  le_trans (le_succ_self _) (le_trans (RationalClosure.succ_le_two_pow p) (le_add_left _ _))

theorem raw_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 rawF p x ≐ sample p (cutoff p) := by
  simpa only [rawF,ap2,GaussianBarnesGlaisherInterval.subst_sample,subst_cutoff,Syn.subst_var,Matrix.cons_val_zero]
    using toPR_eq (Γ := Γ) (sample (var 0) (cutoff (var 0)) : PTm 2) ![p,x]

theorem observation_at (p : PTm n) : Γ ⊢[PRAAx] observation p ≐ recode (sample (clock p) (cutoff (clock p))) := by
  exact (GaussianFastValueCut.name_at rawF two zero p).eqTrans
    (GaussianNameArithmetic.recode_congr (raw_at (clock p) zero))

private theorem square_budget (p : PTm n) : Γ ⊢[PRAAx] le (two*unit p) (square (cutoff p)) := by
  unfold square cutoff
  ipra_le (𝔞(unit p))^2 + 2*𝔞(unit p) + 4

private theorem raw_ordered (p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample q (cutoff q)) (sample p (cutoff p))
      (two*(unit p+unit q)) (unit p*unit q) := by
  let N := cutoff p
  let M := cutoff q
  let r := monus M N
  have hN : Γ ⊢[PRAAx] le two N := cutoff_admitted p
  have he : Γ ⊢[PRAAx] M ≐ N+r := eq_add_of_le (cutoff_monotone hpq)
  have s := square_positive _ (le_trans (le_succ_self one) hN)
  have u := unit_positive (Γ := Γ) p
  have v := unit_positive (Γ := Γ) q
  have old := denominator_positive (square N) q p s
  have newDen := positive_product _ _ u v
  have h := GaussianBarnesGlaisherEndpointRate.ordered_gap q p N r hN
  have budget := square_budget (Γ := Γ) p
  refine distance_congr (sample_congr he.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ old newDen ?_ h)
  unfold rateNumerator rateDenominator
  ipra_le 𝔞(unit p)*𝔞(unit q)*(𝔞(unit q)*sl budget + 𝔞(unit p)*𝔞(square N))

theorem raw_observations (p q x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p x) (ap2 rawF q x)
      (two*(unit p+unit q)) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hd := positive_product _ _ hp hq
  refine distance_congr (raw_at p x).eqSymm (raw_at q x).eqSymm (.eqRefl _) (.eqRefl _) ?_
  refine .orE (le_total p q) ?_ ?_
  · exact distance_symmetric _ _ _ _ hd.wk (raw_ordered p q Prf.hyp0)
  · exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (raw_ordered q p Prf.hyp0)

theorem raw_regular : Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF two (zero : PTm n) := by
  refine .allI (.allI ?_)
  simpa only [GaussianFastValueCut.regular,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    using raw_observations (var 1) (var 0) (zero : PTm (n+2))

theorem regular : Γ ⊢[PRAAx] pointCN nameF (data : PTm n) :=
  GaussianFastValueCut.name_fast rawF two zero raw_regular

theorem late_readback (p q N : PTm n) (hN : Γ ⊢[PRAAx] le two N)
    (hC : Γ ⊢[PRAAx] le N (cutoff (clock p))) :
    Γ ⊢[PRAAx] distanceBounded (observation p) (sample q N)
      (rateNumerator two (square N) (clock p) q) (rateDenominator (square N) (clock p) q) := by
  let t := clock p
  let r := monus (cutoff t) N
  have hc : Γ ⊢[PRAAx] cutoff t ≐ N+r := eq_add_of_le hC
  have hD := square_positive N (le_trans (le_succ_self one) hN)
  have hd := denominator_positive (square N) t q hD
  have actual := distance_congr (sample_congr hc.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBarnesGlaisherEndpointRate.ordered_gap t q N r hN)
  exact distance_congr (observation_at p).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.recode_left_distance _ _ _ _ hd actual)

private theorem late_readback_weakened (p q N : PTm n) (hN : Γ ⊢[PRAAx] le two N)
    (hC : Γ ⊢[PRAAx] le N (cutoff (clock p))) :
    Γ ⊢[PRAAx] distanceBounded (observation p) (sample q N)
      (rateNumerator two (square N) p q) (rateDenominator (square N) p q) := by
  let D := square N
  have hD := square_positive N (le_trans (le_succ_self one) hN)
  have hp := unit_monotone (clock_later (Γ := Γ) p)
  refine distance_radius_mono _ _ _ _ _ _
    (denominator_positive D (clock p) q hD) (denominator_positive D p q hD) ?_
    (late_readback p q N hN hC)
  unfold rateNumerator rateDenominator
  ipra_le (𝔞 D*𝔞(unit q))^2*sl hp

theorem finite_limit_observation (p q N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] distanceBounded (observation p) (sample q N)
      (rateNumerator two (square N) p q) (rateDenominator (square N) p q) := by
  let D := square N
  let A := rateNumerator two D p q
  let B := rateDenominator D p q
  let z := qsub (observation p) (sample q N)
  let u := precision z A B two
  let t := N+u
  have hD := square_positive N (le_trans (le_succ_self one) hN)
  have hb : Γ ⊢[PRAAx] le one B := denominator_positive D p q hD
  have hc : Γ ⊢[PRAAx] le N (cutoff (clock t)) :=
    le_trans (le_add_right N u) (le_trans (clock_later t) (cutoff_later _))
  have hLeft := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t)
  have hRight := denominator_positive D t q hD
  have left := GaussianNameEquivalence.point_at nameF data p t (regular (Γ := Γ))
  have right : Γ ⊢[PRAAx] distanceBounded (observation t) (sample q N)
      (rateNumerator two D t q) (rateDenominator D t q) := late_readback_weakened t q N hN hc
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hLeft hRight left right
  have budget : Γ ⊢[PRAAx] le (unit u) (unit t) := unit_monotone (le_add_left u N)
  refine slack_removal_at z A B two hb ?_
  refine distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hLeft hRight)
    (positive_product _ _ hb (unit_positive u)) ?_ joined
  change Γ ⊢[PRAAx] le
    (((unit p+unit t)*rateDenominator D t q+rateNumerator two D t q*(unit p*unit t))*(B*unit u))
    ((A*unit u+two*B)*(unit p*unit t*rateDenominator D t q))
  dsimp only [A,B,rateNumerator,rateDenominator]
  ipra_le 2*(𝔞 D)^2*(𝔞(unit p))^2*(𝔞(unit q))^2*𝔞(unit t)*sl budget

private theorem subst_finite_data {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (d N) = d (Syn.subst σ N) := by
  simp [GaussianBarnesGlaisherFinite.data,GaussianBarnesGlaisherFinite.sumData,
    GaussianBarnesGlaisherFinite.weightedData,GaussianBarnesGlaisherFinite.squareQuarter,
    GaussianBarnesGlaisherQuartic.negativeWeight,GaussianBarnesGlaisherQuartic.weightNumerator]

theorem finite_limit_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate nameF F data (d N) two (square N) := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] le two (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ,two,one] using hN.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,observation,sample,subst_data,subst_finite_data,square,
    PTm.subst_mul,Syn.shift,sh,Δ,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    using finite_limit_observation (var 1) (var 0) (sh N) hs

theorem actual_Glaisher_logarithm_limit_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    pointCN nameF data :=
  regular

theorem actual_Glaisher_logarithm_limit_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ independentRate nameF F data (d (var 0)) two (square (var 0))) :=
  closeUniv 1 (.impI (finite_limit_rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherLimitName

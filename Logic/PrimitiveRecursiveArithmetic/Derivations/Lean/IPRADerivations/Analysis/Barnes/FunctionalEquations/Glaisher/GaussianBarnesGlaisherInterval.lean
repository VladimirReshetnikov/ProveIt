import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherSuccessor

/-!
# Finite inverse-square telescope for the actual Glaisher approximants

Across a finite interval from `N` to `N+r`, the adjacent analytic
inverse-cube rates are paid by an exact inverse-square telescope. All
samples are taken from the literal finite approximant at a common clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherInterval

open_ipra
open GaussianBarnesGlaisherFinite (nameF data)
open GaussianBarnesGlaisherIncrement (cube cube_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def sample (p N : PTm n) : PTm n := ap2 nameF p (data N)
def square (N : PTm n) : PTm n := N*N
def gap (N r : PTm n) : PTm n := r*(two*N+r)
def numerator (p N r : PTm n) : PTm n :=
  two*gap N r*unit p + two*r*square N*square (N+r)
def denominator (p N r : PTm n) : PTm n := square N*square (N+r)*unit p

def estimate (p N r : PTm n) : Fm PTm n :=
  distanceBounded (sample p (N+r)) (sample p N) (numerator p N r) (denominator p N r)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p N : PTm n) :
    Syn.subst σ (sample p N) = sample (Syn.subst σ p) (Syn.subst σ N) := by
  simp [sample,data,GaussianBarnesGlaisherFinite.sumData,GaussianBarnesGlaisherFinite.weightedData,
    GaussianBarnesGlaisherFinite.squareQuarter,GaussianBarnesGlaisherQuartic.negativeWeight,
    GaussianBarnesGlaisherQuartic.weightNumerator]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p N r : PTm n) :
    Syn.subst σ (numerator p N r) = numerator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [numerator,square,gap]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p N r : PTm n) :
    Syn.subst σ (denominator p N r) = denominator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [denominator,square]

@[simp] theorem subst_estimate {m : ℕ} (σ : Fin n → PTm m) (p N r : PTm n) :
    (estimate p N r).subst σ = estimate (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [estimate]

theorem square_positive (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (square N) :=
  positive_product N N hN hN

theorem sample_congr {p N M : PTm n} (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] sample p N ≐ sample p M := by
  simpa only [subst_sample,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using
    Prf.eqCongr1 (sample (Syn.shift p) (var 0)) h

theorem denominator_positive (p N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (denominator p N r) :=
  positive_product _ _ (positive_product _ _ (square_positive N hN)
    (square_positive _ (le_trans hN (le_add_right N r)))) (unit_positive p)

private theorem adjacent (p N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] estimate p N one := by
  let U := unit p
  let D := cube N
  have h1 := le_trans (le_succ_self one) hN
  have hd := cube_positive N h1
  have hOld := positive_product _ _ (positive_product _ _ hd (unit_positive p)) (unit_positive p)
  have hNew := denominator_positive p N one h1
  have edge : Γ ⊢[PRAAx] le ((N+one)*(N+one)) (N*(two*N+one)) := by
    ipra_le 𝔞 N*sl hN + sl h1
  have obs := rate_at nameF nameF (data (succ N)) (data N) two D p p
    (GaussianBarnesGlaisherSuccessor.successor_rate N hN)
  have radius : Γ ⊢[PRAAx] le (rateNumerator two D p p*denominator p N one)
      (numerator p N one*rateDenominator D p p) := by
    unfold rateNumerator rateDenominator numerator denominator gap square D cube
    ipra_le 2*𝔞 N^2*𝔞 U^3*sl edge
  exact distance_congr (sample_congr (by ipra_ring)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hOld hNew radius obs)

private theorem estimate_zero (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] estimate p N zero :=
  distance_congr (sample_congr (by ipra_ring)) (.eqRefl _)
    (by unfold numerator gap; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero (sample p N) (denominator p N zero)
      (denominator_positive p N zero hN))

private theorem estimate_succ (p N r : PTm n) (hN : Γ ⊢[PRAAx] le two N)
    (ih : Γ ⊢[PRAAx] estimate p N r) : Γ ⊢[PRAAx] estimate p N (succ r) := by
  let M := N+r
  let A := numerator p M one
  let B := denominator p M one
  let C := numerator p N r
  let D := denominator p N r
  let A' := numerator p N (succ r)
  let B' := denominator p N (succ r)
  have hM := le_trans hN (le_add_right N r)
  have h1 := le_trans (le_succ_self one) hN
  have hb : Γ ⊢[PRAAx] le one B := denominator_positive p M one (le_trans (le_succ_self one) hM)
  have hd : Γ ⊢[PRAAx] le one D := denominator_positive p N r h1
  have hn : Γ ⊢[PRAAx] le one B' := denominator_positive p N (succ r) h1
  have result := GaussianReconstructionRoots.distance_triangle (sample p (M+one)) (sample p M) (sample p N)
    A B C D hb hd (adjacent p M hM) ih
  have radius : Γ ⊢[PRAAx] le ((A*D+C*B)*B') (A'*(B*D)) := by
    apply le_of_eq_add (d := zero)
    unfold A B C D A' B' numerator denominator square gap M
    ipra_ring
  exact distance_congr (sample_congr (by unfold M; ipra_ring)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hb hd) hn radius result)

theorem finite_estimate (p N r : PTm n) (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx] estimate p N r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift N) := by simpa [Fm.shift,Syn.shift,two,one] using hN.shift
  have h1 := le_trans (le_succ_self one) hN
  have all : Γ ⊢[PRAAx] .all (estimate (Syn.shift p) (Syn.shift N) (var 0)) := by
    ipra_qfind (by simp [estimate,distanceBounded,GaussianRationalMetric.bounded,RationalArgmin.rationalLE,le_QF]) [subst_estimate]
    · exact estimate_zero p N h1
    · exact estimate_succ (Syn.shift p) (Syn.shift N) (var 0) hs.wk Prf.hyp0
  ipra_simpa_inst [subst_estimate] using all.allE r

theorem uniform_interval (p N r : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] distanceBounded (sample p (N+r)) (sample p N)
      (two*unit p+two*r*square N) (square N*unit p) := by
  have h1 := le_trans (le_succ_self one) hN
  refine distance_radius_mono _ _ _ _ _ _ (denominator_positive p N r h1)
    (positive_product _ _ (square_positive _ h1) (unit_positive p)) ?_ (finite_estimate p N r hN)
  apply le_of_eq_add (d := two*square N*square N*unit p*unit p)
  unfold numerator denominator square gap
  ipra_ring

theorem actual_Glaisher_logarithm_finite_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le two (var 1) ⟶ estimate (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (finite_estimate _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherInterval

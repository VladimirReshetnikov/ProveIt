import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasIntegerPeriod
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Certificates.GaussianDiscretePeriodicMetricCertificate

/-!
# Actual quotient observations on a translated refinement

Fine index k evaluates the original quotient at 1 + translation + k/divisor.
Euclidean division writes the unwrapped argument as an integer translate
of its residue. The candidate's Gamma recurrence then supplies the wrap error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementWrap

open_ipra
open GaussianBarnesVignerasIntegerPeriod (advance data nameF period_at source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalMetric (distanceBounded)
open SignedDiscreteDerivativeOperators (width divisor subst_width subst_divisor)
open GaussianDiscretePeriodicGridReadback (sample)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- Fields after width, divisor, and lattice scale in the refinement data. -/
def translation (x : PTm n) : PTm n := fstT (sndT (sndT (sndT x)))
def observationClock (x : PTm n) : PTm n := fstT (sndT (sndT (sndT (sndT x))))

def numerator (x k : PTm n) : PTm n := advance (divisor x+k) (divisor x) (translation x)

def body (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 (nameF f) (observationClock (var 1)) (data t (numerator (var 1) (var 0)) (divisor (var 1)))

def orbits (f : PR 2) (t : PTm 2) (x N : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    source f t (numerator (Syn.shift x) (var 0*width (Syn.shift x))) (divisor (Syn.shift x)))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (x k : PTm n) :
    Syn.subst σ (numerator x k) = numerator (Syn.subst σ x) (Syn.subst σ k) := by
  simp [numerator,translation]

@[simp] theorem subst_observationClock {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (observationClock x) = observationClock (Syn.subst σ x) := by simp [observationClock]

theorem sample_at (f : PR 2) (t : PTm 2) (x k : PTm n) : inst2 (body f t) k x =
    ap2 (nameF f) (observationClock x) (data t (numerator x k) (divisor x)) := by
  simp only [body,inst2,subst_ap2,subst_observationClock,GaussianBarnesVignerasIntegerPeriod.subst_data,
    subst_numerator,subst_divisor,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem orbit_at (f : PR 2) (t : PTm 2) (x N i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i N) (hs : Γ ⊢[PRAAx] orbits f t x N) :
    Γ ⊢[PRAAx] source f t (numerator x (i*width x)) (divisor x) := by
  have spec : Γ ⊢[PRAAx] lt i N ⟶ source f t (numerator x (i*width x)) (divisor x) := by
    simpa only [orbits,Fm.subst_imp,subst_lt,GaussianBarnesVignerasIntegerPeriod.subst_source,
      subst_numerator,subst_divisor,subst_width,LeanProofs.IPRA.PTm.subst_mul,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using hs.allE i
  exact spec.impE hi

theorem unwrapped_numerator (x N j : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) :
    Γ ⊢[PRAAx] numerator x (j*width x) ≐ advance (numerator x (rem j N*width x)) (divisor x) (quo j N) := by
  have div := (DyadicComplexLogarithm.positive_division j N hN).andE₁
  unfold numerator advance
  ipra_lc natEq (congrMul div (.eqRefl (width x))) - 𝔞(quo j N)*natEq hD

private theorem late_radius (a b p r : PTm n) (hp : Γ ⊢[PRAAx] le (succ p) r)
    (h : Γ ⊢[PRAAx] distanceBounded a b two (unit r)) : Γ ⊢[PRAAx] distanceBounded a b one (unit p) := by
  have hm : Γ ⊢[PRAAx] le (unit (succ p)) (unit r) := GaussianBalancedRadiusArithmetic.unit_monotone _ _ hp
  have hu : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
  apply distance_radius_mono _ _ _ _ _ _ (unit_positive r) (unit_positive p) _ h
  exact le_congr hu (one_mul _).eqSymm hm

theorem node (f : PR 2) (t : PTm 2) (x N p j k : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hp : Γ ⊢[PRAAx] le (succ p) (observationClock x)) (hk : Γ ⊢[PRAAx] k ≐ j*width x)
    (horbit : Γ ⊢[PRAAx] orbits f t x N) : Γ ⊢[PRAAx]
    distanceBounded (sample (body f t) x (rem j N)) (inst2 (body f t) k x) one (unit p) := by
  let a := numerator x (rem j N*width x)
  let b := divisor x
  let r := observationClock x
  let c := advance a b (quo j N)
  have e : Γ ⊢[PRAAx] numerator x k ≐ c := by
    have eq : Γ ⊢[PRAAx] numerator x k ≐ numerator x (j*width x) := by
      ipra_congr (numerator (var 0) (var 1) : PTm 2) with [.eqRefl x,hk]
    exact eq.eqTrans (unwrapped_numerator x N j hN hD)
  have hrem := (DyadicComplexLogarithm.positive_division j N hN).andE₂
  have h := period_at f t a b (quo j N) (orbit_at f t x N (rem j N) hrem horbit)
  have cmp := diagonal_at _ _ _ _ r (cross_to_diagonal _ _ _ _ h)
  have close := late_radius _ _ p r hp (distance_symmetric _ _ _ _ (unit_positive r) cmp)
  have read : Γ ⊢[PRAAx] ap2 (nameF f) r (data t c b) ≐ inst2 (body f t) k x := by
    rw [sample_at]
    ipra_congr (ap2 (nameF f) (var 0) (data t (var 1) (var 2)) : PTm 3) with [.eqRefl r,e.eqSymm,.eqRefl b]
  rw [sample,sample_at]
  exact distance_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _) close

theorem stencil (f : PR 2) (t : PTm 2) (x N p i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hp : Γ ⊢[PRAAx] le (succ p) (observationClock x))
    (horbit : Γ ⊢[PRAAx] orbits f t x N) : Γ ⊢[PRAAx]
    GaussianDiscretePeriodicMetricCertificate.wrapping (body f t) x N i (unit p) := by
  let M := width x
  have atNode (j k : PTm n) (e : Γ ⊢[PRAAx] k ≐ j*M) :
      Γ ⊢[PRAAx] GaussianDiscretePeriodicMetricCertificate.node (body f t) x N (unit p) j k :=
    node f t x N p j k hN hD hp e horbit
  exact .andI (atNode i (i*M) (.eqRefl _))
    (.andI (atNode (succ i) (i*M+M) (by ipra_ring))
      (.andI (atNode (succ (succ i)) (i*M+M+M) (by ipra_ring))
        (atNode (succ (succ (succ i))) (i*M+M+M+M) (by ipra_ring))))

theorem actual_Barnes_refinement_quotient_wrap_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let p := var 2
       let i := var 3
       le one N ⟶ divisor x ≐ N*width x ⟶ le (succ p) (observationClock x) ⟶ orbits f t x N ⟶
         GaussianDiscretePeriodicMetricCertificate.wrapping (body f t) x N i (unit p)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (stencil f t _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementWrap

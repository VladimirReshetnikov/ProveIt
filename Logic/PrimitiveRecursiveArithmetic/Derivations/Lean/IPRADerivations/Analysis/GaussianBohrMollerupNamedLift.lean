import IPRADerivations.Analysis.GaussianBohrMollerupNamedFrozen

/-!
# Cofinal positive real Bohr–Mollerup lift

The lifted program evaluates the given rational presentation on a certified
late observation of the actual input. An extra output bit pays for comparing
two charts of the same frozen rational. The original named log-Gamma input
clock is sufficient by literal rational uniqueness.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedLift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupNamedFrozen (source rationalData native_source frozen_cross)
open GaussianBohrMollerupPresentation (Presentation laws)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeF" => GaussianLogGammaEulerNamed.nameF
local notation "nativeMap" => GaussianLogGammaEulerNamed.rationalMap
local notation "cofinalF" => GaussianLogGammaEulerCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerNamed.rationalData

def clock (p A R : PTm n) : PTm n :=
  GaussianNamedRightHalfPlaneLift.clock nativeMap (succ p) A R

def sample (P : Presentation) (f : PR 2) (p x A R : PTm n) : PTm n :=
  ap2 P.nameF (succ (succ p)) (rationalData P f (clock p A R) x)

abbrev data (x A R : PTm n) : PTm n := GaussianLogGammaEulerNamed.data x A R

def nameF (P : Presentation) (f : PR 2) : PR 2 := PTm.toPR
  (sample P f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p A R : PTm n) :
    Syn.subst σ (clock p A R) = clock (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [clock]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (f : PR 2) (p x A R : PTm n) :
    Syn.subst σ (sample P f p x A R) = sample P f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [sample]

theorem sample_at (P : Presentation) (f : PR 2) (p x A R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF P f) p (data x A R) ≐ sample P f p x A R := by
  let X := data x A R
  have raw : Γ ⊢[PRAAx] ap2 (nameF P f) p X ≐ sample P f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF, ap2] using
      toPR_eq (Γ := Γ) (sample P f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample P f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,A,R])
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

private theorem unit_step (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two * unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem delayed_observation (P : Presentation) (f : PR 2) (p x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF P f) p (data x A R)) (ap2 (nativeF f) (succ p) (data x A R))
      one (unit (succ p)) := by
  let k := clock p A R
  let r := succ (succ p)
  let y := rationalData P f k x
  let z := ap1 cofinalData (ap2 f k x)
  have he := frozen_cross P f k x A R hp hs (GaussianNamedRightHalfPlaneLift.clock_margin nativeMap (succ p) A R)
  have raw := cross_at P.nameF cofinalF y z r r he
  have hr := unit_positive (Γ := Γ) r
  have budget : Γ ⊢[PRAAx] le ((unit r+unit r)*unit (succ p)) (one*(unit r*unit r)) := by
    apply le_of_eq_add (d := zero)
    dsimp only [r]
    have step := natEq (unit_step (Γ := Γ) (succ p))
    apply deriveNat
    ipra_simps
    rw [step]
    ring
  have hx : Γ ⊢[PRAAx] ap2 (nameF P f) p (data x A R) ≐ ap2 P.nameF r y := sample_at P f p x A R
  have hy : Γ ⊢[PRAAx] ap2 (nativeF f) (succ p) (data x A R) ≐ ap2 cofinalF r z :=
    GaussianNamedRightHalfPlaneLift.sample_at nativeMap f (succ p) x A R
  exact distance_congr hx.eqSymm hy.eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hr hr) (unit_positive _) budget raw)

theorem observation (P : Presentation) (f : PR 2) (p q x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF P f) p (data x A R)) (ap2 (nativeF f) q (data x A R))
      (unit p+unit q) (unit p*unit q) := by
  let W := unit (succ p)
  let V := unit q
  let X := data x A R
  let a := ap2 (nameF P f) p X
  let b := ap2 (nativeF f) (succ p) X
  let c := ap2 (nativeF f) q X
  have hW : Γ ⊢[PRAAx] le one W := unit_positive _
  have hV : Γ ⊢[PRAAx] le one V := unit_positive _
  have hD := positive_product W V hW hV
  have hC := positive_product (unit p) V (unit_positive p) hV
  have hn := GaussianLogGammaEulerNamed.name_regular f x A R (native_source f x A R hs)
  have near : Γ ⊢[PRAAx] distanceBounded a b V (W*V) :=
    distance_radius_mono _ _ one W V (W*V) hW hD (le_of_eq_add (d := zero) (by ipra_ring))
      (delayed_observation P f p x A R hp hs)
  have far := cross_at (nativeF f) (nativeF f) X X (succ p) q (cross_refl (nativeF f) X hn)
  have budget : Γ ⊢[PRAAx] le ((V+(W+V))*(unit p*V)) ((unit p+V)*(W*V)) := by
    apply le_of_eq_add (d := zero)
    dsimp only [W]
    have step := natEq (unit_step (Γ := Γ) p)
    apply deriveNat
    ipra_simps
    rw [step]
    ring
  exact distance_radius_mono a c _ _ _ _ hD hC budget
    (distance_triangle_same a b c V (W+V) (W*V) hD near far)

theorem equivalent (P : Presentation) (f : PR 2) (x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF P f) (nativeF f) (data x A R) (data x A R) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hL : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] laws P := by
    simpa [Fm.shift, Syn.shift] using hp.shift.shift
  have hS : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh A) (sh R) := by
    simpa [Fm.shift, Syn.shift, sh] using hs.shift.shift
  simpa [crossEquivalent, sh, Syn.shift] using observation P f (var 1) (var 0) (sh x) (sh A) (sh R) hL hS

theorem name_regular (P : Presentation) (f : PR 2) (x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] pointCN (nameF P f) (data x A R) := by
  let X := data x A R
  have h := equivalent P f x A R hp hs
  exact cross_trans (nameF P f) (nativeF f) (nameF P f) X X X h (cross_symm (nameF P f) (nativeF f) X X h)

theorem late_rational_rate (P : Presentation) (f : PR 2) (s k x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (h : Γ ⊢[PRAAx] source f x A R)
    (hk : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlaneLift.clock nativeMap s A R) k) :
    Γ ⊢[PRAAx] independentRate (nameF P f) P.nameF (data x A R) (rationalData P f k x) one (unit s) := by
  have ht := GaussianNamedRightHalfPlaneLift.clock_margin (Γ := Γ) nativeMap s A R
  have hc := GaussianBohrMollerupNamedFrozen.frozen_source f k x A R h (le_trans ht hk)
  have hr := (GaussianBohrMollerupPresentation.observe_value P
    (GaussianGammaMinimumFreezeRational.numerator f k x) (GaussianGammaMinimumFreezeRational.denominator f k x)
    hp.andE₂.andE₁ hc.andE₁).andE₁
  exact GaussianNamedRateTransport.transport (nativeF f) P.nameF (nameF P f) P.nameF
    (data x A R) (rationalData P f k x) (data x A R) (rationalData P f k x) one (unit s)
    (unit_positive s) (GaussianBohrMollerupNamedFrozen.late_rational_rate P f s k x A R hp h hk)
    (equivalent P f x A R hp h) (cross_refl P.nameF (rationalData P f k x) hr)

theorem actual_named_Bohr_Mollerup_log_Gamma_closed (P : Presentation) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws P ⟶ source f (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF P f) (nativeF f) (data (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (equivalent P f _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedLift

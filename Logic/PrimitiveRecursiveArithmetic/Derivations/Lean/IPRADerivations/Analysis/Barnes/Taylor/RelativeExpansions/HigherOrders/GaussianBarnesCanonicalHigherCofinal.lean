import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.HigherOrders.GaussianBarnesCanonicalHigherTail
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogCofinalRate

import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareCofinal

/-!
# Cofinal names for all higher Barnes logarithmic coefficients

At each internally encoded order, choose the number of observations
from the corresponding inverse-square bound. These coefficients keep
the original logarithmic head boundary and the original retained rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherCofinal

open_ipra
open GaussianBarnesCanonicalHigherRows (coefficientGain)
open GaussianBarnesCanonicalHigherTail (value finite_gap)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev data (z R B j : PTm n) : PTm n := GaussianBarnesCanonicalHigherTail.data z B R j

def length (p j : PTm n) : PTm n := coefficientGain j*unit p

def sample (p z R B j : PTm n) : PTm n := value z B (initial R) j (length p j)

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (fstT (fstT (var 1))) (fstT (sndT (var 1))) (sndT (fstT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_length {m : ℕ} (σ : Fin n → PTm m) (p j : PTm n) :
    Syn.subst σ (length p j) = length (Syn.subst σ p) (Syn.subst σ j) := by simp [length]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B j : PTm n) :
    Syn.subst σ (sample p z R B j) =
      sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [sample]

theorem sample_at (p z R B j : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B j) ≐ sample p z R B j := by
  let x := data z R B j
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐
      sample p (fstT (fstT x)) (fstT (sndT x)) (sndT (fstT x)) (sndT (sndT x)) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (sample (var 0) (fstT (fstT (var 1))) (fstT (sndT (var 1)))
        (sndT (fstT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,x]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,fstT (fstT x),fstT (sndT x),sndT (fstT x),sndT (sndT x)]) (σ' := ![p,z,R,B,j]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

private theorem finite_gaps (z R B j : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianReciprocalSquareCofinal.finiteGaps GaussianBarnesCanonicalHigherTail.body
      (GaussianBarnesCanonicalHigherTail.data z B (initial R) j) (initial R) (coefficientGain j) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [Syn.shift, sh, GaussianBarnesCanonicalHigherTail.value,
    GaussianBarnesCanonicalHigherTail.subst_data, GaussianBarnesCanonicalLogSchedule.subst_initial,
    GaussianBarnesCanonicalHigherRows.subst_coefficientGain] using
    finite_gap (sh z) (sh R) (sh B) (initial (sh R)) (sh j) (var 1) (var 0) (initial_source _ _ _ h')

theorem late_prefix_error (p z R B j r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (length p j) r) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) j r) (sample p z R B j) one (unit p) :=
  GaussianReciprocalSquareCofinal.late_prefix_error _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B j h) hr

theorem prefix_error (p z R B j r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B j) (value z B (initial R) j r)
      (coefficientGain j*unit p+(initial R+r)) ((initial R+r)*unit p) :=
  GaussianReciprocalSquareCofinal.prefix_error _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B j h)

theorem observations (p q z R B j : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B j) (sample q z R B j) (unit p+unit q) (unit p*unit q) :=
  GaussianReciprocalSquareCofinal.observations _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B j h)

theorem regular (z R B j : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B j) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,data,GaussianBarnesCanonicalHigherTail.subst_data,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    distance_congr (sample_at (var 1) (sh z) (sh R) (sh B) (sh j)).eqSymm
      (sample_at (var 0) (sh z) (sh R) (sh B) (sh j)).eqSymm (.eqRefl _) (.eqRefl _)
      (observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh j) h')

theorem actual_Barnes_all_higher_coefficients_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherCofinal

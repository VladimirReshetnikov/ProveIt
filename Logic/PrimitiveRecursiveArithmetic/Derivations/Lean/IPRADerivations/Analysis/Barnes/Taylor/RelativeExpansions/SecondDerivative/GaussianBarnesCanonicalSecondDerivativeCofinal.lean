import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.SecondDerivative.GaussianBarnesCanonicalSecondDerivativeTail
import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogCofinalRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate

import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareCofinal

/-!
# Cofinal name for the Barnes second-derivative expressions

Starting at the original logarithmic head boundary, take exactly
`12R * 2^p` rational rows for an observation at precision `p`.
The finite reciprocal-square estimate proves regularity and provides
a rate against every finite prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeCofinal

open_ipra
open GaussianBarnesCanonicalSecondDerivativeRow (boundNumerator)
open GaussianBarnesCanonicalSecondDerivativeTail (value finite_gap)
open GaussianBarnesCanonicalLogCofinal (source data subst_data)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def length (p R : PTm n) : PTm n := boundNumerator R*unit p

def sample (p z R B : PTm n) : PTm n := value z B (initial R) (length p R)

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_length {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (length p R) = length (Syn.subst σ p) (Syn.subst σ R) := by simp [length]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B : PTm n) :
    Syn.subst σ (sample p z R B) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [sample]

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ sample p z R B := by
  let x := data z R B
  have raw : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ) (sample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,x]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![p,z,R,B]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

private theorem finite_gaps (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianReciprocalSquareCofinal.finiteGaps GaussianBarnesCanonicalSecondDerivativeTail.body
      (GaussianBarnesCanonicalSecondDerivativeTail.data z B (initial R)) (initial R) (boundNumerator R) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [Syn.shift, sh, GaussianBarnesCanonicalSecondDerivativeTail.value,
    GaussianBarnesCanonicalSecondDerivativeTail.subst_data, GaussianBarnesCanonicalLogSchedule.subst_initial,
    GaussianBarnesCanonicalSecondDerivativeRow.subst_boundNumerator] using
    finite_gap (sh z) (sh R) (sh B) (initial (sh R)) (var 1) (var 0) (initial_source _ _ _ h')

theorem late_prefix_error (p z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) r) (sample p z R B) one (unit p) :=
  GaussianReciprocalSquareCofinal.late_prefix_error _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B h) hr

theorem prefix_error (p z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (value z B (initial R) r)
      (boundNumerator R*unit p+(initial R+r)) ((initial R+r)*unit p) :=
  GaussianReciprocalSquareCofinal.prefix_error _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B h)

theorem observations (p q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (sample q z R B) (unit p+unit q) (unit p*unit q) :=
  GaussianReciprocalSquareCofinal.observations _ _ _ _ _ _ (initial_positive R) (finite_gaps z R B h)

theorem regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    distance_congr (sample_at (var 1) (sh z) (sh R) (sh B)).eqSymm
      (sample_at (var 0) (sh z) (sh R) (sh B)).eqSymm (.eqRefl _) (.eqRefl _)
      (observations (var 1) (var 0) (sh z) (sh R) (sh B) h')

theorem sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ap2 nameF p (data z R B)) (boundNumerator R) one := by
  let N := initial R
  let C := boundNumerator R
  have hN := initial_positive (Γ := Γ) R
  have raw := GaussianBarnesCanonicalSecondDerivativeTail.tail_bound z R B N (length p R) (initial_source z R B h)
  have widened := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hN (le_refl one)
    (le_congr (mul_comm one C) (mul_comm N C) (mul_le_mul_right C hN)) raw
  exact GaussianRationalReciprocal.bound_congr (sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem samples_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound nameF (data z R B) (boundNumerator R) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,subst_data,
    GaussianBarnesCanonicalSecondDerivativeRow.subst_boundNumerator] using sample_bound (var 0) (sh z) (sh R) (sh B) hs

theorem actual_cofinal_Barnes_second_derivative_expressions_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalSecondDerivativeCofinal

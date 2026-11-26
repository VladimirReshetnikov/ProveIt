import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHigherTail
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalLogCofinalRate

/-!
# Cofinal names for all higher Barnes logarithmic coefficients

At each internally encoded order, choose the number of observations
from the corresponding inverse-square bound. These coefficients keep
the original logarithmic head boundary and the original retained rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHigherCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalHigherRows (coefficientGain)
open GaussianBarnesCanonicalHigherTail (value finite_gap)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

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

private theorem ordered_finite_gap (z R B j a b : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) j b) (value z B (initial R) j a)
      (coefficientGain j) (initial R+a) := by
  let N := initial R
  let c := monus b a
  have read : Γ ⊢[PRAAx] value z B N j (a+c) ≐ value z B N j b := by
    ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [.eqRefl _, .eqRefl _, .eqRefl _, .eqRefl _, (eq_add_of_le hab).eqSymm]
  exact distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_gap z R B N j a c (initial_source z R B h))

theorem late_prefix_error (p z R B j r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (length p j) r) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) j r) (sample p z R B j) one (unit p) := by
  let K := initial R+length p j
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have fit : Γ ⊢[PRAAx] le (coefficientGain j*unit p) (one*K) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_add_left _ _)
  exact distance_radius_mono _ _ _ _ _ _ hK (unit_positive p) fit (ordered_finite_gap z R B j (length p j) r h hr)

theorem prefix_error (p z R B j r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B j) (value z B (initial R) j r)
      (coefficientGain j*unit p+(initial R+r)) ((initial R+r)*unit p) := by
  let U := unit p
  let K := initial R+r
  let C := coefficientGain j
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hk : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have hkU := positive_product K U hk hu
  refine (le_total r (length p j)).orE ?_ ?_
  · let Δ := le r (length p j) :: Γ
    have d := ordered_finite_gap z R B j r (length p j) h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (C*(K*U)) ((C*U+K)*K) := le_of_eq_add (d := K*K) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hk.wk hkU.wk fit d
  · let Δ := le (length p j) r :: Γ
    have d := late_prefix_error p z R B j r h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (one*(K*U)) ((C*U+K)*U) := le_of_eq_add (d := C*U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hkU.wk fit (distance_symmetric _ _ _ _ hu.wk d)

theorem observations (p q z R B j : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B j) (sample q z R B j) (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let C := coefficientGain j
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hv : Γ ⊢[PRAAx] le one V := unit_positive q
  have hD := positive_product U V hu hv
  refine (le_total p q).orE ?_ ?_
  · let Δ := le p q :: Γ
    have pq : Δ ⊢[PRAAx] le p q := Prf.hyp0
    have lengths := le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone pq)
    have d := late_prefix_error p z R B j (length q j) h.wk lengths
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*U) := le_of_eq_add (d := U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hD.wk budget (distance_symmetric _ _ _ _ hu.wk d)
  · let Δ := le q p :: Γ
    have qp : Δ ⊢[PRAAx] le q p := Prf.hyp0
    have lengths := le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone qp)
    have d := late_prefix_error q z R B j (length p j) h.wk lengths
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*V) := le_of_eq_add (d := V*V) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hv.wk hD.wk budget d

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

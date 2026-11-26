import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalDerivativeTail
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalLogCofinalRate

/-!
# Cofinal name for the Barnes first-derivative expressions

Starting at the original logarithmic head boundary, take exactly
`2R² * 2^p` rational rows for an observation at precision `p`.
The finite reciprocal-square estimate proves regularity and provides
a rate against every finite prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalDerivativeRow (boundNumerator)
open GaussianBarnesCanonicalDerivativeTail (value finite_gap)
open GaussianBarnesCanonicalLogCofinal (source data subst_data)
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

private theorem ordered_finite_gap (z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) b) (value z B (initial R) a)
      (boundNumerator R) (initial R+a) := by
  let N := initial R
  let c := monus b a
  have read : Γ ⊢[PRAAx] value z B N (a+c) ≐ value z B N b := by
    ipra_congr (value (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl _, .eqRefl _, .eqRefl _, (eq_add_of_le hab).eqSymm]
  exact distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (finite_gap z R B N a c (initial_source z R B h))

theorem late_prefix_error (p z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hr : Γ ⊢[PRAAx] le (length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (value z B (initial R) r) (sample p z R B) one (unit p) := by
  let K := initial R+length p R
  have hK : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have fit : Γ ⊢[PRAAx] le (boundNumerator R*unit p) (one*K) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_add_left _ _)
  exact distance_radius_mono _ _ _ _ _ _ hK (unit_positive p) fit (ordered_finite_gap z R B (length p R) r h hr)

theorem prefix_error (p z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (value z B (initial R) r)
      (boundNumerator R*unit p+(initial R+r)) ((initial R+r)*unit p) := by
  let U := unit p
  let K := initial R+r
  let C := boundNumerator R
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hk : Γ ⊢[PRAAx] le one K := le_trans (initial_positive R) (le_add_right _ _)
  have hkU := positive_product K U hk hu
  refine (le_total r (length p R)).orE ?_ ?_
  · let Δ := le r (length p R) :: Γ
    have d := ordered_finite_gap z R B r (length p R) h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (C*(K*U)) ((C*U+K)*K) := le_of_eq_add (d := K*K) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hk.wk hkU.wk fit d
  · let Δ := le (length p R) r :: Γ
    have d := late_prefix_error p z R B r h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (one*(K*U)) ((C*U+K)*U) := le_of_eq_add (d := C*U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hkU.wk fit (distance_symmetric _ _ _ _ hu.wk d)

theorem observations (p q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B) (sample q z R B) (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let C := boundNumerator R
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hv : Γ ⊢[PRAAx] le one V := unit_positive q
  have hD := positive_product U V hu hv
  refine (le_total p q).orE ?_ ?_
  · let Δ := le p q :: Γ
    have pq : Δ ⊢[PRAAx] le p q := Prf.hyp0
    have lengths := le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone pq)
    have d := late_prefix_error p z R B (length q R) h.wk lengths
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*U) := le_of_eq_add (d := U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hD.wk budget (distance_symmetric _ _ _ _ hu.wk d)
  · let Δ := le q p :: Γ
    have qp : Δ ⊢[PRAAx] le q p := Prf.hyp0
    have lengths := le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone qp)
    have d := late_prefix_error q z R B (length p R) h.wk lengths
    have budget : Δ ⊢[PRAAx] le (one*(U*V)) ((U+V)*V) := le_of_eq_add (d := V*V) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hv.wk hD.wk budget d

theorem regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [pointCN,Syn.shift,sh,subst_data,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    distance_congr (sample_at (var 1) (sh z) (sh R) (sh B)).eqSymm
      (sample_at (var 0) (sh z) (sh R) (sh B)).eqSymm (.eqRefl _) (.eqRefl _)
      (observations (var 1) (var 0) (sh z) (sh R) (sh B) h')

theorem actual_cofinal_Barnes_first_derivative_expressions_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeCofinal

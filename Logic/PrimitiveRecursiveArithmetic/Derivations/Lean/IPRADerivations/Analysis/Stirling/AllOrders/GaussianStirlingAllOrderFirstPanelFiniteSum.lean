import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelName
import IPRADerivations.Analysis.Stirling.GaussianStirlingTelescopeName

/-!
# Finite sums of the actual first-order periodic panels

Each summand is the regular name sampled from its own certified harmonic
subdivision. The normalized finite sum is cross-equivalent to the actual
Stirling telescope on every runtime-bounded cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelFiniteSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianValueNormalizerExtensionality (rawDiagonal normalized_names_equivalent)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianStirlingNames (source)
open GaussianStirlingTelescope (dBody rawSum sampleData d_at)
open GaussianStirlingTelescopeName (rawData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "panelF" => GaussianStirlingAllOrderFirstPanelName.nameF
local notation "panelData" => GaussianStirlingAllOrderFirstPanelName.data
local notation "qsum" => GaussianRationalFiniteSum.sum
local notation "T" => GaussianStirlingTelescopeName.nameF

def row (p A B k : PTm n) : PTm n := ap2 panelF p (panelData A B k)
def rowBody : PTm 2 :=
  let d := var 1
  row (fstT d) (fstT (sndT d)) (sndT (sndT d)) (var 0)

@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (p A B k : PTm n) :
    Syn.subst σ (row p A B k) = row (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [row]

theorem row_at (p A B k : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody k (sampleData p A B) ≐ row p A B k := by
  let d := sampleData p A B
  have ea : Γ ⊢[PRAAx] fstT d ≐ p := fst_pair _ _
  have eb : Γ ⊢[PRAAx] sndT d ≐ pairT A B := snd_pair _ _
  have h := Prf.eqCongr (Γ := Γ) (row (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT d,fstT (sndT d),sndT (sndT d),k]) (σ' := ![p,A,B,k]) (fun i => by
      fin_cases i
      exact ea
      exact (congrFst eb).eqTrans (fst_pair _ _)
      exact (congrSnd eb).eqTrans (snd_pair _ _)
      exact .eqRefl _)
  simpa [d,rowBody,inst2] using h

def raw (p N A B : PTm n) : PTm n := qsum rowBody N (sampleData p A B)
def rawF : PR 2 := PTm.toPR (raw (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))))
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (N A B : PTm n) : PTm n := GaussianFastValueCut.nameData N (rawData N A B)

@[simp] theorem subst_raw {l : ℕ} (σ : Fin n → PTm l) (p N A B : PTm n) :
    Syn.subst σ (raw p N A B) = raw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by simp [raw]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (N A B : PTm n) :
    Syn.subst σ (data N A B) = data (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by simp [data]

theorem raw_at (p N A B : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData N A B) ≐ raw p N A B := by
  let x := rawData N A B
  have r : Γ ⊢[PRAAx] ap2 rawF p x ≐ raw p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa [rawF,ap2] using toPR_eq (Γ := Γ)
      (raw (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,x]
  have v : Γ ⊢[PRAAx] sndT x ≐ pairT A B := snd_pair _ _
  exact r.eqTrans (by
    simpa using Prf.eqCongr (Γ := Γ) (raw (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![p,N,A,B]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact fst_pair _ _
        exact (congrFst v).eqTrans (fst_pair _ _)
        exact (congrSnd v).eqTrans (snd_pair _ _)))

private theorem rows (p q N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] termsDistance rowBody dBody N (sampleData p A B) (sampleData q A B) (unit p+unit q) (unit p*unit q) := by
  refine .allI (.impI ?_)
  let a := Syn.shift A
  let b := Syn.shift B
  let s := Syn.shift p
  let t := Syn.shift q
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Fm.shift,Syn.shift,Δ] using h.shift.wk
  have r := GaussianStirlingAllOrderFirstPanelName.point_cross a b i s t hs.andE₁ hs.andE₂
  simpa [termsDistance,Syn.shift,Δ,a,b,s,t,i,GaussianStirlingTelescope.shifted] using
    distance_congr (row_at s a b i).eqSymm (d_at t a b i).eqSymm (.eqRefl _) (.eqRefl _) r

theorem distance_to_telescope (p q N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (raw p N A B) (rawSum q N A B) (N*(unit p+unit q)) (unit p*unit q) :=
  sum_distance rowBody dBody N (sampleData p A B) (sampleData q A B) (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (rows p q N A B h)

private theorem own_rows (p q N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] termsDistance rowBody rowBody N (sampleData p A B) (sampleData q A B) (unit p+unit q) (unit p*unit q) := by
  refine .allI (.impI ?_)
  let a := Syn.shift A
  let b := Syn.shift B
  let s := Syn.shift p
  let t := Syn.shift q
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Fm.shift,Syn.shift,Δ] using h.shift.wk
  have r := GaussianStirlingAllOrderFirstPanelName.point_regular a b i s t hs.andE₁ hs.andE₂
  simpa [termsDistance,Syn.shift,Δ,a,b,s,t,i] using
    distance_congr (row_at s a b i).eqSymm (row_at t a b i).eqSymm (.eqRefl _) (.eqRefl _) r

theorem raw_regular (N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF N (rawData N A B) := by
  refine .allI (.allI ?_)
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let j := Syn.shift (Syn.shift N)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Fm.shift,Syn.shift,Δ] using h.shift.shift
  have hd := sum_distance (Γ := Δ) rowBody rowBody j (sampleData (var 1) a b) (sampleData (var 0) a b)
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))
    (positive_product _ _ (unit_positive _) (unit_positive _)) (own_rows (var 1) (var 0) j a b hs)
  simpa [GaussianFastValueCut.regular,Syn.shift,Δ,a,b,j,raw,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (raw_at (var 1) j a b).eqSymm (raw_at (var 0) j a b).eqSymm (.eqRefl _) (.eqRefl _) hd

theorem name_regular (N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN nameF (data N A B) :=
  GaussianFastValueCut.name_fast rawF N _ (raw_regular N A B h)

theorem telescope_cross (N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent nameF T (data N A B) (GaussianStirlingTelescopeName.data N A B) := by
  let g := GaussianStirlingTelescopeName.rawF
  let w := rawData N A B
  have hr := raw_regular N A B h
  have hg := GaussianStirlingTelescopeName.raw_regular N A B h
  have hd : Γ ⊢[PRAAx] rawDiagonal rawF g w w (two*N) := by
    refine .allI ?_
    let a := Syn.shift A
    let b := Syn.shift B
    let j := Syn.shift N
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source a b := by simpa [a,b,Fm.shift,Syn.shift,Δ] using h.shift
    have e := distance_to_telescope (var 0) (var 0) j a b hs
    have k := distance_congr (raw_at (var 0) j a b).eqSymm
      (GaussianStirlingTelescopeName.raw_at (var 0) j a b).eqSymm (.eqRefl _) (.eqRefl _) e
    let u := unit (var 0 : PTm (n+1))
    have den := positive_product (Γ := Δ) _ _ (unit_positive (var 0)) (unit_positive (var 0))
    have out := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (two*j) u den
      (unit_positive _) (by ipra_le 0) k
    simpa [rawDiagonal,g,w,a,b,j,Δ,u,Syn.shift,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using out
  exact normalized_names_equivalent rawF g N N w w (two*N) hr hg hd

theorem endpoint_cross (N A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent nameF
      (GaussianNamedDifference.nameF GaussianStirlingNames.nameF GaussianStirlingNames.nameF)
      (data N A B) (GaussianStirlingTelescopeName.endpointData N A B) :=
  cross_trans _ _ _ _ _ _ (telescope_cross N A B h) (GaussianStirlingTelescopeName.telescope_cross N A B h)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelFiniteSum

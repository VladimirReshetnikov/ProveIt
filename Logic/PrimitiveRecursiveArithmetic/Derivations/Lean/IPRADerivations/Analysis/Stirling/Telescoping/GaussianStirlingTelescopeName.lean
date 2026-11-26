import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingTelescope
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRecurrence

/-!
# A normalized name for the finite Stirling telescope

The program computes the literal finite sum of the original Stirling
difference samples with a length-dependent observation clock. The
checked rational recurrence identifies its value with the named
difference of the original (A) endpoints.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingTelescopeName

open_ipra
open GaussianStirlingNames (source)
open GaussianStirlingTelescope (shifted shifted_source rawSum endpoint sampleData dBody d_at
  localRows rows_from_recurrence independent_error diagonal_error errorNumerator errorDenominator)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianFastValueCut (regular)
open GaussianValueNormalizerExtensionality (rawDiagonal)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "A" => GaussianStirlingNames.nameF
local notation "D" => GaussianStirlingDifference.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def rawData (N a b : PTm n) : PTm n := pairT N (pairT a b)
def rawBody : PTm 2 := rawSum (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def rawF : PR 2 := PTm.toPR rawBody
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (N a b : PTm n) : PTm n := GaussianFastValueCut.nameData N (rawData N a b)
def endpointData (N a b : PTm n) : PTm n :=
  GaussianNamedDifference.data (GaussianStirlingNames.nameData a b) (GaussianStirlingNames.nameData (shifted a b N) b)

ipra_subst rawData
ipra_subst data
ipra_subst endpointData

theorem raw_at (p N a b : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData N a b) ≐ rawSum p N a b := by
  let x := rawData N a b
  have read : Γ ⊢[PRAAx] ap2 rawF p x ≐ rawSum p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa [rawF,rawBody,ap2] using toPR_eq (Γ := Γ) rawBody ![p,x]
  have p₂ : Γ ⊢[PRAAx] sndT x ≐ pairT a b := snd_pair _ _
  have bind : Γ ⊢[PRAAx] rawSum p (fstT x) (fstT (sndT x)) (sndT (sndT x)) ≐ rawSum p N a b := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawSum (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![p,N,a,b]) (fun j => by
        fin_cases j
        · exact .eqRefl _
        · exact fst_pair _ _
        · exact p₂.fstE
        · exact p₂.sndE)
  exact read.eqTrans bind

private theorem raw_rows (p q N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] termsDistance dBody dBody N (sampleData p a b) (sampleData q a b) (unit p+unit q) (unit p*unit q) := by
  refine .allI (.impI ?_)
  let X := Syn.shift a
  let Y := Syn.shift b
  let P := Syn.shift p
  let Q := Syn.shift q
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift N) :: Γ.map Fm.shift
  let t := shifted X Y i
  have h : Δ ⊢[PRAAx] source X Y := by simpa [Fm.shift,Syn.shift,Δ,X,Y] using hs.shift.wk
  have g := shifted_source X Y i h
  have regularD := GaussianStirlingDifference.name_regular t Y g.andE₁ g.andE₂
  have d := point_at D (GaussianStirlingDifference.data t Y) P Q regularD
  simpa [termsDistance,Syn.shift,Δ,X,Y,P,Q,i] using
    distance_congr (d_at P X Y i).eqSymm (d_at Q X Y i).eqSymm (.eqRefl _) (.eqRefl _) d

theorem raw_distance (p q N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (rawSum p N a b) (rawSum q N a b) (N*(unit p+unit q)) (unit p*unit q) :=
  sum_distance dBody dBody N (sampleData p a b) (sampleData q a b) (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (raw_rows p q N a b hs)

theorem raw_regular (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] regular rawF N (rawData N a b) := by
  refine .allI (.allI ?_)
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift.shift
  simpa [regular,Syn.shift,sh,Δ] using
    distance_congr (raw_at (Γ := Δ) (var 1) (sh N) (sh a) (sh b)).eqSymm (raw_at (var 0) (sh N) (sh a) (sh b)).eqSymm
      (.eqRefl _) (.eqRefl _) (raw_distance (var 1) (var 0) (sh N) (sh a) (sh b) h)

theorem name_regular (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data N a b) :=
  GaussianFastValueCut.name_fast rawF N (rawData N a b) (raw_regular N a b hs)

theorem name_at (p N a b : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data N a b) ≐
    rawSum (GaussianFastValueCut.exponent N p) N a b := by
  let q := GaussianFastValueCut.exponent N p
  exact (GaussianFastValueCut.name_at rawF N (rawData N a b) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at q N a b)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem endpoint_regular (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN G (endpointData N a b) :=
  GaussianNamedDifference.name_regular A A _ _ (GaussianStirlingNames.name_regular a b hs)
    (GaussianStirlingNames.name_regular (shifted a b N) b (shifted_source a b N hs))

theorem rows (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] localRows N a b :=
  rows_from_recurrence N a b hs (fun u v h => GaussianStirlingRecurrence.recurrence u v h)

theorem endpoint_error (p q N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (rawSum p N a b) (endpoint q N a b)
      (N*errorNumerator p q) (errorDenominator p q) :=
  independent_error p q N a b hs (rows N a b hs)

theorem named_diagonal_error (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data N a b)) (ap2 G p (endpointData N a b))
      (num 9*N+num 7) (unit p) := by
  let u := unit p
  have hu := unit_positive (Γ := Γ) p
  have first := distance_congr (.eqRefl _) (raw_at p N a b) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.normalized_to_sample rawF N (rawData N a b) p (raw_regular N a b hs))
  have second := diagonal_error p N a b hs (rows N a b hs)
  have last := GaussianNamedDifference.sample_error A A (GaussianStirlingNames.nameData a b)
    (GaussianStirlingNames.nameData (shifted a b N) b) p (GaussianStirlingNames.name_regular a b hs)
    (GaussianStirlingNames.name_regular _ _ (shifted_source a b N hs))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ u hu (distance_triangle_same _ _ _ _ _ u hu first second)
      (distance_symmetric _ _ _ _ hu last))

theorem telescope_cross (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF G (data N a b) (endpointData N a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 9*N+num 7)
    (name_regular N a b hs) (endpoint_regular N a b hs)
  refine .allI ?_
  let X := Syn.shift a
  let Y := Syn.shift b
  let J := Syn.shift N
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source X Y := by simpa [Fm.shift,Syn.shift,Δ,X,Y] using hs.shift
  simpa [rawDiagonal,Syn.shift,Δ,X,Y,J] using named_diagonal_error (var 0) J X Y h

theorem actual_Stirling_named_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 0) ⟶ crossEquivalent nameF G (data (var 2) (var 1) (var 0)) (endpointData (var 2) (var 1) (var 0))) :=
  closeUniv 3 (.impI (telescope_cross _ _ _ Prf.hyp0))

theorem actual_Stirling_telescope_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 0) ⟶
      distanceBounded (rawSum (var 4) (var 2) (var 1) (var 0)) (endpoint (var 3) (var 2) (var 1) (var 0))
        (var 2*errorNumerator (var 4) (var 3)) (errorDenominator (var 4) (var 3))) :=
  closeUniv 5 (.impI (endpoint_error _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingTelescopeName

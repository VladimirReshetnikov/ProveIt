import OAI.Combinatorics.Progressions.Probability.PositiveDensityRetained

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principal_mixed_comparison {D α V : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (t : Finset V)
    (c : PrincipalIntegerTuples B h α L → V → ℝ)
    (target : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℝ)
    (a : PrincipalIntegerTuples B h α L → V → ℂ)
    (b : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ)
    (φ : V → ℂ) {δ ε : ℝ}
    (hc : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ v ∈ t, 0 ≤ c y v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ t, ‖a y v-b (principalResidueLabel m y) v‖ ≤ δ)
    (hcoeff : ∀ r v, v ∈ t →
      |(principalResidueWeights B h L hL m hm r hsize).mean (fun y => c y v)-target r v| ≤ ε) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖p.complexMean (fun y => 𝔼 v ∈ t, (c y v : ℂ)*a y v*φ v) -
      (∑ r, 𝔼 v ∈ t, ((q.weight r*target r v : ℝ) : ℂ)*b r v*φ v)‖ ≤
        δ*p.mean (fun y => 𝔼 v ∈ t, c y v)+ε*q.mean (fun r => 𝔼 v ∈ t, ‖b r v‖) := by
  classical
  dsimp only
  apply mixed_residue_comparison _ (principalResidueLabel m) t c target a b φ hc hφ hspatial
  intro r v hv
  apply FiniteProbabilityWeights.fiberMean_condition_error
  intro hr
  simpa only [principalResidueWeights_eq_condition] using hcoeff r v hv

theorem principal_jointCoefficient_mixed_comparison {D α Q V : Type*}
    [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {X : Q → Type*} [∀ q, Countable (X q)] [∀ q, MeasurableSpace (X q)]
    [∀ q, MeasurableSingletonClass (X q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (p : PrincipalIntegerTuples B h α L → ∀ q, PMF (X q)) (S : Q → ℝ) (hS : ∀ q, 0 ≤ S q)
    (mask : (PrincipalTupleIndex B h → Option α → ZMod m) → ∀ q, X q → ℝ)
    (f : (PrincipalTupleIndex B h → Option α → ZMod m) →
      (JointBlockParameter B h α → ℝ) → ∀ q, X q → ℝ)
    (C K : ℝ≥0) (hC : 1 ≤ C) {G ε δ : ℝ} (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hcap : ∀ r y q x, |f r y q x| ≤ C)
    (hLip : ∀ r q x, LipschitzOnWith K (fun y => f r y q x) (Metric.closedBall 0 1))
    (hmask : ∀ r q x, 0 ≤ mask r q x ∧ mask r q x ≤ G)
    (he : ∀ r y, (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0 → ∀ q x,
      |S q*(p y q x).toReal-mask r q x*f r (principalTupleNormalized L y) q x| ≤ ε)
    (t : Finset V) (out : V → ∀ q, X q)
    (a : PrincipalIntegerTuples B h α L → V → ℂ)
    (b : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℂ) (φ : V → ℂ)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ t, ‖a y v-b (principalResidueLabel m y) v‖ ≤ δ) :
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    let mass := fun y v => (∏ q, S q)*(dependentProductPMF (p y) (out v)).toReal
    let target := fun r v => (∏ q, mask r q (out v q)) *
      (∫ y, (∏ q, f r y q (out v q)) ∂jointBooleanSource h)
    let E := Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q+
      G^Fintype.card Q*jointTupleQuadratureError (α := α) B h (Fintype.card Q) C K L m
    ‖source.complexMean (fun y => 𝔼 v ∈ t, (mass y v : ℂ)*a y v*φ v) -
      (∑ r, 𝔼 v ∈ t, ((residues.weight r*target r v : ℝ) : ℂ)*b r v*φ v)‖ ≤
        δ*source.mean (fun y => 𝔼 v ∈ t, mass y v)+E*residues.mean (fun r => 𝔼 v ∈ t, ‖b r v‖) := by
  dsimp only
  refine principal_mixed_comparison B h L hL m hm hsize t _ _ a b φ ?_ hφ hspatial ?_
  · intro y _ v _
    exact mul_nonneg (Finset.prod_nonneg (fun q _ => hS q)) ENNReal.toReal_nonneg
  · intro r v _
    exact jointCoefficient_principalTuple_comparison B h L hL m hm r hsize hsmall p S (mask r) (f r)
      C K hC hG hε (hcap r) (hLip r) (hmask r) (he r) (out v)

end Erdos3

end

end OAI

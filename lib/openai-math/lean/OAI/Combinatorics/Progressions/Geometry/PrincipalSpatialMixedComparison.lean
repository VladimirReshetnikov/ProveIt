import OAI.Combinatorics.Progressions.Estimates.PrincipalMixedComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalSpatial_mixed_comparison {D A α J N V : Type*}
    [Fintype D] [DecidableEq D] [Fintype A] [Fintype α] [DecidableEq α]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    {ℓ M : ℕ} {ρ ξ r ε : ℝ} (s : α ↪ J)
    (x : J → IntegerScalarCubeBox α ℓ) (root : J → ℤ)
    (hM : 0 < M) (hℓ : 0 < ℓ) (hx : GoodScalarKernelTuple s (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (ℓ : ℤ)) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hp : integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (c : A → N → ℤ) (index : A → N → PrincipalTupleIndex B h)
    (H : A → ℝ) (Q : A → N → ℝ) (hH : ∀ a, 0 < H a) (hQ : ∀ a n, 0 < Q a n)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ a n, ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)*Q a n ≤ ξ*H a)
    (hρ : 0 < ρ) (hscale : ∀ a, ρ ≤ H a/ℓ) (hscaleQ : ∀ a n, ρ ≤ Q a n)
    (hlarge : smoothSpatialMeshThreshold α J N ℓ ≤ ρ) (hr : 0 < r)
    (t : Finset V) (out : V → A → (Unit ⊕ α) → ℤ)
    (W : PrincipalIntegerTuples B h α L → V → ℝ)
    (target : (PrincipalTupleIndex B h → Option α → ZMod m) → V → ℝ) (φ : V → ℂ)
    (hW : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 → ∀ v ∈ t, 0 ≤ W y v)
    (hφ : ∀ v ∈ t, ‖φ v‖ ≤ 1)
    (hbox : ∀ v ∈ t, ∀ a i, |((spatialStar (out v a) i : ℤ) : ℝ)/H a| ≤ 1)
    (hcoeff : ∀ rr v, v ∈ t →
      |(principalResidueWeights B h L hL m hm rr hsize).mean (fun y => W y v)-target rr v| ≤ ε) :
    let P := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let F := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hP := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hP
      (H a) ℓ (hH a) (by exact_mod_cast hℓ)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let E := smoothSpatialError N s M ℓ ρ ξ
    let source := principalTupleWeights (α := α) B h L hL
    let residues := source.fiberLaw (principalResidueLabel m)
    let site := fun rr v => ∏ a, spatialSiteApprox P
      (Matrix.fromCols F (liftResidueMatrix (principalSpatialResidueColumns m (c a) (index a) rr)))
      m (f a) (H a) 1 r (out v a)
    ‖source.complexMean (fun y => 𝔼 v ∈ t, (W y v : ℂ)*
        (((∏ a, ∏ _i : Unit ⊕ α, H a)*
          (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
            (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
            (by exact_mod_cast hℓ) hQ (out v)).toReal : ℝ) : ℂ)*φ v) -
      (∑ rr, 𝔼 v ∈ t, ((residues.weight rr*target rr v : ℝ) : ℂ)*site rr v*φ v)‖ ≤
      (Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*(1+G*smoothSpatialDensityCap s M+E)^Fintype.card A)*
        source.mean (fun y => 𝔼 v ∈ t, W y v) +
        ε*residues.mean (fun rr => 𝔼 v ∈ t, ‖site rr v‖) := by
  dsimp only
  refine principal_mixed_comparison B h L hL m hm hsize t W target _ _ φ hW hφ ?_ hcoeff
  intro y _ v hv
  exact principalVectorSpatial_site_error s x root hM hℓ hx hroot m hp c index H Q hH hQ
    hξ0 hξ1 hwidth hρ hscale hscaleQ hlarge hr y (out v) (hbox v hv)

end Erdos3

end

end OAI

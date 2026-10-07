import OAI.Combinatorics.Progressions.Probability.PrincipalTestMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def principalResidueLift {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod m) : JointBlockParameter B h α → ℤ :=
  Classical.choose (principalTupleResidues_has_lift m r)

theorem principalResidueLift_spec {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod m) :
    integerResidueMap _ m (principalResidueLift m r) = principalTupleResidues r :=
  Classical.choose_spec (principalTupleResidues_has_lift m r)

theorem independentPMF_grid_mass_le_one {Q : Type*} [Fintype Q]
    (I : Q → Type*) [∀ q, Fintype (I q)] (p : ∀ q, PMF (I q → ℤ))
    (grid : Finset ((Σ q, I q) → ℤ)) :
    (∑ v ∈ grid, ∏ q, (p q (fun i => v ⟨q, i⟩)).toReal) ≤ 1 := by
  classical
  let E : ((Σ q, I q) → ℤ) ↪ (∀ q, I q → ℤ) :=
    ⟨fun v q i => v ⟨q, i⟩, fun v w he => funext (fun j => congrFun (congrFun he j.1) j.2)⟩
  have he := pmf_sum_toReal_le_one (dependentProductPMF p) (grid.map E)
  have hE (v : (Σ q, I q) → ℤ) (q) : E v q = fun i => v ⟨q, i⟩ := rfl
  simpa only [Finset.sum_map, dependentProductPMF_apply, ENNReal.toReal_prod, hE] using he

theorem principalResidueWeights_nonzero_source {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (y : PrincipalIntegerTuples B h α L) (hy : (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0) :
    (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 := by
  classical
  intro hz
  apply hy
  rw [principalResidueWeights_eq_condition]
  simp [FiniteProbabilityWeights.condition, hz]

theorem principal_jointPMF_grid_mixture {Q D α : Type*}
    [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) [NeZero m] (hm : 0 < m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (I : Q → Type*) [∀ q, Fintype (I q)]
    (P : PrincipalIntegerTuples B h α L → ∀ q, PMF (I q → ℤ))
    (grid : Finset ((Σ q, I q) → ℤ))
    (a : PrincipalIntegerTuples B h α L → ((Σ q, I q) → ℤ) → ℂ)
    (b : (PrincipalTupleIndex B h → Option α → ZMod m) → ((Σ q, I q) → ℤ) → ℂ)
    (f : (PrincipalTupleIndex B h → Option α → ZMod m) → ((Σ q, I q) → ℝ) → ℝ)
    (shift scale : (Σ q, I q) → ℝ)
    (mask : (PrincipalTupleIndex B h → Option α → ZMod m) → ((Σ q, I q) → ℤ) → ℝ)
    (M ε : (PrincipalTupleIndex B h → Option α → ZMod m) → ℝ)
    (hM : ∀ r, 0 < M r) (hb : ∀ r v, v ∈ grid → ‖b r v‖ ≤ M r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hspatial : ∀ y, (principalTupleWeights (α := α) B h L hL).weight y ≠ 0 →
      ∀ v ∈ grid, ‖a y v - b (principalResidueLabel m y) v‖ ≤ δ)
    (hcoeff : ∀ r ψ, (∀ v ∈ grid, ‖ψ v‖ ≤ 1) →
      ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => ∑ v ∈ grid, ((∏ q, (P y q (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * ψ v) -
          gridDensityTest (f r) shift scale grid (mask r) ψ‖ ≤ ε r)
    (φ : ((Σ q, I q) → ℤ) → ℂ) (hφ : ∀ v ∈ grid, ‖φ v‖ ≤ 1) :
    let p := principalTupleWeights (α := α) B h L hL
    let q := p.fiberLaw (principalResidueLabel m)
    ‖p.complexMean (fun y => ∑ v ∈ grid,
        ((∏ q, (P y q (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * a y v * φ v) -
      q.complexMean (fun r => gridDensityTest (f r) shift scale grid (mask r) (fun v => b r v * φ v))‖ ≤
        δ + q.mean (fun r => M r * ε r) := by
  apply principal_mixed_test_comparison B h L hL m hm hsize grid
    (fun y v => ∏ q, (P y q (fun i => v ⟨q, i⟩)).toReal) a b
    (fun r ψ => gridDensityTest (f r) shift scale grid (mask r) ψ)
    (fun r z ψ => gridDensityTest_smul (f r) shift scale grid (mask r) z ψ)
    M ε hM hb hδ _ _ hspatial hcoeff φ hφ
  · intro y _ v _
    exact Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  · intro y _
    exact independentPMF_grid_mass_le_one I (P y) grid

end Erdos3

end

end OAI

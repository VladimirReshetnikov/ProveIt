import OAI.Combinatorics.Progressions.Linear.NativeComparisonProjections
import OAI.Combinatorics.Progressions.Polynomial.RealComparisonPolynomialProjections

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_eval_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℚ) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (eval x (F.realPolarizedLog π p)) =
      eval (fun i => x (e.symm i)) (F.realPolarizedLog π p) := by
  rw [F.realPolarizedLog_eval, F.realPolarizedLog_eval]
  simp only [map_sum, LinearMap.map_smul_of_tower, F.realPolarizedCoefficient_permute π p e he]
  symm
  calc
    (∑ a : SquarefreeIndex ι, (a.val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p a) =
      ∑ a : SquarefreeIndex ι,
        ((SquarefreeIndex.permute e a).val.prod fun i n => x (e.symm i) ^ n) •
        F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) :=
      (Equiv.sum_comp (SquarefreeIndex.permute e) _).symm
    _ = _ := by simp only [SquarefreeIndex.permute_weight]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def polarizeRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  F.realPolarizedOrbit π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩

theorem polarizeRealOrbit_zero (p : F.realification.PolynomialOrbit) :
    (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval 0
      (F.polarizeRealOrbit π p) = 1 :=
  F.realPolarizedOrbit_eval_zero π _

theorem polarizeRealOrbit_permute (p : F.realification.PolynomialOrbit)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (x : ι → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.squarefreeBlockPermute π e he).toLieHom)
        ((F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval x
          (F.polarizeRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (e.symm i)) (F.polarizeRealOrbit π p) := by
  apply NilpotentLieBCHGroup.ext
  exact F.realPolarizedLog_eval_permute π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩
    e he (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def compareRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F := (F.comparisonFiltration π).realification)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩)
    (F.realComparisonLog_adapted π ⟨p.log F.realification, p.adapted F.realification⟩)

theorem compareRealOrbit_zero (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) 0
      (F.compareRealOrbit π p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ => 0)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩) = 0
  rw [eval_zero_eq_coefficient, F.realComparisonLog_coefficient, F.realComparisonCoefficient_zero_index]

theorem compareRealOrbit_projections (p : F.realification.PolynomialOrbit)
    (hp : F.realification.polynomialOrbitEval 0 p = 1) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonFirst π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) = F.realification.polynomialOrbitEval x p ∧
      NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonSecond π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun j => x (π j)) (F.polarizeRealOrbit π p) := by
  have hz : coefficients (p.log F.realification) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp
    change eval (fun _ => 0) (p.log F.realification) = 0 at h
    rwa [eval_zero_eq_coefficient] at h
  constructor
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_first_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_second_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonSpaceOrbit_projections (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit)
    (hg : M.filtration.realification.polynomialOrbitEval 0 g = 1) (x : σ → ℤ) :
    let π := fun i : ReplicatedIndex bound => i.1
    let z := (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval
      (fun _ => 1) x (M.filtration.compareRealOrbit π g)
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk z) =
      QuotientGroup.mk ((M.filtration.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun i => x (π i)) (M.filtration.polarizeRealOrbit π g)) := by
  have h := M.filtration.compareRealOrbit_projections
    (fun i : ReplicatedIndex bound => i.1) g hg x
  constructor
  · simpa only [comparisonFirstSpace_mk, realificationMap] using
      congrArg (fun y : D.RealGroup => (QuotientGroup.mk y : D.Space)) h.1
  · simpa only [comparisonSecondSpace_mk, realificationMap] using
      congrArg (fun y : (M.squarefreeModel p B hB hstable).RealGroup =>
        (QuotientGroup.mk y : (M.squarefreeModel p B hB hstable).Space)) h.2

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_normalized_comparison_orbit (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B)
    (E : RationalFilteredNilmanifold
      (M.filtration.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1))
      (max s (Fintype.card (ReplicatedIndex bound))) r)
    (hEF : E.filtration = M.filtration.comparisonFiltration (fun j : ReplicatedIndex bound => j.1))
    (hEL : E.lattice = M.comparisonLattice p B hB hstable)
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        ε • M.comparisonFirstSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) ∧
        M.comparisonSecondSpace p B hB hstable E hEL
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x h)) =
            QuotientGroup.mk
              ((M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)).realification.polynomialOrbitEval
                (fun j => x j.1) (M.filtration.polarizeRealOrbit (fun j : ReplicatedIndex bound => j.1) g₀)) := by
  let π := fun j : ReplicatedIndex bound => j.1
  let g₀ := M.filtration.realification.normalizeMultidegreeOrbit g ε γ
  have hg₀ : M.filtration.realification.polynomialOrbitEval 0 g₀ = 1 :=
    M.filtration.realification.normalizeMultidegreeOrbit_zero g ε γ hfactor
  have hF : (M.filtration.comparisonFiltration π).realification = E.filtration.realification := by rw [hEF]
  let h := (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq hF (fun _ : σ => 1)
    (M.filtration.compareRealOrbit π g₀)
  have heval (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x h =
      (M.filtration.comparisonFiltration π).realification.polynomialOrbitEval _ x
        (M.filtration.compareRealOrbit π g₀) :=
    (M.filtration.comparisonFiltration π).realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨h, (heval 0).trans (M.filtration.compareRealOrbit_zero π g₀), fun x => ?_⟩
  rw [heval]
  obtain ⟨h₁, h₂⟩ := M.comparisonSpaceOrbit_projections p B hB hstable E hEL g₀ hg₀ x
  constructor
  · rw [h₁]
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x g₀) : D.Space) = _
    change (QuotientGroup.mk (ε * M.filtration.realification.polynomialOrbitEval x
      (M.filtration.realification.normalizeMultidegreeOrbit g ε γ)) : D.Space) = _
    rw [M.filtration.realification.normalizeMultidegreeOrbit_eval]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · exact h₂

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

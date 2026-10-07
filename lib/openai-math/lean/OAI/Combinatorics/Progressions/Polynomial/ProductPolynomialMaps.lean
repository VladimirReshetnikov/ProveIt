import OAI.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem piRealOrbit_projection_log {ι σ : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w) (a : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval a)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F g).log = (g a).log := by
  classical
  apply coefficients.injective
  ext α
  simp only [coefficients_map, piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · exact realProductSingle_projection a _
  · intro j _ hja
    exact realProductSingle_projection_ne (Ne.symm hja) _
  · simp

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (f : κ → ι)

noncomputable def productRestrictionIndex
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    Fin (Fintype.card (Σ i, Fin (d i))) :=
  let z := (Fintype.equivFin (Σ j : κ, Fin (d (f j)))).symm k
  Fintype.equivFin (Σ i, Fin (d i)) ⟨f z.1, z.2⟩

theorem productRestriction_coordinates (x : ∀ i, L i)
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    (pi (fun j => D (f j))).basis.repr (liePiMap (fun j => liePiEval (R := ℚ) (f j)) x) k =
      (pi D).basis.repr x (productRestrictionIndex (d := d) f k) := by
  rw [productFinBasis_repr]
  exact productFinBasis_repr_component D x _ _

theorem productRestriction_layers (j : ℕ) (x : ∀ i, L i)
    (hx : x ∈ (pi D).filtration.layer j) :
    liePiMap (fun k => liePiEval (R := ℚ) (f k)) x ∈ (pi (fun k => D (f k))).filtration.layer j := by
  apply (mem_pi_layer (fun k => (D (f k)).filtration) j _).mpr
  intro k
  exact (mem_pi_layer (fun i => (D i).filtration) j x).mp hx (f k)

theorem productRestriction_lattice :
    (pi D).lattice ≤ (pi (fun j => D (f j))).lattice.comap
      (mapOfSteps (hL := (pi D).filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun j => D (f j))).filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun j => liePiEval (R := ℚ) (f j)))) := by
  intro x hx
  apply (mem_piBCHSubgroup _ _ _).mpr
  intro j
  exact (mem_piBCHSubgroup _ _ x).mp hx (f j)

theorem productRestriction_realLattice (x : (pi D).RealGroup) (hx : x ∈ (pi D).realLattice) :
    realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi (fun j => D (f j))).filtration.lowerCentralSeries_eq_bot)
      (liePiMap (fun j => liePiEval (R := ℚ) (f j))) x ∈ (pi (fun j => D (f j))).realLattice :=
  realificationMap_subgroup _ _ _ (productRestriction_lattice D f) hx

theorem productRestriction_piRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    VectorPolynomial.map ((realificationLieHom (liePiMap (fun j => liePiEval (R := ℚ) (f j)))).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (D i).filtration) g).log =
        (piRealOrbit (fun j => (D (f j)).filtration) (fun j => g (f j))).log := by
  apply coefficients.injective
  ext α
  apply ((pi (fun j => D (f j))).basis.baseChange ℝ).repr.injective
  ext k
  rw [realProductFinBasis_repr, realProductFinBasis_repr, coefficients_map]
  let z := (Fintype.equivFin (Σ j : κ, Fin (d (f j)))).symm k
  change ((D (f z.1)).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval z.1)
      (realificationLieHom (liePiMap (fun j => liePiEval (R := ℚ) (f j)))
        (coefficients (piRealOrbit (fun i => (D i).filtration) g).log α))) z.2 =
    ((D (f z.1)).basis.baseChange ℝ).repr (realificationLieHom (liePiEval z.1)
      (coefficients (piRealOrbit (fun j => (D (f j)).filtration) (fun j => g (f j))).log α)) z.2
  rw [realification_liePiEval_liePiMap]
  have hleft := congrArg (fun p => coefficients p α)
    (piRealOrbit_projection_log (fun i => (D i).filtration) g (f z.1))
  have hright := congrArg (fun p => coefficients p α)
    (piRealOrbit_projection_log (fun j => (D (f j)).filtration) (fun j => g (f j)) z.1)
  simp only [coefficients_map] at hleft hright
  exact congrArg (fun x => ((D (f z.1)).basis.baseChange ℝ).repr x z.2)
    (hleft.trans hright.symm)

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

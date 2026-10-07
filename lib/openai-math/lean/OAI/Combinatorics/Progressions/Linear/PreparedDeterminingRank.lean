import OAI.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget

namespace OAI

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationFamily

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem determining_card :
    Fintype.card (Σ j, PreparedSamplerContinuous L j) = ∑ j, (L j).rank := by
  simp only [Fintype.card_sigma, PreparedSamplerContinuous, Fintype.card_fin]

theorem determining_card_le_potential :
    Fintype.card (Σ j, PreparedSamplerContinuous L j) ≤ L.potential := by
  rw [L.determining_card]
  exact sum_ranks_le_potential (fun j => (L j).rank)

variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
  (euclideanSubspace (U j)))
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))

include U b o bW hb

theorem lattice_determining_card : Fintype.card (Σ j, Eout j) = ∑ j, (L j).rank := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
    allocatedLatticeDimension_eq U b o hb bW j

theorem lattice_determining_card_le {D : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D) :
    Fintype.card (Σ j, Eout j) ≤ m * D := by
  rw [L.lattice_determining_card U b o bW hb]
  exact hprepared

theorem recovered_lattice_rank_bound {s d₀ d D E : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hD : D ≤ d) (hE : E ≤ d₀ + s * (d - D)) (hm : m ≤ s) :
    Fintype.card (Σ j, Eout j) + E ≤ d₀ + s * d :=
  recursive_patch_step_rank_bound hD hE
    (L.lattice_determining_card_le U b o bW hb hprepared) hm

end RankPreparationFamily

namespace PolynomialPatch

variable {X J σ : Type} {m s d₀ d D E : ℕ} (L : RankPreparationFamily X J m)
variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
  (euclideanSubspace (U j)))
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (hprepared : (∑ j, (L j).rank) ≤ m * D)
variable (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d - D)) (hm : m ≤ s)

noncomputable def padPreparedRecoveredRank
    (Q : PolynomialPatch σ s (Fintype.card (Σ j, Eout j) + E)) :
    PolynomialPatch σ s (d₀ + s * d) :=
  Q.padRank hs (L.recovered_lattice_rank_bound U b o bW hb hprepared hD hE hm)

@[simp] theorem padPreparedRecoveredRank_value
    (Q : PolynomialPatch σ s (Fintype.card (Σ j, Eout j) + E)) (x : σ → ℝ) :
    (Q.padPreparedRecoveredRank L U b o bW hb hprepared hs hD hE hm).value x =
      Q.value x := padRank_value _ _ _ _

@[simp] theorem padPreparedRecoveredRank_lip
    (Q : PolynomialPatch σ s (Fintype.card (Σ j, Eout j) + E)) :
    (Q.padPreparedRecoveredRank L U b o bW hb hprepared hs hD hE hm).kernel.lip =
      Q.kernel.lip + 4 := padRank_lip _ _ _

end PolynomialPatch
end Erdos3

end

end OAI

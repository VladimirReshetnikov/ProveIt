import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates
import OAI.Combinatorics.Progressions.Geometry.PreparedDeterminingCoordinates
import OAI.Combinatorics.Progressions.Geometry.SortedLayerCoordinateEnumeration
import OAI.Combinatorics.Progressions.Linear.PreparedDeterminingRank

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def sortedDeterminingPolynomial
    (i : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.determiningPolynomial bW hmem (sortedLayerCoordinateEquiv E i)

noncomputable def sortedDeterminingMatrix {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j))) : ℤ :=
  L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a)

theorem sortedDeterminingPolynomial_support
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (i : Fin (Fintype.card (Σ j, E j))) :
    L.sortedDeterminingPolynomial bW hmem i ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E i) := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (L.sortedDeterminingPolynomial bW hmem i).weightedTotalDegree (1 : X → ℕ) ≤ _
  rw [MvPolynomial.weightedTotalDegree_one]
  exact L.determiningPolynomial_degree bW hmem hdegree (sortedLayerCoordinateEquiv E i)

theorem sortedDeterminingMatrix_weight {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j)))
    (hne : L.sortedDeterminingMatrix bW e i a ≠ 0) :
    sortedLayerCoordinateWeight E a ≤ (e i).1.val + 1 :=
  (L.determiningMatrix_weight bW (e i) (sortedLayerCoordinateEquiv E a) hne).le

theorem sortedDeterminingPolynomial_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (fun a => MvPolynomial.aeval x (L.sortedDeterminingPolynomial bW hmem a)) i =
        eval x (L (e i).1).poly (e i).2 := by
  change (∑ a, (L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ) *
      MvPolynomial.eval x (L.determiningPolynomial bW hmem (sortedLayerCoordinateEquiv E a))) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a =>
    (L.determiningMatrix bW (e i) a : ℝ) *
      MvPolynomial.eval x (L.determiningPolynomial bW hmem a))]
  exact (L.determiningPolynomial_reconstruction bW hmem x (e i)).symm

include bW

theorem integral_determining_card : Fintype.card (Σ j, E j) = ∑ j, (L j).rank := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact (L j).integralCoordinateBasis_card (bW j)

theorem sortedDeterminingRecovered_rank {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s) :
    Fintype.card (Σ j, E j) + returned ≤ d₀ + s * d := by
  apply recursive_patch_step_rank_bound hD hreturned (j := m) _ hm
  rw [L.integral_determining_card bW]
  exact hprepared

noncomputable def determiningPatch {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    PolynomialPatch X s (Fintype.card (Σ j, E j)) :=
  PolynomialPatch.ofCoordinates (sortedLayerCoordinateWeight E)
    (sortedLayerCoordinateWeight_pos E)
    (fun i => (sortedLayerCoordinateWeight_le E i).trans hm)
    (sortedLayerCoordinateWeight_mono E)
    (L.sortedDeterminingPolynomial bW hmem)
    (L.sortedDeterminingPolynomial_support bW hmem hdegree) Φ

noncomputable def padDeterminingRecovered {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) :
    PolynomialPatch X s (d₀ + s * d) :=
  Q.padRank hs (L.sortedDeterminingRecovered_rank bW hprepared hD hreturned hm)

@[simp] theorem padDeterminingRecovered_value {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) (x : X → ℝ) :
    (L.padDeterminingRecovered bW hprepared hs hD hreturned hm Q).value x = Q.value x :=
  PolynomialPatch.padRank_value _ _ _ _

@[simp] theorem padDeterminingRecovered_lip {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) :
    (L.padDeterminingRecovered bW hprepared hs hD hreturned hm Q).kernel.lip =
      Q.kernel.lip + 4 := PolynomialPatch.padRank_lip _ _ _

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)

noncomputable def determiningCenterCoordinate (a : L.DeterminingIndex E) : ℝ :=
  ((L a.1).integralCoordinateBasis (bW a.1)).repr (c a.1) a.2

theorem determiningCenterCoordinate_reconstruction (r : L.PreparedCoordinate) :
    (c r.1).val r.2 = ∑ a : L.DeterminingIndex E,
      (L.determiningMatrix bW r a : ℝ) * L.determiningCenterCoordinate bW c a := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ a : E u, (L.determiningMatrix bW r ⟨u, a⟩ : ℝ) *
        L.determiningCenterCoordinate bW c ⟨u, a⟩) =
      if h : u = r.1 then
        ∑ a : E r.1, ((L r.1).integralCoordinateMatrix (bW r.1) r.2 a : ℝ) *
          L.determiningCenterCoordinate bW c ⟨r.1, a⟩
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp [determiningMatrix]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  rw [Fintype.sum_dite_eq']
  have h := congrArg (fun v : (L r.1).space => v.val r.2)
    (((L r.1).integralCoordinateBasis (bW r.1)).sum_repr (c r.1))
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, determiningCenterCoordinate,
    RankPreparationLayer.integralCoordinateMatrix_cast, mul_comm] using h.symm

noncomputable def sortedDeterminingCenter
    (a : Fin (Fintype.card (Σ j, E j))) : ℝ :=
  L.determiningCenterCoordinate bW c (sortedLayerCoordinateEquiv E a)

theorem sortedDeterminingCenter_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (L.sortedDeterminingCenter bW c) i = (c (e i).1).val (e i).2 := by
  change (∑ a, (L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ) *
    L.determiningCenterCoordinate bW c (sortedLayerCoordinateEquiv E a)) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a =>
    (L.determiningMatrix bW (e i) a : ℝ) * L.determiningCenterCoordinate bW c a)]
  exact (L.determiningCenterCoordinate_reconstruction bW c (e i)).symm

variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def centeredDeterminingPolynomial
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.sortedDeterminingPolynomial bW hmem a - MvPolynomial.C (L.sortedDeterminingCenter bW c a)

theorem centeredDeterminingPolynomial_support
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (a : Fin (Fintype.card (Σ j, E j))) :
    L.centeredDeterminingPolynomial bW c hmem a ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E a) :=
  (weightedSupportLE _ _).sub_mem
    (L.sortedDeterminingPolynomial_support bW hmem hdegree a)
    (weightedSupportLE_C _ _ _)

theorem centeredDeterminingPolynomial_reconstruction {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℝ) (i : Fin n) :
    realIntegerMatrix (L.sortedDeterminingMatrix bW e)
      (fun a => MvPolynomial.aeval x (L.centeredDeterminingPolynomial bW c hmem a)) i =
      eval x (L (e i).1).poly (e i).2 - (c (e i).1).val (e i).2 := by
  calc
    _ = realIntegerMatrix (L.sortedDeterminingMatrix bW e)
        (fun a => MvPolynomial.aeval x (L.sortedDeterminingPolynomial bW hmem a)) i -
        realIntegerMatrix (L.sortedDeterminingMatrix bW e)
          (L.sortedDeterminingCenter bW c) i := by
      simp only [centeredDeterminingPolynomial, realIntegerMatrix, map_sub,
        MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        mul_sub, Finset.sum_sub_distrib]
    _ = _ := by rw [L.sortedDeterminingPolynomial_reconstruction bW hmem,
      L.sortedDeterminingCenter_reconstruction bW c]

theorem fullTaggedBufferedCoordinates_eq_centeredDetermining {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (x : X → ℤ) :
    fullTaggedBufferedCoordinates e (fun j => (L j).poly) (fun j => (c j).val) x =
      realIntegerMatrix (L.sortedDeterminingMatrix bW e)
        (fun a => MvPolynomial.aeval (fun i => (x i : ℝ))
          (L.centeredDeterminingPolynomial bW c hmem a)) := by
  funext i
  exact (L.centeredDeterminingPolynomial_reconstruction bW c hmem e
    (fun i => (x i : ℝ)) i).symm

noncomputable def centeredDeterminingPatch {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    PolynomialPatch X s (Fintype.card (Σ j, E j)) :=
  PolynomialPatch.ofCoordinates (sortedLayerCoordinateWeight E)
    (sortedLayerCoordinateWeight_pos E)
    (fun i => (sortedLayerCoordinateWeight_le E i).trans hm)
    (sortedLayerCoordinateWeight_mono E)
    (L.centeredDeterminingPolynomial bW c hmem)
    (L.centeredDeterminingPolynomial_support bW c hmem hdegree) Φ

end Erdos3.RankPreparationFamily

end

end OAI

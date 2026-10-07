import OAI.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tupleColumnMatrix {I J : Type*} {Ω : J → Type*}
    (c : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) : Matrix I J ℤ :=
  Matrix.of (fun i j => c j (x j) i)

noncomputable def columnResidueSet {I X : Type*} [Fintype X]
    (c : X → I → ℤ) (m : ℕ) (r : I → ZMod m) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => integerResidueMap I m (c x) = r)

theorem mem_columnResidueSet {I X : Type*} [Fintype X]
    (c : X → I → ℤ) (m : ℕ) (r : I → ZMod m) (x : X) :
    x ∈ columnResidueSet c m r ↔ integerResidueMap I m (c x) = r := by
  classical
  simp only [columnResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem tupleColumnMatrix_residue_iff {I J : Type*} {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (c : ∀ j, Ω j → I → ℤ) (m : ℕ) (r : Matrix I J (ZMod m)) (x : ∀ j, Ω j) :
    integerResidueMatrix (tupleColumnMatrix c x) m = r ↔
      ∀ j, x j ∈ columnResidueSet (c j) m (fun i => r i j) := by
  simp only [mem_columnResidueSet]
  constructor
  · intro h j
    funext i
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact congrFun (h j) i

theorem tupleColumnMatrix_residue_set {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (c : ∀ j, Ω j → I → ℤ) (m : ℕ) (r : Matrix I J (ZMod m)) :
    Finset.univ.filter (fun x => integerResidueMatrix (tupleColumnMatrix c x) m = r) =
      FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteProbabilityWeights.mem_piRestrictionSet, tupleColumnMatrix_residue_iff]

theorem tupleColumnMatrix_residue_mass {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (c : ∀ j, Ω j → I → ℤ)
    (m : ℕ) (r : Matrix I J (ZMod m)) :
    (FiniteProbabilityWeights.pi p).mass
      (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j))) =
      ∏ j, (p j).mass (columnResidueSet (c j) m (fun i => r i j)) :=
  FiniteProbabilityWeights.piRestriction_mass _ _

theorem tupleColumnMatrix_residue_condition {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (c : ∀ j, Ω j → I → ℤ)
    (m : ℕ) (r : Matrix I J (ZMod m))
    (hr : ∀ j, 0 < (p j).mass (columnResidueSet (c j) m (fun i => r i j))) :
    FiniteProbabilityWeights.pi
      (fun j => (p j).condition (columnResidueSet (c j) m (fun i => r i j)) (hr j)) =
    (FiniteProbabilityWeights.pi p).condition
      (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j)))
      (FiniteProbabilityWeights.piRestriction_mass_pos p _ hr) :=
  FiniteProbabilityWeights.pi_condition _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem condition_weight_support {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) (hG : 0 < p.mass G)
    (x : X) (hx : (p.condition G hG).weight x ≠ 0) : x ∈ G ∧ p.weight x ≠ 0 := by
  have hm : x ∈ G := by
    by_contra hn
    exact hx (by simp [FiniteProbabilityWeights.condition, hn])
  refine ⟨hm, ?_⟩
  intro hz
  exact hx (by simp [FiniteProbabilityWeights.condition, hz])

theorem piRestriction_positive_factors {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (G : ∀ j, Finset (Ω j))
    (h : 0 < (FiniteProbabilityWeights.pi p).mass (FiniteProbabilityWeights.piRestrictionSet G)) :
    ∀ j, 0 < (p j).mass (G j) := by
  intro j
  by_contra hn
  have hz : (p j).mass (G j) = 0 := le_antisymm (le_of_not_gt hn) ((p j).mass_nonneg _)
  have hzero : (∏ j, (p j).mass (G j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hz
  rw [FiniteProbabilityWeights.piRestriction_mass, hzero] at h
  exact (lt_irrefl 0) h

theorem tupleResidue_condition_independent {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (c : ∀ j, Ω j → I → ℤ)
    (m : ℕ) (r : Matrix I J (ZMod m))
    (h : 0 < (FiniteProbabilityWeights.pi p).mass
      (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j)))) :
    let hr := piRestriction_positive_factors p (fun j => columnResidueSet (c j) m (fun i => r i j)) h
    (FiniteProbabilityWeights.pi p).condition
        (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j))) h =
      FiniteProbabilityWeights.pi
        (fun j => (p j).condition (columnResidueSet (c j) m (fun i => r i j)) (hr j)) := by
  exact (FiniteProbabilityWeights.pi_condition _ _ _).symm

theorem tupleResidue_condition_support {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (c : ∀ j, Ω j → I → ℤ)
    (m : ℕ) (r : Matrix I J (ZMod m))
    (h : 0 < (FiniteProbabilityWeights.pi p).mass
      (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j))))
    (x : ∀ j, Ω j)
    (hx : ((FiniteProbabilityWeights.pi p).condition
      (FiniteProbabilityWeights.piRestrictionSet (fun j => columnResidueSet (c j) m (fun i => r i j))) h).weight x ≠ 0) :
    integerResidueMatrix (tupleColumnMatrix c x) m = r := by
  apply (tupleColumnMatrix_residue_iff c m r x).mpr
  exact (FiniteProbabilityWeights.mem_piRestrictionSet _ x).mp
    (condition_weight_support _ _ h x hx).1

theorem spatialResiduePattern_card (I N : Type*) [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] (m : ℕ) [NeZero m] :
    Fintype.card (Matrix (Unit ⊕ I) N (ZMod m)) = m ^ ((Fintype.card I + 1) * Fintype.card N) := by
  rw [← Fintype.card_congr (Matrix.of : ((Unit ⊕ I) → N → ZMod m) ≃ Matrix (Unit ⊕ I) N (ZMod m))]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_unit]
  rw [← pow_mul]
  congr 1
  ring

end Erdos3

end

end OAI

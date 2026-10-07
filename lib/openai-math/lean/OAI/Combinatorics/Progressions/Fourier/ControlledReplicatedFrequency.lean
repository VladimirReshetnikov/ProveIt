/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.ComparisonAmbient

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedFrequency (η : L →ₗ[ℚ] ℚ) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] ℚ :=
  η.comp ((F.layer bound).subtype.comp F.replicatedTopCoefficient)

theorem replicatedFrequency_apply (η : L →ₗ[ℚ] ℚ)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedFrequency η x =
      η (squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound))) := rfl

theorem replicatedFrequency_permute (η : L →ₗ[ℚ] ℚ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedFrequency η (F.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x) =
      F.replicatedFrequency η x := by
  change η (squarefreePolynomialEquiv (squarefreePermute e x.val) _) = _
  rw [squarefreePermute_coefficient, SquarefreeIndex.permute_symm, SquarefreeIndex.permute_full]
  rfl

variable {κ : SquarefreeIndex (ReplicatedIndex bound) → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

theorem replicatedFrequency_basis_full (η : L →ₗ[ℚ] ℚ)
    (j : κ (SquarefreeIndex.full (ReplicatedIndex bound))) :
    F.replicatedFrequency η
        (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨SquarefreeIndex.full _, j⟩) =
      η (b (SquarefreeIndex.full _) j).val := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_self]

theorem replicatedFrequency_basis_ne (η : L →ₗ[ℚ] ℚ) (a : SquarefreeIndex (ReplicatedIndex bound))
    (ha : a ≠ SquarefreeIndex.full (ReplicatedIndex bound)) (j : κ a) :
    F.replicatedFrequency η (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨a, j⟩) = 0 := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_ne _ b a _ ha, map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem replicatedTopCoefficient_blockLayerMap (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedTopCoefficient (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) • x := by
  classical
  apply Subtype.ext
  rw [F.replicatedTopCoefficient_apply, F.blockLayerMap_coe,
    factorialBlockMonomial_coefficient, replicated_blockDegree_full, ite_eq_left rfl]
  rfl

theorem replicatedFrequency_blockLayerMap_top (η : L →ₗ[ℚ] ℚ)
    (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedFrequency η (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) * η x.val := by
  change η (F.replicatedTopCoefficient (F.blockLayerMap _ bound hb x)).val = _
  rw [F.replicatedTopCoefficient_blockLayerMap hb x]
  exact map_smul η _ x.val

theorem replicatedFrequency_blockLayerMap_ne (η : L →ₗ[ℚ] ℚ)
    (a : σ → ℕ) (ha : a ≠ 0) (hab : a ≠ bound) (x : F.layer a) :
    F.replicatedFrequency η (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) a ha x) = 0 := by
  classical
  rw [F.replicatedFrequency_apply, F.blockLayerMap_coe,
    factorialBlockMonomial_coefficient, replicated_blockDegree_full,
    ite_eq_right (Ne.symm hab), map_zero]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem comparisonLayer_top_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : L × F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ F.comparisonLayer (fun j : ReplicatedIndex bound => j.1) s) :
    (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2 := by
  have hterminal : F.comparisonProductLayer (fun j : ReplicatedIndex bound => j.1) (s + 1) = ⊥ := by
    have h := F.comparisonProductLayer_terminal (fun j : ReplicatedIndex bound => j.1)
    simpa only [replicatedIndex_card, ← hstep, max_self] using h
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have hu0 : u = 0 := by simpa only [hterminal, Submodule.mem_bot] using hu
  rw [hu0, zero_add]
  refine F.comparisonGraphLayer_induction (fun j : ReplicatedIndex bound => j.1) s
    (P := fun z => (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2) hv ?_ ?_ ?_
  · intro a ha hsa x
    by_cases hab : a ≤ bound
    · have heq : a = bound := by
        funext i
        apply le_antisymm (hab i)
        by_contra hi
        have hlt : a i < bound i := Nat.lt_of_not_ge hi
        have hsum : (∑ j, a j) < ∑ j, bound j :=
          Finset.sum_lt_sum (fun j _ => hab j) ⟨i, Finset.mem_univ i, hlt⟩
        omega
      subst a
      exact (F.replicatedFrequency_blockLayerMap_top η ha x).symm
    · have hx0 : x = 0 := by
        apply Subtype.ext
        have h : x.val ∈ (⊥ : Submodule ℚ L) := F.terminal a hab ▸ x.property
        exact (Submodule.mem_bot ℚ).mp h
      rw [hx0, map_zero]
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · intro x y hx hy
    change (multidegreeFactorial bound : ℚ) * η (x.1 + y.1) = F.replicatedFrequency η (x.2 + y.2)
    rw [map_add, map_add, mul_add, hx, hy]

theorem comparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s) :
    (multidegreeFactorial bound : ℚ) * η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) z) =
      F.replicatedFrequency η (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) z) :=
  F.comparisonLayer_top_frequency hstep η hz

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realComparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : ℝ ⊗[ℚ] F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).realification.layer s) :
    (multidegreeFactorial bound : ℝ) * realifyFunctional η
        (realificationLieHom (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1)) z) =
      realifyFunctional (F.replicatedFrequency η)
        (realificationLieHom (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1)) z) := by
  change z ∈ ((F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s).baseChange ℝ at hz
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    simp only [LinearMap.baseChange_tmul, realificationLieHom_tmul, realifyFunctional_tmul]
    change (multidegreeFactorial bound : ℝ) *
      (r * (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)) =
      r * (F.replicatedFrequency η
        (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ)
    have h := F.comparisonTop_frequency hstep η y.property
    have hr : (multidegreeFactorial bound : ℝ) *
        (η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) =
        (F.replicatedFrequency η
          (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) y.val) : ℝ) := by
      exact_mod_cast h
    rw [← hr]
    ring
  | add y w hy hw => simp only [map_add, mul_add, hy, hw]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

def replicatedFrequencyHeight (d H : ℕ) : ℕ := (d + 1) * (H * H) ^ d

theorem replicatedFrequencyHeight_pos (d : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < replicatedFrequencyHeight d H := by
  have hHpos : 0 < H := by omega
  unfold replicatedFrequencyHeight
  positivity

namespace RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem replicatedFrequency_basis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j : M.SquarefreeBasisIndex) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rcases j with ⟨a, k⟩
  by_cases ha : a = SquarefreeIndex.full (ReplicatedIndex bound)
  · subst a
    change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨_, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_full]
    have h := linearFunctional_coordinate_height D.basis η
      (fun i => rationalHeightLE_ceil_exp (hη i)) _ (M.squarefreeCoefficientBasis_height hM _ k)
    simp only [Fintype.card_fin] at h
    exact h
  · change RationalHeightLE (M.filtration.replicatedFrequency η
      (M.filtration.squarefreeBasis _ (M.squarefreeCoefficientBasis p) ⟨a, k⟩)) _
    rw [M.filtration.replicatedFrequency_basis_ne (M.squarefreeCoefficientBasis p) η a ha k]
    exact rationalHeightLE_zero (replicatedFrequencyHeight_pos d (one_le_ceil_exp p))

theorem replicatedFrequency_finBasis_height {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) (j) :
    RationalHeightLE (M.filtration.replicatedFrequency η (M.squarefreeFinBasis p j))
      (replicatedFrequencyHeight d ⌈Real.exp p⌉₊) := by
  rw [squarefreeFinBasis, Module.Basis.reindex_apply]
  exact M.replicatedFrequency_basis_height hM η hη _

theorem exists_replicatedFrequency_denominator {p : ℝ} (hM : M.ComplexityLE p) (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ l : ℕ, 0 < l ∧
      l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ Fintype.card M.SquarefreeBasisIndex ∧
      ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
        (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n := by
  obtain ⟨l, hl, hbound, z, hz, _⟩ := exists_bounded_integer_array
    (fun j => M.filtration.replicatedFrequency η (M.squarefreeBasis p j))
    (M.replicatedFrequency_basis_height hM η hη)
  exact ⟨l, hl, hbound, fun j => ⟨z j, (hz j).symm⟩⟩

end RationalFilteredNilmanifold.MultidegreeStructure

end Erdos3

end

section

namespace Erdos3

noncomputable def replicatedFrequencyDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  (2 : ℝ) ^ t * (p + 3) ^ 5

theorem replicatedFrequencyHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (replicatedFrequencyHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hprod : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ Real.exp p * Real.exp p := by rw [Nat.cast_mul]; gcongr
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact rational_sum_cost_le_exp d (H * H) hp 2 1 hprod
    (by simpa only [pow_one] using hd.trans (by linarith))

theorem replicatedFrequencyHeight_ceil_exp (d : ℕ) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 4) := by
  have h := replicatedFrequencyHeight_le_exp d ⌈Real.exp p⌉₊
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  have heq : p + 1 + 2 = p + 3 := by ring
  simpa only [heq] using h

theorem replicatedFrequencyDenominator_le_exp (t N d l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : l ≤ replicatedFrequencyHeight d ⌈Real.exp p⌉₊ ^ N) :
    (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p) := by
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ t * (p + 3) := by
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ _ := mul_le_mul_of_nonneg_left (hd.trans (by linarith)) (by positivity)
  calc
    (l : ℝ) ≤ (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ^ N := by exact_mod_cast hl
    _ ≤ (Real.exp ((p + 3) ^ 4)) ^ N :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (replicatedFrequencyHeight_ceil_exp d hp hd) N
    _ = Real.exp ((N : ℝ) * (p + 3) ^ 4) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (((2 : ℝ) ^ t * (p + 3)) * (p + 3) ^ 4) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hNr (by positivity))
    _ = _ := by congr 1; unfold replicatedFrequencyDenominatorBudget; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def squarefreeFrequencyInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeInputBudget t p + replicatedFrequencyDenominatorBudget t p

noncomputable def squarefreeFrequencyModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeFrequencyInputBudget t p +
    (squarefreeFrequencyInputBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem squarefreeInputBudget_le_frequency (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ squarefreeFrequencyInputBudget t p := by
  apply le_add_of_nonneg_right
  unfold replicatedFrequencyDenominatorBudget
  positivity

theorem squarefreeFrequencyInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ squarefreeFrequencyInputBudget t p :=
  (squarefreeInputBudget_nonneg t hp).trans (squarefreeInputBudget_le_frequency t hp)

theorem squarefreeFrequencyInputBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeFrequencyInputBudget t p ≤ squarefreeFrequencyModelBudget t p := by
  exact le_add_of_nonneg_right
    (pow_nonneg (add_nonneg (squarefreeFrequencyInputBudget_nonneg t hp) (Nat.cast_nonneg _)) _)

theorem squarefree_frequency_grid_budget (t N d l B : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p))
    (hB : B ≤ bchIntegralDenominatorBound t *
      squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (N ^ 3) * l) :
    (B : ℝ) ≤ Real.exp (squarefreeFrequencyModelBudget t p) := by
  have hq := squarefreeFrequencyInputBudget_nonneg t hp
  have hbase := squarefreeInputBudget_le_frequency t hp
  have hNq : (N : ℝ) ≤ squarefreeFrequencyInputBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyInputBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hd).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase))
  have hlq : (l : ℝ) ≤ Real.exp (squarefreeFrequencyInputBudget t p) :=
    hl.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (squarefreeInputBudget_nonneg t hp)))
  exact (Nat.cast_le.mpr hB).trans ((integral_grid_allowance_le_exp
    (bchIntegralDenominatorBound t) N _ l hq hNq hHq hlq).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq)))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group)
    (hg : g ∈ M.squarefreeLattice p B hstable) :
    ∃ n : ℤ, M.filtration.replicatedFrequency η g.coord = n :=
  coordinateGrid_functional_integral (M.squarefreeBasis p) (M.filtration.replicatedFrequency η)
    l B hdiv hη hg

theorem squarefreeRealLattice_frequency_integral (p : ℝ) (η : L →ₗ[ℚ] ℚ) (l B : ℕ)
    (hB : 0 < B) (hstable : M.SquarefreeGridStable p B) (hdiv : l ∣ B)
    (hη : ∀ j : M.SquarefreeBasisIndex, ∃ n : ℤ,
      (l : ℚ) * M.filtration.replicatedFrequency η (M.squarefreeBasis p j) = n)
    (z : (M.squarefreeModel p B hB hstable).RealGroup)
    (hz : z ∈ (M.squarefreeModel p B hB hstable).realLattice) :
    ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n :=
  (M.squarefreeModel p B hB hstable).realLattice_functional_integral
    (M.filtration.replicatedFrequency η)
    (M.squarefreeLattice_frequency_integral p η l B hstable hdiv hη) z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3

theorem exists_squarefreeFrequency_cost (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → squarefreeFrequencyModelBudget t p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let K := bchIntegralDenominatorBound t + 5
  let A := Polynomial.C (2 ^ t) * X + (X + 3) ^ 8 + Polynomial.C (2 ^ t) * (X + 3) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [X, K, A, squarefreeFrequencyModelBudget, squarefreeFrequencyInputBudget,
    squarefreeInputBudget, replicatedFrequencyDenominatorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_replicated_frequency {p : ℝ} (hM : M.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B),
      (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE
        (squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      (∀ i, rationalLogHeight (M.filtration.replicatedFrequency η
        ((M.squarefreeModel p B hB hstable).basis i)) ≤
          squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      ∀ z : (M.squarefreeModel p B hB hstable).RealGroup,
        z ∈ (M.squarefreeModel p B hB hstable).realLattice →
          ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n := by
  let t := ∑ i, bound i
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨l, hl, hlraw, hclear⟩ := M.exists_replicatedFrequency_denominator hM η hη
  have hN := M.squarefreeBasisIndex_card_le p
  have hlexp := replicatedFrequencyDenominator_le_exp t _ d l hp hM.1.1 hN hlraw
  obtain ⟨B, hB, hdiv, hBraw, hstable⟩ := M.exists_squarefree_stable_grid hM l hl
  rw [replicatedIndex_card] at hBraw
  have hbase : squarefreeInputBudget t p ≤ squarefreeFrequencyModelBudget t p :=
    (squarefreeInputBudget_le_frequency t hp).trans (squarefreeFrequencyInputBudget_le_model t hp)
  have hq : 0 ≤ squarefreeFrequencyModelBudget t p := (squarefreeInputBudget_nonneg t hp).trans hbase
  have hdq : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ squarefreeFrequencyModelBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have h8 : (p + 3) ^ 8 ≤ squarefreeFrequencyModelBudget t p :=
    (le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr h8)
  have hGq : (replicatedFrequencyHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyModelBudget t p) :=
    (replicatedFrequencyHeight_ceil_exp d hp hM.1.1).trans (Real.exp_le_exp.mpr
      ((pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 3) (by decide : 4 ≤ 8)).trans h8))
  refine ⟨B, hB, hstable, ?_, ?_, ?_⟩
  · exact M.squarefreeModel_complexity hM B hB hstable hq hdq
      (squarefree_frequency_grid_budget t _ d l B hp hM.1.1 hN hlexp hBraw) hHq
  · intro i
    exact rationalLogHeight_le_of_height (M.replicatedFrequency_finBasis_height hM η hη i) hGq
  · intro z hz
    exact M.squarefreeRealLattice_frequency_integral p η l B hB hstable hdiv hclear z hz

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup
import OAI.Combinatorics.Progressions.Linear.ImageDefiningMatrix
import OAI.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight

namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem basis_repr_height_one (e : Basis ι ℚ L) (i j : ι) :
    RationalHeightLE (e.repr (e i) j) 1 := by
  classical
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact rationalHeightLE_one (by omega)
  · exact rationalHeightLE_zero (by omega)

theorem lie_basis_bracket_height (e : Basis ι ℚ L) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (v : L) (hv : ∀ j, RationalHeightLE (e.repr v j) K) (i k : ι) :
    RationalHeightLE (e.repr ⁅e i, v⁆ k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  classical
  rw [lie_coordinate_formula]
  have h := rationalHeightLE_sum
    (fun ab : ι × ι => lieStructureConstants e ab.1 ab.2 k * e.repr (e i) ab.1 * e.repr v ab.2)
    (fun ab => ((hc ab.1 ab.2 k).mul (basis_repr_height_one e i ab.1)).mul (hv ab.2))
  simpa only [Fintype.card_prod, ← pow_two, mul_one] using h

theorem span_basis_brackets_layer (e : Basis ι ℚ L) (v : κ → L) (n : ℕ)
    (hv : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    Submodule.span ℚ (Set.range (fun ij : ι × κ => ⁅e ij.1, v ij.2⁆)) =
      (LieModule.lowerCentralSeries ℚ L L (n + 1)).toSubmodule := by
  classical
  rw [LieModule.lowerCentralSeries_succ]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    apply LieSubmodule.lie_mem_lie (by simp)
    change v j ∈ (LieModule.lowerCentralSeries ℚ L L n).toSubmodule
    rw [← hv]
    exact Submodule.subset_span ⟨j, rfl⟩
  · rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, y, hy, rfl⟩
    have hy' : y ∈ Submodule.span ℚ (Set.range v) := hv.symm ▸ hy
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hy'
    rw [← e.sum_repr x, ← ht]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(j, i), rfl⟩

omit [Fintype κ] in
theorem exists_small_bounded_spanning_family (e : Basis ι ℚ L) (P : Submodule ℚ L)
    (v : κ → L) (hspan : Submodule.span ℚ (Set.range v) = P) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ w : Fin r → L,
      Submodule.span ℚ (Set.range w) = P ∧
      ∀ i j, RationalHeightLE (e.repr (w i) j) H := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨w, hw, hwspan, _⟩ := hex
  refine ⟨finrank ℚ P, ?_, w, hwspan, ?_⟩
  · simpa only [Module.finrank_eq_card_basis e] using P.finrank_le
  · intro i j
    obtain ⟨a, ha⟩ := hw i
    rw [← ha]
    exact hv a j

theorem exists_bounded_layer_spanning (e : Basis ι ℚ L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ v : Fin r → L,
      Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule ∧
      ∀ i j, RationalHeightLE (e.repr (v i) j) (lieCoordinateHeight (Fintype.card ι) H n) := by
  induction n with
  | zero =>
    apply exists_small_bounded_spanning_family e _ e
    · simp [e.span_eq]
    · intro i j
      exact (basis_repr_height_one e i j).mono (lieCoordinateHeight_pos _ _ _)
  | succ n ih =>
    obtain ⟨r, _, v, hvspan, hv⟩ := ih
    apply exists_small_bounded_spanning_family e _ (fun ij : ι × Fin r => ⁅e ij.1, v ij.2⁆)
    · exact span_basis_brackets_layer e v n hvspan
    · intro ij k
      exact (lie_basis_bracket_height e hc (v ij.2) (hv ij.2) ij.1 k).mono
        (lieCoordinateHeight_step _ _ _)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

def layerRoundingBound (d H l n : ℕ) : ℕ :=
  d * l * lieCoordinateHeight d H n ^ (d * d + 1)

theorem layerRoundingBound_mono_layer (d H l : ℕ) : Monotone (layerRoundingBound d H l) := by
  intro m n hmn
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lieCoordinateHeight_mono_length d H hmn) _)

theorem layerRoundingBound_le_exp (d H l n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    (layerRoundingBound d H l n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 5)) := by
  let t := p + 2
  let a := 3 * n + 2
  have ht : 2 ≤ t := by dsimp [t]; linarith
  have hK := lieCoordinateHeight_le_exp d H n hp hd hH
  have hdim : ((d * d + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
    push_cast
    dsimp [t]
    nlinarith [mul_self_le_mul_self (Nat.cast_nonneg d) hd]
  have hpow : (lieCoordinateHeight d H n : ℝ) ^ (d * d + 1) ≤
      Real.exp (t ^ (a + 2)) := by
    calc
      _ ≤ (Real.exp (t ^ a)) ^ (d * d + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hK _
      _ = Real.exp (((d * d + 1 : ℕ) : ℝ) * t ^ a) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 2 * t ^ a) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdim (by positivity))
      _ = _ := by rw [← pow_add]; congr 2; omega
  have hdp : (d : ℝ) ≤ Real.exp p := hd.trans (by linarith [Real.add_one_le_exp p])
  have hpA : p ≤ t ^ a := le_power_budget hp (by dsimp [a]; omega)
  have htwo : (2 : ℝ) ≤ t ^ 2 := by nlinarith
  have hp2 : 2 * p ≤ t ^ (a + 2) := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left htwo (by positivity : 0 ≤ t ^ a)]
  unfold layerRoundingBound
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp p * Real.exp (t ^ (a + 2)) :=
      mul_le_mul (mul_le_mul hdp hl (by positivity) (by positivity)) hpow
        (by positivity) (by positivity)
    _ = Real.exp (2 * p + t ^ (a + 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ (a + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show a + 3 = (a + 2) + 1 by omega, pow_succ t (a + 2)]
      nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ t ^ (a + 2))]
    _ = _ := by rfl

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_layer_reduction (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) (n : ℕ) :
    ∃ K : Set G, IsCompact K ∧
      (∀ r ∈ K, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l n) ∧
      ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
        ∃ r ∈ K, ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
          (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  obtain ⟨r, hr, v, hspan, hv⟩ := exists_bounded_layer_spanning e hc n
  let B := lieCoordinateHeight (Fintype.card ι) H n
  let m := rationalSpanGridStep e v l
  have hB : 1 ≤ B := lieCoordinateHeight_pos _ _ _
  have hm : m ≤ l * B ^ (Fintype.card ι * Fintype.card ι) := by
    apply (rationalSpanGridStep_le e v l (fun i j => hv j i)).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right hB
    simpa only [Fintype.card_fin] using Nat.mul_le_mul_left (Fintype.card ι) hr
  have hsize : r * m * B ≤ layerRoundingBound (Fintype.card ι) H l n := by
    calc
      _ ≤ Fintype.card ι * (l * B ^ (Fintype.card ι * Fintype.card ι)) * B :=
        Nat.mul_le_mul_right B (Nat.mul_le_mul hr hm)
      _ = _ := by simp [layerRoundingBound, pow_succ, mul_assoc, B]
  refine ⟨(fun x : E => (⟨x⟩ : G)) ''
    boundedSpanCell (fun j => rationalLieInclusion (v j)) (m : ℝ),
    (isCompact_boundedSpanCell _ _).image NilpotentLieBCHGroup.continuous_mk, ?_,
    realification_layer_reduction_in_cell e Γ l hl hinner n v hspan⟩
  rintro _ ⟨x, hx, rfl⟩ i
  have hcoord : ∀ j k, |(e.baseChange ℝ).repr (rationalLieInclusion (v j)) k| ≤ (B : ℝ) := by
    intro j k
    rw [rationalLieInclusion_coordinates]
    exact (hv j k).abs_real_le
  have hb := boundedSpanCell_coordinate_bound (e.baseChange ℝ) _
    (Nat.cast_nonneg m) hcoord hx i
  apply hb.trans
  simpa only [Fintype.card_fin, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hsize

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

theorem exists_bounded_realification_factors (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧
      (∀ r ∈ rs, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤
        layerRoundingBound (Fintype.card ι) H l s) ∧
      ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = rs.prod * γ := by
  let J : ℕ → Subgroup G := fun n => NilpotentLieBCHGroup.subgroup
    (show LieIdeal ℚ E from LieModule.lowerCentralSeries ℚ E E n).toLieSubalgebra
  have hzero : J 0 = ⊤ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E 0) ↔ g ∈ (⊤ : Subgroup G)
    simp
  have hterminal : J s = ⊥ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E s) ↔ g = 1
    rw [realification_lowerCentralSeries_eq_bot hnil, LieSubmodule.mem_bot]
    exact ⟨fun h => NilpotentLieBCHGroup.ext h, fun h => congrArg NilpotentLieBCHGroup.coord h⟩
  apply exists_representative_factors_of_reductions
    (Γ.map NilpotentLieBCHGroup.realificationHom) J s _ hzero hterminal
  intro i hi g hg
  obtain ⟨K, _, hbound, hreduce⟩ := exists_bounded_realification_layer_reduction e Γ l hl hinner hc i
  obtain ⟨r, hr, w, hw, hrem⟩ := hreduce g hg
  refine ⟨r, ?_, w, hw, hrem⟩
  intro k
  exact (hbound r hr k).trans (Nat.cast_le.mpr (layerRoundingBound_mono_layer _ _ _ hi.le))

end Erdos3

end

section

namespace Erdos3

open Module

def lieTreeHeight (d H n : ℕ) : ℕ := (d ^ 2 + H + 2) ^ ((3 * d ^ 2 + 3) ^ n)

theorem lieTreeHeight_ge_input (d H n : ℕ) : H ≤ lieTreeHeight d H n := by
  unfold lieTreeHeight
  have hE : 1 ≤ (3 * d ^ 2 + 3) ^ n := Nat.one_le_pow _ _ (by omega)
  calc
    H ≤ d ^ 2 + H + 2 := by omega
    _ = (d ^ 2 + H + 2) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hE

theorem lieTreeHeight_mono (d H : ℕ) : Monotone (lieTreeHeight d H) := by
  intro i j hij
  unfold lieTreeHeight
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hij)

theorem lieTreeHeight_step (d H n : ℕ) :
    (d ^ 2 + 1) * (H * lieTreeHeight d H n * lieTreeHeight d H n) ^ (d ^ 2) ≤
      lieTreeHeight d H (n + 1) := by
  let A := d ^ 2 + H + 2
  let N := d ^ 2
  let E := (3 * N + 3) ^ n
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hH : H ≤ A := by dsimp [A]; omega
  have hN : N + 1 ≤ A := by dsimp [A, N]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  change (N + 1) * (H * A ^ E * A ^ E) ^ N ≤ A ^ ((3 * N + 3) ^ (n + 1))
  calc
    _ ≤ A * (A * A ^ E * A ^ E) ^ N := by gcongr
    _ = A ^ (1 + (1 + 2 * E) * N) := by
      rw [← pow_succ', ← pow_add, ← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right hA
      rw [pow_succ]
      change 1 + (1 + 2 * E) * N ≤ E * (3 * N + 3)
      nlinarith

theorem lieTreeHeight_le_coordinateHeight (d H n : ℕ) :
    lieTreeHeight d H n ≤ lieCoordinateHeight d H (2 * n) := by
  unfold lieTreeHeight lieCoordinateHeight
  apply Nat.pow_le_pow_right (by omega)
  rw [pow_mul]
  apply Nat.pow_le_pow_left
  nlinarith [sq_nonneg (d : ℤ)]

theorem lieTreeHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieTreeHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (6 * n + 2)) := by
  have h := lieCoordinateHeight_le_exp d H (2 * n) hp hd hH
  have hle : (lieTreeHeight d H n : ℝ) ≤ lieCoordinateHeight d H (2 * n) := by
    exact_mod_cast lieTreeHeight_le_coordinateHeight d H n
  simpa only [show 3 * (2 * n) + 2 = 6 * n + 2 by omega] using hle.trans h

theorem finiteLieTrees_coordinate_height {I ι L : Type*} [Fintype I] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (v : I → L) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H) (n : ℕ)
    (a : FreeMagma I) (ha : a ∈ finiteLieTrees I n) (k : ι) :
    RationalHeightLE (e.repr (lieTreeEval v a) k) (lieTreeHeight (Fintype.card ι) H n) := by
  classical
  induction n generalizing a k with
  | zero => simp only [finiteLieTrees, Finset.notMem_empty] at ha
  | succ n ih =>
    rcases Finset.mem_union.mp ha with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (hv i k).mono (lieTreeHeight_ge_input _ _ _)
    · obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hb, hc'⟩ := Finset.mem_product.mp hbc
      exact (lie_bracket_coordinate_height e hc (lieTreeEval v b) (lieTreeEval v c)
        (fun j => ih b hb j) (fun j => ih c hc' j) k).mono (lieTreeHeight_step _ _ _)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
        ∃ r, (∀ i, |(e.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = r * γ := by
  obtain ⟨C, hC, hprod⟩ := exists_bch_group_product_exp_bound s (3 * s + 5)
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ _ e hnil Γ l H p hl hinner hc hp hd hH hlbound g
  obtain ⟨rs, hlen, hcoords, γ, hγ, heq⟩ := exists_bounded_realification_factors e Γ l hl hinner hc g
  refine ⟨rs.prod, ?_, γ, hγ, heq⟩
  apply hprod (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) rs
  · intro i j k
    exact (realLieBasis_structure e i j k).symm
  · exact hp
  · exact hd
  · exact hlen.le
  · exact hH
  · exact hc
  · intro r hr i
    exact (hcoords r hr i).trans (layerRoundingBound_le_exp _ _ _ _ hp hd hH hlbound)

theorem exists_compact_realification_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ K : Set (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)),
        IsCompact K ∧
        (∀ r ∈ K, ∀ i, |(e.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        ∀ g, ∃ r ∈ K, ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = r * γ := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner hc hp hd hH hlbound
  refine ⟨NilpotentLieBCHGroup.coordinateBox (e.baseChange ℝ) (Real.exp ((p + C) ^ C)),
    NilpotentLieBCHGroup.isCompact_coordinateBox _ _, fun _ hr => hr, ?_⟩
  intro g
  obtain ⟨r, hr, γ, hγ, heq⟩ := hrep e hnil Γ l H p hl hinner hc hp hd hH hlbound g
  exact ⟨r, hr, γ, hγ, heq⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_rational_representatives_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m H : ℕ) (p : ℝ),
      Λ ≤ Γ → 0 < l → 0 < m → bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      scaledIntegerGrid m ⊆ bchSubgroupCoordinates e Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      ∀ g ∈ Γ, ∃ r ∈ Γ, (∀ i, |(e.repr r.coord i : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ γ ∈ Λ, g = r * γ := by
  obtain ⟨C, hC, hreal⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hmb g hg
  obtain ⟨τ, hA, hS, _⟩ := exists_realification_topology_of_grid e Γ l hl houter
  let : TopologicalSpace (ℝ ⊗[ℚ] L) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := hA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] L) := hS
  obtain ⟨r, hr, γR, hγR, heq⟩ :=
    hreal e hnil Λ m H p hm hinner hc hp hd hH hmb (NilpotentLieBCHGroup.realificationHom g)
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hγR
  let rQ := g * γ⁻¹
  have hphi : NilpotentLieBCHGroup.realificationHom rQ = r := by
    rw [map_mul, map_inv, heq]
    group
  refine ⟨rQ, Γ.mul_mem hg (Γ.inv_mem (hΛ hγ)), ?_, γ, hγ, ?_⟩
  · intro i
    have hi := hr i
    rw [← hphi] at hi
    change |(e.baseChange ℝ).equivFun (NilpotentLieBCHGroup.realificationHom rQ).coord i| ≤ _ at hi
    rwa [NilpotentLieBCHGroup.realificationHom_coordinates] at hi
  · dsimp [rQ]
    group

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_subgroup_index_exp_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ Λ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m H : ℕ) (p : ℝ),
      Λ ≤ Γ → 0 < l → 0 < m → bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      scaledIntegerGrid m ⊆ bchSubgroupCoordinates e Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (l : ℝ) ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hrep⟩ := exists_rational_representatives_exp_bound s
  refine ⟨C + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hlb hmb
  let f : NilpotentLieBCHGroup L s hnil → ι → ℚ := fun g => e.equivFun g.coord
  have hf : Function.Injective f := by
    intro x y hxy
    exact NilpotentLieBCHGroup.ext (e.equivFun.injective hxy)
  obtain ⟨hfinite, hindex⟩ := finite_index_of_bounded_grid_representatives f hf Γ Λ l
    ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ hl
    (fun g hg => houter ((bchSubgroupCoordinates_repr e Γ g).mpr hg))
    (Nat.le_ceil _) (hrep e hnil Γ Λ l m H p hΛ hl hm houter hinner hc hp hd hH hmb)
  refine ⟨hfinite, ?_⟩
  apply (Nat.cast_le.mpr hindex).trans
  simpa only [Nat.cast_add, Nat.cast_ofNat] using grid_box_count_le_exp C (Fintype.card ι) l hC hp hd hlb

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_controlled_normal_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ Λ₀ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m₀ H : ℕ) (p : ℝ),
      0 < l → 0 < m₀ → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (l : ℝ) ≤ Real.exp p → (m₀ : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup (NilpotentLieBCHGroup L s hnil),
        Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
        (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
          scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
          bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨C, hC, hindex⟩ := exists_subgroup_index_exp_bound s
  refine ⟨2 * C + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ Λ₀ l m₀ H p hl hm₀ hinner houter htarget hc hp hd hH hlb hm₀b
  let m := l * m₀
  let Λ := subgroupPowerCover Γ m
  let ℓ := m * l
  have hm : 0 < m := Nat.mul_pos hl hm₀
  have hℓ : 0 < ℓ := Nat.mul_pos hm hl
  have hallow : (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) :=
    powerCover_grid_allowance_le_exp l m₀ hp hlb hm₀b
  have hgrid := subgroupPowerCover_grid e Γ l m hinner houter
  have hle : Λ ≤ Γ := subgroupPowerCover_le Γ m
  have hpq : p ≤ (p + 2) ^ 2 := by nlinarith
  have hexp : Real.exp p ≤ Real.exp ((p + 2) ^ 2) := Real.exp_le_exp.mpr hpq
  obtain ⟨hfinite, hidx⟩ := hindex e hnil Γ Λ l ℓ H ((p + 2) ^ 2) hle hl hℓ
    houter hgrid.1 hc (by positivity) (hd.trans hpq) (hH.trans hexp) (hlb.trans hexp) hallow
  refine ⟨Λ, subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget dvd_rfl,
    hle, inferInstance, inferInstance, hfinite, ?_, ℓ, hℓ, hallow, hgrid⟩
  apply hidx.trans
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using quadratic_shift_exp_budget C hp

end Erdos3

end

section

namespace Erdos3

open Module

theorem product_grid_allowance_le_exp {κ : Type*} [Fintype κ] (m : κ → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hm : ∀ i, (m i : ℝ) ≤ Real.exp p) :
    ((∏ i, m i : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  classical
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _i : κ, Real.exp p := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hm i)
    _ = Real.exp ((Fintype.card κ : ℝ) * p) := by rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hκ hp])
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem exists_common_controlled_normal_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
      (Λ₀ : κ → Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (m : κ → ℕ) (p : ℝ),
      0 < l → (∀ i, 0 < m i) → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      (∀ i, scaledIntegerGrid (m i) ⊆ bchSubgroupCoordinates e (Λ₀ i)) →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p → (∀ i, (m i : ℝ) ≤ Real.exp p) →
      ∃ Λ : Subgroup (NilpotentLieBCHGroup L s hnil),
        (∀ i, Λ ≤ Λ₀ i) ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
        (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 8) ∧
          scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
          bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨C, hC, hcover⟩ := exists_controlled_normal_cover s
  refine ⟨2 * C + 5, by omega, ?_⟩
  intro ι κ L _ _ _ _ e hnil Γ Λ₀ l H m p hl hm hinner houter htarget hc hp hd hκ hH hlb hmb
  classical
  let M := ∏ i, m i
  have hM : 0 < M := Finset.prod_pos (fun i _ => hm i)
  have hMgrid : scaledIntegerGrid M ⊆ bchSubgroupCoordinates e (⨅ i, Λ₀ i) := by
    intro x hx
    change (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hnil) ∈ ⨅ i, Λ₀ i
    apply Subgroup.mem_iInf.mpr
    intro i
    exact htarget i (scaledIntegerGrid_subset_of_dvd (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) hx)
  have hpq : p ≤ (p + 2) ^ 2 := by nlinarith
  have hexp : Real.exp p ≤ Real.exp ((p + 2) ^ 2) := Real.exp_le_exp.mpr hpq
  obtain ⟨Λ, hΛ, hΓ, hchar, hnormal, hfinite, hindex, ℓ, hℓ, hℓb, hlow, hupp⟩ :=
    hcover e hnil Γ (⨅ i, Λ₀ i) l M H ((p + 2) ^ 2) hl hM hinner houter hMgrid hc
      (by positivity) (hd.trans hpq) (hH.trans hexp) (hlb.trans hexp)
      (product_grid_allowance_le_exp m hp hκ hmb)
  refine ⟨Λ, fun i => hΛ.trans (iInf_le Λ₀ i), hΓ, hchar, hnormal, hfinite, ?_,
    ℓ, hℓ, ?_, hlow, hupp⟩
  · apply hindex.trans
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using quadratic_shift_exp_budget C hp
  · exact hℓb.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 2 2))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct NNReal

theorem matrixDenominator_allowance_le_exp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (l H : ℕ) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((l * matrixDenominator A : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
  have hD : (matrixDenominator A : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    apply (Nat.cast_le.mpr (matrixDenominator_le A hA)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_mul]
    calc
      (Fintype.card ι : ℝ) * Fintype.card κ * p ≤ (p + 2) * (p + 2) * (p + 2) := by
        gcongr <;> linarith
      _ = (p + 2) ^ 3 := by ring
  rw [Nat.cast_mul]
  calc
    (l : ℝ) * matrixDenominator A ≤ Real.exp p * Real.exp ((p + 2) ^ 3) :=
      mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ 3) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 4) := by
      apply Real.exp_le_exp.mpr
      have hp3 := le_power_budget hp (by decide : 1 ≤ 3)
      nlinarith [mul_nonneg hp (pow_nonneg (by linarith : (0 : ℝ) ≤ p + 2) 3)]

theorem bch_comap_inner_grid {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l : ℕ)
    (hΛ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ) :
    scaledIntegerGrid (l * matrixDenominator (LinearMap.toMatrix e f φ.toLinearMap)) ⊆
      bchSubgroupCoordinates e (Λ.comap (map (hnil := hL) φ)) := by
  rw [bchSubgroupCoordinates_comap e f φ Λ]
  intro x hx
  exact hΛ (matrix_mulVec_fine_grid (LinearMap.toMatrix e f φ.toLinearMap) l hx)

theorem exists_bounded_image_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι κ L M : Type*} [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
      (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates f Λ →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ y : CosetImage (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom),
        ∃ x, projectToCosetImage (realificationMap (hnil := hL) (hM := hM) φ)
            (Λ.map realificationHom) x = y ∧
          ∀ i, |(f.baseChange ℝ).repr (realificationMap (hnil := hL) (hM := hM) φ x).coord i| ≤
            Real.exp ((((p + 2) ^ 4 + C) ^ C) + (p + 2) ^ 2) := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro ι κ L M _ _ _ _ _ _ _ _ _ hL hM e f φ Λ l H p hl hΛ hc hφ hp hι hκ hH hlp y
  classical
  let Γ := Λ.comap (map (hnil := hL) φ)
  let A := LinearMap.toMatrix e f φ.toLinearMap
  let q := l * matrixDenominator A
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    change RationalHeightLE (LinearMap.toMatrix e f φ.toLinearMap i j) H
    rw [LinearMap.toMatrix_apply]
    exact hφ i j
  have hq : 0 < q := Nat.mul_pos hl (matrixDenominator_pos A)
  have hqbound := matrixDenominator_allowance_le_exp A l H hA hp hκ hι hH hlp
  have hp' : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  obtain ⟨g, hg⟩ := projectToCosetImage_surjective
    (realificationMap (hnil := hL) (hM := hM) φ) (Λ.map realificationHom) y
  obtain ⟨r, hr, γ, hγ, heq⟩ := hrep e hL Γ q H ((p + 2) ^ 4) hq
    (bch_comap_inner_grid e f φ Λ l hΛ) hc (by positivity) (hι.trans hp')
    (hH.trans (Real.exp_le_exp.mpr hp')) hqbound g
  have hγmap : realificationMap (hnil := hL) (hM := hM) φ γ ∈ Λ.map realificationHom :=
    realificationMap_subgroup φ Γ Λ le_rfl hγ
  refine ⟨r, ?_, ?_⟩
  · apply Subtype.ext
    have hgy := congrArg Subtype.val hg
    change (QuotientGroup.mk (realificationMap (hnil := hL) (hM := hM) φ g) :
      _ ⧸ Λ.map realificationHom) = y.val at hgy
    rw [← hgy, heq, map_mul]
    exact (quotient_mk_mul_mem (Λ.map realificationHom)
      (realificationMap (hnil := hL) (hM := hM) φ r) ⟨_, hγmap⟩).symm
  · intro i
    have hnorm : ‖(e.baseChange ℝ).equivFun r.coord‖ ≤ Real.exp (((p + 2) ^ 4 + C) ^ C) := by
      apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
      intro j
      simpa only [Basis.equivFun_apply, Real.norm_eq_abs] using hr j
    have hbound := abs_matrix_mulVec_le (fun i j => (A i j : ℝ)) (H : ℝ≥0)
      (fun i j => (hA i j).abs_real_le) ((e.baseChange ℝ).equivFun r.coord) i
    dsimp only [A] at hbound
    rw [baseChange_matrix_apply e f φ.toLinearMap] at hbound
    have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤
        (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) := by
      change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
      gcongr
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    calc
      _ ≤ ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) * ‖(e.baseChange ℝ).equivFun r.coord‖ := hbound
      _ ≤ (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H : ℝ) *
          Real.exp (((p + 2) ^ 4 + C) ^ C) := mul_le_mul hfac hnorm (norm_nonneg _) (NNReal.coe_nonneg _)
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp (((p + 2) ^ 4 + C) ^ C) :=
        mul_le_mul_of_nonneg_right (coordinateLipschitzBound_le_exp _ _ _ hp hκ hι hH) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

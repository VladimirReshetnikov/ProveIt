/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import OAI.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight
import OAI.Combinatorics.Progressions.Linear.FreeLieTruncationKernel

namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

noncomputable def freeLieBoundedCoordinates : FreeLieAlgebra ℚ X →ₗ[ℚ] (BoundedFreeWord X s → ℚ) where
  toFun p w := (freeLieWordExpansion p).coeff w.val
  map_add' p q := by ext w; simp
  map_smul' c p := by ext w; simp

theorem freeLieBoundedCoordinates_eq_zero_iff (p : FreeLieAlgebra ℚ X) :
    freeLieBoundedCoordinates X s p = 0 ↔
      p ∈ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s := by
  rw [freeLie_lowerCentralSeries_iff_low_coeff_zero]
  constructor
  · intro hp w hw
    exact congrFun hp ⟨w, hw⟩
  · intro hp
    ext w
    exact hp w.val w.property

namespace FreeNilpotentLieAlgebra

noncomputable def coordinates : FreeNilpotentLieAlgebra X s →ₗ[ℚ] (BoundedFreeWord X s → ℚ) :=
  (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule.liftQ
    (freeLieBoundedCoordinates X s)
    (fun p hp => (freeLieBoundedCoordinates_eq_zero_iff X s p).mpr hp)

theorem coordinates_mk (p : FreeLieAlgebra ℚ X) :
    coordinates X s (mk X s p) = freeLieBoundedCoordinates X s p := rfl

theorem coordinates_injective : Function.Injective (coordinates X s) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := mk_surjective X s x
  obtain ⟨b, rfl⟩ := mk_surjective X s y
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (mk_eq_zero X s (a - b)).mpr
  apply (freeLieBoundedCoordinates_eq_zero_iff X s (a - b)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

instance finite [Fintype X] : Module.Finite ℚ (FreeNilpotentLieAlgebra X s) :=
  Module.Finite.of_injective (coordinates X s) (coordinates_injective X s)

theorem finrank_le [Fintype X] :
    Module.finrank ℚ (FreeNilpotentLieAlgebra X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have h := LinearMap.finrank_le_finrank_of_injective (coordinates_injective X s)
  calc
    _ ≤ Module.finrank ℚ (BoundedFreeWord X s → ℚ) := h
    _ = Fintype.card (BoundedFreeWord X s) := by simp
    _ ≤ _ := boundedFreeWord_card_le

end FreeNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3

theorem wordTruncation_lie {X : Type*} (s : ℕ) (p q : WordPolynomial X) :
    wordTruncation s ⁅p, q⁆ = wordTruncation s ⁅wordTruncation s p, wordTruncation s q⁆ := by
  simp only [wordPolynomial_lie, map_sub]
  exact congrArg₂ (· - ·) (wordTruncation_mul s p q) (wordTruncation_mul s q p)

namespace FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

noncomputable def expansion : FreeNilpotentLieAlgebra X s →ₗ[ℚ] WordPolynomial X :=
  (LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s).toSubmodule.liftQ
    ((wordTruncation s).comp freeLieWordExpansion.toLinearMap)
    (fun p hp => (wordTruncation_eq_zero_iff s _).mpr
      ((freeLie_lowerCentralSeries_iff_low_coeff_zero s p).mp hp))

theorem expansion_mk (p : FreeLieAlgebra ℚ X) :
    expansion X s (mk X s p) = wordTruncation s (freeLieWordExpansion p) := rfl

theorem expansion_coeff (x : FreeNilpotentLieAlgebra X s) (w : BoundedFreeWord X s) :
    (expansion X s x).coeff w.val = coordinates X s x w := by
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  rw [expansion_mk, wordTruncation_coeff, ite_eq_left w.property]
  rfl

theorem expansion_injective : Function.Injective (expansion X s) := by
  intro x y hxy
  apply coordinates_injective X s
  funext w
  rw [← expansion_coeff, ← expansion_coeff, hxy]

theorem expansion_truncated (x : FreeNilpotentLieAlgebra X s) :
    wordTruncation s (expansion X s x) = expansion X s x := by
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  exact wordTruncation_idempotent s _

theorem expansion_lie (x y : FreeNilpotentLieAlgebra X s) :
    expansion X s ⁅x, y⁆ = wordTruncation s ⁅expansion X s x, expansion X s y⁆ := by
  obtain ⟨a, rfl⟩ := mk_surjective X s x
  obtain ⟨b, rfl⟩ := mk_surjective X s y
  rw [← LieHom.map_lie, expansion_mk, LieHom.map_lie, expansion_mk, expansion_mk]
  exact wordTruncation_lie s _ _

theorem expansion_of (hs : 1 ≤ s) (x : X) :
    expansion X s (of X s x) = MonoidAlgebra.single (FreeSemigroup.of x) 1 := by
  rw [of, expansion_mk, freeLieWordExpansion_of, wordTruncation_single]
  exact ite_eq_left hs

end FreeNilpotentLieAlgebra

end Erdos3

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

variable (X : Type*) (s : ℕ)

theorem mk_tree_eq_zero_of_length_gt (a : FreeMagma X) (ha : s < a.length) :
    mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a) = 0 := by
  apply (mk_eq_zero X s _).mpr
  apply (freeLie_lowerCentralSeries_iff_low_coeff_zero s _).mpr
  intro w hw
  rw [freeLieWordExpansion_tree]
  by_contra h
  have he := commutatorTree_homogeneous a w h
  omega

noncomputable def treeGenerators [Fintype X] : Finset (FreeNilpotentLieAlgebra X s) := by
  classical
  exact ((finiteLieTrees X s).filter (fun a => a.length ≤ s)).image
    (fun a => mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a))

theorem treeGenerators_span [Fintype X] :
    Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := mk_surjective X s x
  apply freeLie_linear_induction
    (fun p => mk X s p ∈ Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s)))
  · simpa only [map_zero] using (Submodule.zero_mem
      (Submodule.span ℚ (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))))
  · intro p q hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro c p hp
    rw [map_smul]
    exact Submodule.smul_mem _ c hp
  · intro a
    by_cases ha : a.length ≤ s
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨mem_finiteLieTrees_of_length_le X a ha, ha⟩, rfl⟩
    · rw [mk_tree_eq_zero_of_length_gt X s a (Nat.lt_of_not_ge ha)]
      exact Submodule.zero_mem _

theorem treeGenerators_card_le [Fintype X] :
    (treeGenerators X s).card ≤ (Fintype.card X + 2) ^ (3 ^ s) := by
  classical
  exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans
    (finiteLieTrees_card_le X s)

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_coordinate_height (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s x w) ((2 * (s + 1)) ^ s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  change RationalHeightLE ((freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val) _
  rw [freeLieWordExpansion_tree]
  exact (commutatorTree_coefficient_height s a w.val w.property).mono
    (Nat.pow_le_pow_right (by omega) (by omega))

theorem treeGenerators_coordinate_integral (x : FreeNilpotentLieAlgebra X s)
    (hx : x ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    ∃ z : ℤ, (z : ℚ) = coordinates X s x w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hlen := (Finset.mem_filter.mp ha).2
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_integral s a w.val w.property
  refine ⟨z, ?_, hbound.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩
  change (z : ℚ) = (freeLieWordExpansion (lieTreeEval (FreeLieAlgebra.of ℚ) a)).coeff w.val
  rwa [freeLieWordExpansion_tree]

theorem exists_bounded_tree_basis :
    ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) ((2 * (s + 1)) ^ s)) ∧
      ∀ i w, ∃ z : ℤ, (z : ℚ) = coordinates X s (b i) w ∧ z.natAbs ≤ (2 * (s + 1)) ^ s := by
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (treeGenerators X s : Set (FreeNilpotentLieAlgebra X s))
  rw [treeGenerators_span, finrank_top] at hex
  obtain ⟨v, hv, hspan, hlin⟩ := hex
  let b := Basis.mk hlin (le_of_eq hspan.symm)
  have hb (i) : b i ∈ treeGenerators X s := by
    simpa only [b, Basis.mk_apply, Finset.mem_coe] using hv i
  exact ⟨b, hb, fun i w => treeGenerators_coordinate_height X s (b i) (hb i) w,
    fun i w => treeGenerators_coordinate_integral X s (b i) (hb i) w⟩

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module

variable {X ι L : Type*} [Fintype X] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s H : ℕ} (e : Basis ι ℚ L) (f : X → L)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

theorem lift_treeGenerator_height
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H)
    (x : FreeNilpotentLieAlgebra X s) (hx : x ∈ treeGenerators X s) (i : ι) :
    RationalHeightLE (e.repr (lift f hnil x) i) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  rw [lift_mk, lift_lieTreeEval]
  exact finiteLieTrees_coordinate_height e f hc hf s a (Finset.mem_filter.mp ha).1 i

theorem lift_basis_matrix_height
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hf : ∀ x i, RationalHeightLE (e.repr (f x) i) H) (i j) :
    RationalHeightLE (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  rw [LinearMap.toMatrix_apply]
  exact lift_treeGenerator_height e f hnil hc hf (b j) (hb j) i

theorem lift_basis_matrix_logHeight
    (b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s))
    (hb : ∀ j, b j ∈ treeGenerators X s) {p : ℝ} (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p)
    (hf : ∀ x i, rationalLogHeight (e.repr (f x) i) ≤ p) (i j) :
    rationalLogHeight (LinearMap.toMatrix b e (lift f hnil).toLinearMap i j) ≤
      (p + 3) ^ (6 * s + 2) := by
  have hraw := lift_basis_matrix_height e f hnil b hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
    (fun x i => rationalHeightLE_ceil_exp (hf x i)) i j
  apply rationalLogHeight_le_of_height hraw
  have h := lieTreeHeight_le_exp (Fintype.card ι) ⌈Real.exp p⌉₊ s
    (p := p + 1) (by linarith) (by linarith) (ceil_exp_le_exp_add_one hp)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3.FreeNilpotentLieAlgebra

open Module
attribute [local instance] LieRing.ofAssociativeRing

variable (X : Type*) [Fintype X] (s : ℕ)

theorem treeGenerators_lie_or_zero {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) :
    ⁅x, y⁆ = 0 ∨ ⁅x, y⁆ ∈ treeGenerators X s := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
  have he : ⁅mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) a),
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) b)⁆ =
      mk X s (lieTreeEval (FreeLieAlgebra.of ℚ) (a * b)) := (LieHom.map_lie _ _ _).symm
  rw [he]
  by_cases hab : (a * b).length ≤ s
  · right
    exact Finset.mem_image.mpr ⟨a * b, Finset.mem_filter.mpr
      ⟨mem_finiteLieTrees_of_length_le X (a * b) hab, hab⟩, rfl⟩
  · exact Or.inl (mk_tree_eq_zero_of_length_gt X s (a * b) (Nat.lt_of_not_ge hab))

theorem treeGenerators_lie_coordinate_height {x y : FreeNilpotentLieAlgebra X s}
    (hx : x ∈ treeGenerators X s) (hy : y ∈ treeGenerators X s) (w : BoundedFreeWord X s) :
    RationalHeightLE (coordinates X s ⁅x, y⁆ w) ((2 * (s + 1)) ^ s) := by
  rcases treeGenerators_lie_or_zero X s hx hy with hzero | hmem
  · rw [hzero, map_zero, Pi.zero_apply]
    have hH : 1 ≤ (2 * (s + 1)) ^ s := one_le_pow₀ (by omega)
    simpa only [RationalHeightLE, Rat.num_zero, Int.natAbs_zero, Rat.den_zero, Nat.zero_le,
      true_and] using hH
  · exact treeGenerators_coordinate_height X s _ hmem w

theorem exists_bounded_structure_basis :
    let n := Fintype.card (BoundedFreeWord X s)
    let d := finrank ℚ (FreeNilpotentLieAlgebra X s)
    let H := (2 * (s + 1)) ^ s
    ∃ b : Basis (Fin d) ℚ (FreeNilpotentLieAlgebra X s),
      (∀ i, b i ∈ treeGenerators X s) ∧
      (∀ i w, RationalHeightLE (coordinates X s (b i) w) H) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        ((n + 1) * (rationalSolveHeight d H * H) ^ n) := by
  dsimp only
  obtain ⟨b, hb, hcoord, _⟩ := exists_bounded_tree_basis X s
  refine ⟨b, hb, hcoord, ?_⟩
  intro i j k
  have h := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (coordinates X s) (coordinates_injective X s)
    (show 1 ≤ (2 * (s + 1)) ^ s from one_le_pow₀ (by omega))
    (fun w l => by simpa only [Pi.basisFun_repr] using hcoord l w)
    ⁅b i, b j⁆ (fun w => by simpa only [Pi.basisFun_repr] using
      treeGenerators_lie_coordinate_height X s (hb i) (hb j) w) k
  simpa only [Fintype.card_fin, lieStructureConstants] using h

end Erdos3.FreeNilpotentLieAlgebra

end

section

namespace Erdos3

open Module

theorem exists_bounded_free_nilpotent_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i w, rationalLogHeight (FreeNilpotentLieAlgebra.coordinates X s (b i) w) ≤ (p + C) ^ C) ∧
        ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C := by
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.C H + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let A := ((s : ℝ) + 1) * (p + 1) ^ s
  let T := A + (H : ℝ) + p + 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAT : A ≤ T := by
    exact (le_add_of_nonneg_right (Nat.cast_nonneg H)).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hT : 0 ≤ T := hA.trans hAT
  have hHT : (H : ℝ) ≤ T := by
    exact (le_add_of_nonneg_left hA).trans
      ((le_add_of_nonneg_right hp).trans (le_add_of_nonneg_right (by norm_num)))
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, A, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hBC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  have hsize : ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ A :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (1 : ℝ))) s) (by positivity)
  have hn : (Fintype.card (BoundedFreeWord X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (boundedFreeWord_card_le (X := X) (s := s))
      _ ≤ _ := hsize
  have hd : (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ A := by
    calc
      _ ≤ ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s := by
        exact_mod_cast (FreeNilpotentLieAlgebra.finrank_le X s)
      _ ≤ _ := hsize
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  obtain ⟨b, hb, hcoord, hstructure⟩ := FreeNilpotentLieAlgebra.exists_bounded_structure_basis X s
  refine ⟨hd.trans (hAT.trans hTC), hn.trans (hAT.trans hTC), b, hb, ?_, ?_⟩
  · intro i w
    exact rationalLogHeight_le_of_height (hcoord i w)
      (hHexp.trans (Real.exp_le_exp.mpr hTC))
  · intro i j k
    have hcost := embedding_coordinate_height_budget
      (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
      hT (hn.trans hAT) (hd.trans hAT) hHexp hHexp
    exact rationalLogHeight_le_of_height (hstructure i j k)
      (hcost.trans (Real.exp_le_exp.mpr hBC))

end Erdos3

end

section

namespace Erdos3

open Module
attribute [local instance] LieRing.ofAssociativeRing

theorem exists_free_nilpotent_source_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (X : Type*) [Fintype X] (p : ℝ),
      0 ≤ p → (Fintype.card X : ℝ) ≤ p →
      (finrank ℚ (FreeNilpotentLieAlgebra X s) : ℝ) ≤ (p + C) ^ C ∧
      ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ (p + C) ^ C ∧
      ∃ b : Basis (Fin (finrank ℚ (FreeNilpotentLieAlgebra X s))) ℚ (FreeNilpotentLieAlgebra X s),
        (∀ i, b i ∈ FreeNilpotentLieAlgebra.treeGenerators X s) ∧
        (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + C) ^ C) ∧
        ∀ x ∈ FreeNilpotentLieAlgebra.treeGenerators X s, ∀ i,
          rationalLogHeight (b.repr x i) ≤ (p + C) ^ C := by
  obtain ⟨a, _, hmodel⟩ := exists_bounded_free_nilpotent_model s
  let H := (2 * (s + 1)) ^ s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + 2) ^ (3 ^ s) + Polynomial.C H + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 8)
  refine ⟨C, hC, ?_⟩
  intro X _ p hp hX
  let B := (p + a) ^ a
  let V := (p + 2) ^ (3 ^ s)
  let T := B + V + (H : ℝ) + 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hBT : B ≤ T := by
    exact (le_add_of_nonneg_right hV).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hVT : V ≤ T := by
    exact (le_add_of_nonneg_left hB).trans
      ((le_add_of_nonneg_right (Nat.cast_nonneg H)).trans (le_add_of_nonneg_right (by norm_num)))
  have hHT : (H : ℝ) ≤ T :=
    (le_add_of_nonneg_left (add_nonneg hB hV)).trans (le_add_of_nonneg_right (by norm_num))
  have hT : 0 ≤ T := hB.trans hBT
  have hsum : T + (T + 2) ^ 8 ≤ (p + C) ^ C := by
    simpa [Q, T, B, V, Polynomial.eval₂_pow] using hbudget p hp
  have hTC : T ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (T + 2) ^ 8)).trans hsum
  have hPC : (T + 2) ^ 8 ≤ (p + C) ^ C := (le_add_of_nonneg_left hT).trans hsum
  obtain ⟨hd, hn, b, hb, _, hstructure⟩ := hmodel X p hp hX
  have hgen : ((FreeNilpotentLieAlgebra.treeGenerators X s).card : ℝ) ≤ V := by
    calc
      _ ≤ ((Fintype.card X : ℝ) + 2) ^ (3 ^ s) := by
        exact_mod_cast FreeNilpotentLieAlgebra.treeGenerators_card_le X s
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (add_le_add hX (le_refl (2 : ℝ))) _
  have hHexp : (H : ℝ) ≤ Real.exp T := hHT.trans
    ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp T))
  refine ⟨hd.trans (hBT.trans hTC), hgen.trans (hVT.trans hTC), b, hb,
    fun i j k => (hstructure i j k).trans (hBT.trans hTC), ?_⟩
  intro x hx i
  have hraw := embedding_basis_coordinate_height b (Pi.basisFun ℚ (BoundedFreeWord X s))
    (FreeNilpotentLieAlgebra.coordinates X s) (FreeNilpotentLieAlgebra.coordinates_injective X s)
    (show 1 ≤ H from one_le_pow₀ (by omega))
    (fun w j => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s (b j) (hb j) w)
    x (fun w => by simpa only [Pi.basisFun_repr] using
      FreeNilpotentLieAlgebra.treeGenerators_coordinate_height X s x hx w) i
  have hcost := embedding_coordinate_height_budget
    (Fintype.card (BoundedFreeWord X s)) (finrank ℚ (FreeNilpotentLieAlgebra X s)) H H
    hT (hn.trans hBT) (hd.trans hBT) hHexp hHexp
  apply rationalLogHeight_le_of_height hraw
  simpa only [Fintype.card_fin] using hcost.trans (Real.exp_le_exp.mpr hPC)

end Erdos3

end

end OAI

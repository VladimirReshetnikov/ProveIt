import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import OAI.Combinatorics.Progressions.Estimates.ControlledProductReconstruction
import OAI.Combinatorics.Progressions.Estimates.ReplicatedLieAction
import OAI.Combinatorics.Progressions.Linear.AdaptedBasisGeometry

namespace OAI

section

namespace Erdos3

theorem rationalLogHeight_le_iff (q : ℚ) (p : ℝ) :
    rationalLogHeight q ≤ p ↔
      (q.num.natAbs : ℝ) ≤ Real.exp p ∧ (q.den : ℝ) ≤ Real.exp p := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [rationalLogHeight, Real.log_le_iff_le_exp (lt_of_lt_of_le hd (le_max_right _ _)), max_le_iff]

theorem rationalLogHeight_nonneg (q : ℚ) : 0 ≤ rationalLogHeight q := by
  apply Real.log_nonneg
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  exact hd.trans (le_max_right _ _)

theorem rationalHeightLE_ceil_exp {q : ℚ} {p : ℝ} (h : rationalLogHeight q ≤ p) :
    RationalHeightLE q ⌈Real.exp p⌉₊ := by
  obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff q p).mp h
  exact ⟨Nat.cast_le.mp (hn.trans (Nat.le_ceil _)), Nat.cast_le.mp (hd.trans (Nat.le_ceil _))⟩

theorem rationalLogHeight_le_of_height {q : ℚ} {H : ℕ} {p : ℝ}
    (hq : RationalHeightLE q H) (hH : (H : ℝ) ≤ Real.exp p) :
    rationalLogHeight q ≤ p :=
  (rationalLogHeight_le_iff q p).mpr
    ⟨(Nat.cast_le.mpr hq.1).trans hH, (Nat.cast_le.mpr hq.2).trans hH⟩

theorem one_le_ceil_exp (p : ℝ) : 1 ≤ ⌈Real.exp p⌉₊ :=
  Nat.one_le_ceil_iff.mpr (Real.exp_pos p)

theorem ceil_exp_le_exp_add_one {p : ℝ} (hp : 0 ≤ p) :
    (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (p + 1) := by
  have h1 : 1 ≤ Real.exp p := by simpa using Real.exp_le_exp.mpr hp
  calc
    _ ≤ Real.exp p + 1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ ≤ 2 * Real.exp p := by linarith
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos p).le
    _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis_logHeight {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hv : ∀ i j k, rationalLogHeight (e.repr (v i j : L) k) ≤ p)
    (hc : ∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (e.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (e i) j) ≤ (p + 3) ^ 5) ∧
      ∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := hp.trans (le_add_of_nonneg_right zero_le_one)
  have hd1 : (Fintype.card ι : ℝ) ≤ p + 1 := hd.trans (le_add_of_nonneg_right zero_le_one)
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd1
  obtain ⟨b, w, hw, hbound, hcentral, hb, hlayer⟩ :=
    F.exists_bounded_sorted_adapted_basis e v hspan
      (fun i j k => rationalHeightLE_ceil_exp (hv i j k))
  have hinverse := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  refine ⟨b, w, hw, hbound, hcentral, hlayer,
    fun j i => rationalLogHeight_le_of_height (hb j i) hHp, ?_, ?_⟩
  · intro i j
    apply rationalLogHeight_le_of_height (hinverse i j)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalSolveHeight_le_budget (Fintype.card (Fin (finrank ℚ L))) H hp1 hr hHp
  · intro i j k
    apply rationalLogHeight_le_of_height (hstructure i j k)
    simpa only [show p + 1 + 2 = p + 3 by ring] using
      rationalLieStructureHeight_inverse_budget (Fintype.card ι)
        (Fintype.card (Fin (finrank ℚ L))) H hp1 hd1 hr hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

noncomputable def boundedRationalCandidates (H : ℕ) : Finset ℚ := by
  classical
  exact ((Finset.Icc (-(H : ℤ)) H) ×ˢ Finset.range (H + 1)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ) / z.2)

theorem mem_boundedRationalCandidates {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    q ∈ boundedRationalCandidates H := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(q.num, q.den), Finset.mem_product.mpr ⟨?_, ?_⟩, Rat.num_div_den q⟩
  · apply Finset.mem_Icc.mpr
    have hn : |q.num| ≤ (H : ℤ) := by
      simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hq.1)
    exact abs_le.mp hn
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq.2)

theorem boundedRationalCandidates_card (H : ℕ) :
    (boundedRationalCandidates H).card ≤ (2 * H + 1) * (H + 1) := by
  classical
  have hcard : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    omega
  exact Finset.card_image_le.trans (by rw [Finset.card_product, hcard, Finset.card_range])

theorem finite_card_bounded_height_arrays {ι : Type*} [Fintype ι]
    (S : Set (ι → ℚ)) (H : ℕ) (hS : ∀ x ∈ S, ∀ i, RationalHeightLE (x i) H) :
    S.Finite ∧ S.ncard ≤ ((2 * H + 1) * (H + 1)) ^ Fintype.card ι := by
  classical
  let f : S → (ι → ↥(boundedRationalCandidates H)) :=
    fun x i => ⟨x.val i, mem_boundedRationalCandidates (hS x x.property i)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  let : Finite S := Finite.of_injective f hf
  have hc := Nat.card_le_card_of_injective f hf
  have hb := Nat.pow_le_pow_left (boundedRationalCandidates_card H) (Fintype.card ι)
  refine ⟨Set.toFinite S, ?_⟩
  have hbound : S.ncard ≤ (boundedRationalCandidates H).card ^ Fintype.card ι := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_coe] using hc
  exact hbound.trans hb

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_normalized_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℚ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ r : VectorPolynomial σ ℚ D.filtration.realification.squareLieSubalgebra,
          D.filtration.realification.squareFiltration.Adapted w r ∧
          VectorPolynomial.map D.filtration.realification.squareFst.toLinearMap r =
            normalizedShiftLog s h (-ε.coord) (-γ.coord) f.log ∧
          VectorPolynomial.map D.filtration.realification.squareSnd.toLinearMap r = f.log := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  let H := ⌈Real.exp p⌉₊
  let u : D.RealGroup := ⟨eval h f.log⟩
  let v : D.RealGroup := ⟨eval (fun _ => 0) f.log⟩
  obtain ⟨ε, hε, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice D.grid H (p + 1) D.grid_pos D.inner_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) (u * v⁻¹)
  refine ⟨ε, γ, hγ, hε, ?_⟩
  exact D.filtration.realification.exists_normalized_shift_square w hw h (-ε.coord) (-γ.coord)
    f.log f.adapted (D.filtration.realification.normalizedShift_horizontal_zero h f.log ε γ heq)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem rational_functional_value_logHeight {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (eta : V →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (heta : ∀ i, rationalLogHeight (eta (b i)) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (b.repr x i) ≤ p) :
    rationalLogHeight (eta x) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hterms (i) : RationalHeightLE (b.repr x i * eta (b i)) (H * H) :=
    (rationalHeightLE_ceil_exp (hx i)).mul (rationalHeightLE_ceil_exp (heta i))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have he : eta x = ∑ i, b.repr x i * eta (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  apply rationalLogHeight_le_of_height (rationalHeightLE_sum _ hterms)
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hι.trans (show p ≤ p + 2 by linarith))

end Erdos3

end

section

namespace Erdos3

open Module

theorem linearMap_coordinate_logHeight
    {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] [Fintype ι]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hT : ∀ i j, rationalLogHeight (f.repr (T (e i)) j) ≤ p)
    (x : V) (hx : ∀ i, rationalLogHeight (e.repr x i) ≤ p) (j : κ) :
    rationalLogHeight (f.repr (T x) j) ≤ (p + 2) ^ 4 := by
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) :=
        mul_le_mul hH hH (Nat.cast_nonneg H) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  have hraw := linearMap_coordinate_height e f T
    (fun i j => rationalHeightLE_ceil_exp (hT i j)) x
    (fun i => rationalHeightLE_ceil_exp (hx i)) j
  apply rationalLogHeight_le_of_height hraw
  exact rational_sum_cost_le_exp (Fintype.card ι) (H * H) hp 2 1 hHH
    (by simpa only [pow_one] using hn.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_layer_basis (a : σ → ℕ) (ha : a ≤ bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  let a' : ∀ i, Fin (bound i + 1) := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
  exact ⟨M.basis a', hM.2 a'⟩

theorem exists_ordinary_layer_basis (n : Fin (s + 1)) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.ordinary.layer (n.val + 1)))) ℚ
        (M.filtration.ordinary.layer (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  rw [M.ordinary]
  exact ⟨D.layerBasis n, hM.1.2.2.2 n⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_positive_layer_basis (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hms : m < s + 1
  · exact ⟨D.layerBasis ⟨m, hms⟩, hD.2.2.2 ⟨m, hms⟩⟩
  · have hzero : D.filtration.layer (m + 1) = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (by omega : s + 1 ≤ m + 1)).trans_eq D.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (D.filtration.layer (m + 1))
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hzero, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg d).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

theorem exists_native_complex_reconstruction (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      (E.realLattice ⊓ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
        D.realLattice.map (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) →
      ∀ (u : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
      (letI := D.metricSpace; LipschitzWith ℓ u) → (∀ x, ‖u x‖ ≤ 1) →
      (∀ k ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ).ker, ∀ x,
        u (QuotientGroup.mk (k * x)) = u (QuotientGroup.mk x)) →
      ∃ (v : E.Space → ℂ) (K : ℝ≥0),
        (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (letI := E.metricSpace; LipschitzWith K v) ∧
        (∀ y, ‖v y‖ ≤ 2) ∧
        ∀ x, v (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) = u (QuotientGroup.mk x) := by
  obtain ⟨c, _, hrec⟩ := exists_controlled_rational_image_reconstruction s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ hcover u ℓ hℓ hu hub hker
  have ht : 0 ≤ p + 1 := by linarith
  have hpt : p ≤ p + 1 := by linarith
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr hpt
  obtain ⟨v, K, hK, hv, hb, heval⟩ := hrec D.filtration.lowerCentralSeries_eq_bot
    E.filtration.lowerCentralSeries_eq_bot D.basis E.basis φ D.lattice E.lattice
    D.grid E.grid ⌈Real.exp p⌉₊ D.grid_pos E.grid_pos (one_le_ceil_exp p)
    D.outer_grid E.inner_grid E.outer_grid
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
    (fun i j => rationalHeightLE_ceil_exp (hφ i j)) hcover u hker ℓ 1 hu hub
    (p + 1) ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt)
    (ceil_exp_le_exp_add_one hp) (hE.2.1.trans hexp) (hℓ.trans hexp)
    (by simpa only [NNReal.coe_one] using Real.one_le_exp ht)
  have hcost : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hcost), hv,
    fun y => by simpa only [NNReal.coe_one, mul_one] using hb y, heval⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem RationalHeightLE.pow {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (n : ℕ) :
    RationalHeightLE (q ^ n) (H ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using rationalHeightLE_one (by decide : 1 ≤ 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hq

theorem ceil_exp_power_le_exp {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    ((⌈Real.exp p⌉₊ ^ n : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * (p + 1)) := by
  rw [Nat.cast_pow, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (ceil_exp_le_exp_add_one hp) n

end Erdos3

end

end OAI

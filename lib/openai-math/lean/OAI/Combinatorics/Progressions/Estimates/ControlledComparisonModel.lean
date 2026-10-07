import OAI.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
import OAI.Combinatorics.Progressions.Lattices.ComparisonLattice
import OAI.Combinatorics.Progressions.Linear.ScaledPairBasisHeight

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L K : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  {s t d r : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem exists_model_of_bounded_embedding (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j k, RationalHeightLE (D.basis.repr (φ (b j)) k) H)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin r) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis φ.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_of_steps
    (hM := F.lowerCentralSeries_eq_bot) b D.basis φ hφ D.lattice hH D.grid_pos
    hmatrix D.inner_grid D.outer_grid hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis φ hφ hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d r H hp hd hr hHp
  choose a ha using hlayers
  have hLayer (n : Fin (t + 1)) (j) (k) :
      rationalLogHeight (b.repr (a n j : K) k) ≤ (p + 2) ^ 8 := by
    apply rationalLogHeight_le_of_height
      (embedding_basis_coordinate_height b D.basis φ.toLinearMap hφ hH
        (fun i j => hb j i) (a n j : K) (ha n j) k)
    simpa only [Fintype.card_fin] using
      embedding_coordinate_height_budget d r H H hp hd hr hHp hHp
  let E : RationalFilteredNilmanifold K t r :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · exact fun n j k => (hLayer n j k).trans h8

include D in
theorem embedding_basis_card_le (b : Basis (Fin r) ℚ K)
    (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) : r ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hφ
  simpa only [finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin] using h

theorem exists_model_of_embedding_logHeight (F : NilpotentLieFiltration K t)
    (b : Basis (Fin r) ℚ K) (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    {p : ℝ} (hD : D.GeometryComplexityLE p)
    (hb : ∀ j k, rationalLogHeight (D.basis.repr (φ (b j)) k) ≤ p)
    (hlayers : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (D.basis.repr (φ (a j : K)) k) ≤ p) :
    ∃ E : RationalFilteredNilmanifold K t r,
      E.filtration = F ∧ E.basis = b ∧
      E.lattice = D.lattice.comap (NilpotentLieBCHGroup.mapOfSteps φ) ∧
      E.GeometryComplexityLE ((p + 3) ^ 11) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  have hr : (r : ℝ) ≤ p := (Nat.cast_le.mpr (D.embedding_basis_card_le b φ hφ)).trans hD.1
  have hLayer : ∀ n : Fin (t + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, RationalHeightLE (D.basis.repr (φ (a j : K)) k) ⌈Real.exp p⌉₊ := by
    intro n
    obtain ⟨a, ha⟩ := hlayers n
    exact ⟨a, fun j k => rationalHeightLE_ceil_exp (ha j k)⟩
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := D.exists_model_of_bounded_embedding F b φ hφ
    (one_le_ceil_exp p) (fun j k => rationalHeightLE_ceil_exp (hb j k)) hLayer
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    (by linarith : 0 ≤ p + 1) (hD.1.trans (by linarith)) (hr.trans (by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨E, hEF, hEb, hEL, ?_⟩
  convert hE using 1
  ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_layer_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.dilationPairLayer q n))) ℚ
        (D.filtration.dilationPairLayer q n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  obtain ⟨a, ha⟩ := D.exists_positive_layer_basis (n + 1) (by omega) hD
  obtain ⟨b, hb⟩ := D.exists_positive_layer_basis n hn hD
  obtain ⟨c, hc⟩ := exists_scaledPair_basis_height D.basis
    (D.filtration.layer n) (D.filtration.layer (n + 1)) (D.filtration.antitone (Nat.le_succ n))
    a b (q ^ n) hH (one_le_pow₀ hH) ((rationalHeightLE_ceil_exp hq).pow n)
    (fun j k => rationalHeightLE_ceil_exp (ha j k))
    (fun j k => rationalHeightLE_ceil_exp (hb j k))
  have hbound : ((H * H ^ n : ℕ) : ℝ) ≤ Real.exp ((n + 1 : ℝ) * (p + 1)) := by
    rw [← pow_succ']
    simpa only [Nat.cast_add, Nat.cast_one] using ceil_exp_power_le_exp hp (n + 1)
  exact ⟨c, fun j k => ⟨rationalLogHeight_le_of_height (hc j k).1 hbound,
    rationalLogHeight_le_of_height (hc j k).2 hbound⟩⟩

theorem exists_dilationPair_filtration_basis (q : ℚ) (n : ℕ) (hn : 1 ≤ n)
    {p : ℝ} (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ b : Basis (Fin (finrank ℚ ((D.filtration.dilationPairFiltration q).layer n))) ℚ
        ((D.filtration.dilationPairFiltration q).layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j).val.val.1 k) ≤ (n + 1 : ℝ) * (p + 1) ∧
        rationalLogHeight (D.basis.repr (b j).val.val.2 k) ≤ (n + 1 : ℝ) * (p + 1) := by
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q n hn hD hq
  let e := D.filtration.dilationPairFiltrationLayerEquiv q n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) :
      ((c j : D.filtration.dilationPairSubalgebra q) : L × L) =
        (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      NilpotentLieFiltration.dilationPairFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def pairToPi : (L × L) →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  liePiMap ![LieHom.fst ℚ L L, LieHom.snd ℚ L L]

@[simp] theorem pairToPi_zero (x : L × L) : pairToPi x 0 = x.1 := rfl

@[simp] theorem pairToPi_one (x : L × L) : pairToPi x 1 = x.2 := rfl

theorem pairToPi_injective : Function.Injective (pairToPi (L := L)) := by
  intro x y h
  exact Prod.ext (congrFun h 0) (congrFun h 1)

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

def dilationPairToPi (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ (Fin 2 → L) :=
  pairToPi.comp (F.dilationPairSubalgebra q).incl

theorem dilationPairToPi_injective (q : ℚ) : Function.Injective (F.dilationPairToPi q) :=
  fun _ _ h => Subtype.ext (pairToPi_injective h)

theorem dilationPairToPi_mem (q : ℚ) {n : ℕ} {x : F.dilationPairSubalgebra q}
    (hx : x ∈ (F.dilationPairFiltration q).layer n) :
    F.dilationPairToPi q x ∈ (pi (fun _ : Fin 2 => F)).layer n := by
  apply (mem_pi_layer _ _ _).mpr
  intro i
  fin_cases i
  · exact hx.1
  · exact hx.2.1

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem pair_product_basis_logHeight (x : L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 2, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr (pairToPi x) k) ≤ p := by
  have h (j : Fin 2) (l : Fin d) : rationalLogHeight (D.basis.repr (pairToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2
  rw [productFinBasis_repr]
  exact h _ _

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def dilationPairLattice (q : ℚ) : Subgroup (D.filtration.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (D.filtration.dilationPairToPi q))

theorem dilationPairLattice_mem (q : ℚ) (x : (D.filtration.dilationPairFiltration q).Group) :
    x ∈ D.dilationPairLattice q ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (D.filtration.dilationPairToPi q) x) ∈
    piBCHSubgroup (fun _ : Fin 2 => D.filtration) (fun _ : Fin 2 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h i
    fin_cases i
    · exact h.1
    · exact h.2

noncomputable def dilationPairGeometryBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + 4) ^ 2 + (s + 2) * (p + 1) + 6) ^ 11

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (D.filtration.dilationPairSubalgebra q) s
        (finrank ℚ (D.filtration.dilationPairSubalgebra q)),
      E.filtration = D.filtration.dilationPairFiltration q ∧
      E.lattice = D.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (D.filtration.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hD.1
  let P := pi (fun _ : Fin 2 => D)
  let K := D.filtration.dilationPairSubalgebra q
  let F := D.filtration.dilationPairFiltration q
  let φ := D.filtration.dilationPairToPi q
  let C : ℝ := (s + 2) * (p + 1)
  let R : ℝ := (p + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + 4)]
  have hP : P.GeometryComplexityLE R := by
    have hh := pi_geometry (fun _ : Fin 2 => D) (by linarith : 0 ≤ p + 2)
      (by simpa using (show (2 : ℝ) ≤ p + 2 by linarith))
      (fun _ => hD.mono D (by linarith : p ≤ p + 2))
    have hgeom : P.GeometryComplexityLE ((p + 4) ^ 2) := by
      simpa only [show p + 2 + 2 = p + 4 by ring] using hh
    exact hgeom.mono P (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := D.exists_dilationPair_layer_basis q 1 (by decide) hD hq
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbase : 2 * (p + 1) ≤ C := by
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ p + 1)
    exact le_add_of_nonneg_left (Nat.cast_nonneg s)
  have hbK (j) (k) : rationalLogHeight (P.basis.repr (φ (bK j)) k) ≤ R := by
    apply D.pair_product_basis_logHeight
    intro l
    have hh := hb j l
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact ⟨hh.1.trans (hbase.trans hCR), hh.2.trans (hbase.trans hCR)⟩
  have hlayers (n : Fin (s + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight (P.basis.repr (φ (a j)) k) ≤ R := by
    obtain ⟨a, ha⟩ := D.exists_dilationPair_filtration_basis q (n.val + 1) (by omega) hD hq
    refine ⟨a, fun j k => ?_⟩
    have hn : ((n.val + 1 : ℕ) + 1 : ℝ) ≤ (s + 2 : ℝ) := by
      exact_mod_cast (show n.val + 1 + 1 ≤ s + 2 by omega)
    have hbound := mul_le_mul_of_nonneg_right hn (show 0 ≤ p + 1 by linarith)
    apply D.pair_product_basis_logHeight
    intro l
    exact ⟨(ha j l).1.trans (hbound.trans hCR), (ha j l).2.trans (hbound.trans hCR)⟩
  have hφ := D.filtration.dilationPairToPi_injective q
  obtain ⟨E, hEF, hEb, hEL, hE⟩ := P.exists_model_of_embedding_logHeight F bK φ hφ hP hbK hlayers
  have hdim : finrank ℚ K ≤ 2 * d := by
    have hh := P.embedding_basis_card_le bK φ hφ
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hh
  refine ⟨E, hEF, hEL, ?_, hdim, ?_⟩
  · simpa only [R, C, dilationPairGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hE
  · intro j k
    rw [hEb]
    have hh := hb j k
    norm_num only [Nat.cast_one, one_add_one_eq_two] at hh
    exact hh

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_dilationPair_model_of_eq (F : NilpotentLieFiltration L s)
    (hF : F = D.filtration) (q : ℚ) {p : ℝ}
    (hD : D.GeometryComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (F.dilationPairSubalgebra q) s
        (finrank ℚ (F.dilationPairSubalgebra q)),
      E.filtration = F.dilationPairFiltration q ∧
      E.lattice = (pi (fun _ : Fin 2 => D)).lattice.comap
        (NilpotentLieBCHGroup.mapOfSteps (F.dilationPairToPi q)) ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (F.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) := by
  subst F
  exact D.exists_dilationPair_model q hD hq

namespace MultidegreeStructure

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ}
  {D : RationalFilteredNilmanifold L s d} (M : D.MultidegreeStructure bound)

noncomputable def dilationPairLattice (q : ℚ) :
    Subgroup (M.filtration.ordinary.dilationPairFiltration q).Group :=
  (pi (fun _ : Fin 2 => D)).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q))

theorem dilationPairLattice_mem (q : ℚ)
    (x : (M.filtration.ordinary.dilationPairFiltration q).Group) :
    x ∈ M.dilationPairLattice q ↔
      (⟨x.coord.val.1⟩ : D.filtration.Group) ∈ D.lattice ∧
      (⟨x.coord.val.2⟩ : D.filtration.Group) ∈ D.lattice := by
  change (NilpotentLieBCHGroup.mapOfSteps (M.filtration.ordinary.dilationPairToPi q) x) ∈
    piBCHSubgroup (fun _ : Fin 2 => D.filtration) (fun _ : Fin 2 => D.lattice) ↔ _
  rw [mem_piBCHSubgroup]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

theorem exists_dilationPair_model (q : ℚ) {p : ℝ}
    (hM : M.ComplexityLE p) (hq : rationalLogHeight q ≤ p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra q) s
        (finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q)),
      E.filtration = M.filtration.ordinary.dilationPairFiltration q ∧
      E.lattice = M.dilationPairLattice q ∧
      E.GeometryComplexityLE (dilationPairGeometryBudget s p) ∧
      finrank ℚ (M.filtration.ordinary.dilationPairSubalgebra q) ≤ 2 * d ∧
      ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ 2 * (p + 1) ∧
        rationalLogHeight (D.basis.repr (E.basis j).val.2 k) ≤ 2 * (p + 1) :=
  D.exists_dilationPair_model_of_eq M.filtration.ordinary M.ordinary q hM.1 hq

end MultidegreeStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_comparison_layer_basis {p : ℝ} (hM : M.ComplexityLE p) (n : ℕ) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n))) ℚ
        (M.filtration.comparisonLayer (fun i : ReplicatedIndex bound => i.1) n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis_height hM n
  exact ⟨b, fun j k => rationalLogHeight_le_of_height (hb j k)
    (comparisonBasisHeight_le_exp bound hp)⟩

theorem exists_comparison_filtration_basis {p : ℝ} (hM : M.ComplexityLE p)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ b : Basis (Fin (finrank ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n))) ℚ
        ((M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).layer n),
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (b j).val.val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM n
  let e := M.filtration.comparisonFiltrationLayerEquiv
    (fun i : ReplicatedIndex bound => i.1) n hn
  let c := (b.map e.symm).reindex (finCongr e.finrank_eq.symm)
  have hval (j) : (c j).val.val = (b ((finCongr e.finrank_eq.symm).symm j)).val := by
    simp only [c, Basis.reindex_apply, Basis.map_apply, e,
      MultidegreeLieFiltration.comparisonFiltrationLayerEquiv]
    rfl
  refine ⟨c, fun j k => ?_⟩
  rw [hval]
  exact hb _ k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonGeometryBudget (t : ℕ) (p q : ℝ) : ℝ :=
  ((p + q + 4) ^ 2 + comparisonBasisBudget t p + 6) ^ 11

theorem comparisonSubalgebra_finrank_le (p : ℝ) :
    finrank ℚ (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1)) ≤
      (2 ^ (∑ i, bound i) + 1) * d := by
  have hdim : finrank ℚ
      (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1)) ≤
        d + Fintype.card M.SquarefreeBasisIndex := by
    have h := lie_subalgebra_finrank_le (D.basis.prod (M.squarefreeFinBasis p))
      (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    simpa only [Fintype.card_sum, Fintype.card_fin] using h
  have hcard := M.squarefreeBasisIndex_card_le p
  calc
    _ ≤ d + Fintype.card M.SquarefreeBasisIndex := hdim
    _ ≤ d + 2 ^ (∑ i, bound i) * d := Nat.add_le_add_left hcard d
    _ = _ := by ring

theorem exists_comparison_model {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q) :
    ∃ E : RationalFilteredNilmanifold
        (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
        (max s (Fintype.card (ReplicatedIndex bound)))
        (finrank ℚ (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))),
      E.filtration = M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1) ∧
      E.lattice = M.comparisonLattice p B hB hstable ∧
      E.GeometryComplexityLE (comparisonGeometryBudget (∑ i, bound i) p q) ∧
      ∀ j k, rationalLogHeight
        ((D.basis.prod (M.squarefreeFinBasis p)).repr (E.basis j).val k) ≤
        comparisonBasisBudget (∑ i, bound i) p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let P := M.comparisonAmbient p B hB hstable
  let K := M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1)
  let F := M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)
  let C := comparisonBasisBudget (∑ i, bound i) p
  let R := (p + q + 4) ^ 2 + C + 3
  have hC : 0 ≤ C := by dsimp [C, comparisonBasisBudget]; positivity
  have hCR : C ≤ R := by dsimp [R]; nlinarith only [sq_nonneg (p + q + 4)]
  have hP : P.GeometryComplexityLE R :=
    (M.comparisonAmbient_geometry B hB hstable hM.1 hE).mono P
      (by dsimp [R]; linarith)
  obtain ⟨b, hb⟩ := M.exists_comparison_layer_basis hM 1
  let bK : Basis (Fin (finrank ℚ K)) ℚ K := b
  have hbK (j k) : rationalLogHeight (P.basis.repr (M.comparisonToAmbient (bK j)) k) ≤ R :=
    (M.comparisonAmbient_point_logHeight p B hB hstable (bK j) (hb j) k).trans hCR
  have hlayers (n : Fin (max s (Fintype.card (ReplicatedIndex bound)) + 1)) :
      ∃ a : Basis (Fin (finrank ℚ (F.layer (n.val + 1)))) ℚ (F.layer (n.val + 1)),
        ∀ j k, rationalLogHeight
          (P.basis.repr (M.comparisonToAmbient (a j : K)) k) ≤ R := by
    obtain ⟨a, ha⟩ := M.exists_comparison_filtration_basis hM (n.val + 1) (by omega)
    exact ⟨a, fun j k =>
      (M.comparisonAmbient_point_logHeight p B hB hstable (a j) (ha j) k).trans hCR⟩
  obtain ⟨E, hEF, hEb, hEL, hgeom⟩ := P.exists_model_of_embedding_logHeight F bK
    M.comparisonToAmbient M.comparisonToAmbient_injective hP hbK hlayers
  refine ⟨E, hEF, hEL, ?_, ?_⟩
  · simpa only [R, C, comparisonGeometryBudget, add_assoc,
      show (3 : ℝ) + 3 = 6 by norm_num] using hgeom
  · intro j k
    rw [hEb]
    exact hb j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

theorem exists_comparisonModel_cost (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      comparisonGeometryBudget t p (squarefreeFrequencyModelBudget t p) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let K := bchIntegralDenominatorBound t + 5
  let A := Polynomial.C (2 ^ t) * X + (X + 3) ^ 8 + Polynomial.C (2 ^ t) * (X + 3) ^ 5
  let Q := A + (A + Polynomial.C K) ^ K
  let B := X + 1 + Polynomial.C (t ^ 2)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (((X + Q + 4) ^ 2 + B + 6) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [X, K, A, Q, B, comparisonGeometryBudget, comparisonBasisBudget,
    squarefreeFrequencyModelBudget, squarefreeFrequencyInputBudget, squarefreeInputBudget,
    replicatedFrequencyDenominatorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_comparison_model {p : ℝ} (hM : M.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B),
      (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE
        (squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      (∀ i, rationalLogHeight (M.filtration.replicatedFrequency η
        ((M.squarefreeModel p B hB hstable).basis i)) ≤
          squarefreeFrequencyModelBudget (∑ i, bound i) p) ∧
      (∀ z : (M.squarefreeModel p B hB hstable).RealGroup,
        z ∈ (M.squarefreeModel p B hB hstable).realLattice →
          ∃ n : ℤ, realifyFunctional (M.filtration.replicatedFrequency η) z.coord = n) ∧
      ∃ E : RationalFilteredNilmanifold
          (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
          (max s (Fintype.card (ReplicatedIndex bound)))
          (finrank ℚ (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))),
        E.filtration = M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1) ∧
        E.lattice = M.comparisonLattice p B hB hstable ∧
        E.GeometryComplexityLE (comparisonGeometryBudget (∑ i, bound i) p
          (squarefreeFrequencyModelBudget (∑ i, bound i) p)) ∧
        ∀ j k, rationalLogHeight
          ((D.basis.prod (M.squarefreeFinBasis p)).repr (E.basis j).val k) ≤
          comparisonBasisBudget (∑ i, bound i) p := by
  obtain ⟨B, hB, hstable, hE, hfreq, hint⟩ := M.exists_controlled_replicated_frequency hM η hη
  exact ⟨B, hB, hstable, hE, hfreq, hint, M.exists_comparison_model hM B hB hstable hE.1⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

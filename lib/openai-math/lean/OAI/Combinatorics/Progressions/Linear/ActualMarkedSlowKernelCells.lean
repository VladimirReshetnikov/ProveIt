import OAI.Combinatorics.Progressions.Estimates.UniformParameterNet
import OAI.Combinatorics.Progressions.Polynomial.MarkedPolynomialSectionSlow
import OAI.Combinatorics.Progressions.Polynomial.PolynomialGridValues

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_subgroup_net
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (K : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, center j ∈ K) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, g ∈ K →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let Ω := {g : NilpotentLieBCHGroup L s hnil //
    g ∈ K ∧ ∀ i, |e.repr g.coord i| ≤ B}
  have hBr : (1 : ℝ) ≤ B := hB
  let : Nonempty Ω := ⟨⟨1, K.one_mem, by simp⟩⟩
  obtain ⟨code, rep, hrep⟩ := exists_uniform_parameter_net
    (fun g : Ω => e.equivFun g.val.coord) (by positivity : (0 : ℝ) < B)
    (fun g i => g.property.2 i) hN
  refine ⟨fun j => (rep j).val, fun j => (rep j).property.1,
    fun j i => (rep j).property.2 i, ?_⟩
  intro g hg hgb
  let x : Ω := ⟨g, hg, hgb⟩
  refine ⟨code x, ?_⟩
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB (by positivity)
    g (rep (code x)).val hgb (rep (code x)).property.2
  intro i
  exact (show |e.repr g.coord i - e.repr (rep (code x)).val.coord i| ≤
      dist (e.equivFun x.val.coord) (e.equivFun (rep (code x)).val.coord) from
    by simpa only [Real.dist_eq, Basis.equivFun_apply, x] using
      dist_le_pi_dist (e.equivFun x.val.coord)
        (e.equivFun (rep (code x)).val.coord) i).trans (hrep x)

theorem exists_bounded_kernel_net {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {N : ℕ} (hN : 0 < N) :
    let := rightMetricSpace (hnil := hnil) e
    ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
      (∀ j, π (center j) = 1) ∧
      (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
      ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
        (∀ i, |e.repr g.coord i| ≤ B) →
        ∃ j, dist g (center j) ≤
          bchBoxMetricConstant s (Fintype.card ι) H B * (4 * B / N) := by
  exact exists_bounded_subgroup_net e c hstructure hc π.ker B hB hN

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_net_with_budget {G : Type*} [Group G]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (π : NilpotentLieBCHGroup L s hnil →* G)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := hnil) e
    ∃ N : ℕ, 0 < N ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤
        Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |e.repr (center j).coord i| ≤ B) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |e.repr g.coord i| ≤ B) →
          ∃ j, dist g (center j) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := hnil) e
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount (2 * B) K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hBp' : 2 * (B : ℝ) ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    exact (mul_le_mul_of_nonneg_left hBp (by norm_num)).trans
      (by nlinarith [Real.exp_pos p])
  have hcard := boxCoverCount_dimension_bound (Fintype.card ι) K
    (by positivity : 0 ≤ 2 * (B : ℝ)) hε (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card ι : ℝ) ≤ p + 1) hBp' (hK.trans hexp)
    (hεinv.trans hexp)
  obtain ⟨center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net e c hstructure hc π B hB hN
  refine ⟨N, hN, ?_, center, hmark, hbound, ?_⟩
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
  · intro g hg hgb
    obtain ⟨j, hj⟩ := hnet g hg hgb
    refine ⟨j, hj.trans ?_⟩
    have hm := boxCoverMeshCount_error (B := 2 * (B : ℝ)) K hε
    dsimp only [N, K] at *
    simpa only [show (2 : ℝ) * (2 * B) = 4 * B by ring] using hm

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
open scoped NNReal

theorem exists_slow_kernel_net_geometry_budget (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d n H : ℕ) (p A : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp ((p + 2) ^ r) →
      ∃ B : ℝ≥0, 1 ≤ B ∧
        ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ B ∧
        (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (bchBoxMetricConstant s d H B : ℝ) *
          (((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A * n * s) ≤
            Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C s * (X + 1) + (X + 2) ^ r
  obtain ⟨a, _, hP⟩ := exists_natPolynomial_eval_budget P
  obtain ⟨b, _, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  let Q := (X + Polynomial.C a + Polynomial.C b) ^ b + P + X + Polynomial.C s
  obtain ⟨C, hC, hQ⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro d n H p A hp hd hn hH hA hAp
  let q : ℝ := s * (p + 1) + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let B : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp hq
  have hn1 : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hAM : ((s : ℝ) + 1) * ((n : ℝ) + 1) ^ s * A ≤ Real.exp q := by
    calc
      _ ≤ Real.exp s * (Real.exp p) ^ s * Real.exp ((p + 2) ^ r) :=
        mul_le_mul (mul_le_mul (Real.add_one_le_exp (s : ℝ))
          (pow_le_pow_left₀ (by positivity) hn1 _) (by positivity) (Real.exp_pos _).le)
          hAp hA (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [q]
        ring
  have hpA : p ≤ p + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hBa : (B : ℝ) ≤ Real.exp (((p + a) + 2) ^ a) := by
    apply Real.exp_le_exp.mpr
    have h' : q ≤ (p + a) ^ a := by simpa [P, X, q, Polynomial.eval₂_pow] using hP p hp
    exact h'.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hBC : (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + a + b) ^ b) :=
    hbox d H B (p + a) (hp.trans hpA) (hd.trans hpA)
      (hH.trans (Real.exp_le_exp.mpr hpA)) hBa
  have hfinal : (p + a + b) ^ b + q + p + s ≤ (p + C) ^ C := by
    simpa [Q, P, X, q, Polynomial.eval₂_pow] using hQ p hp
  have hbase : 0 ≤ (p + a + b) ^ b := by positivity
  have hnexp : (n : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hsexp : (s : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp (s : ℝ)]
  refine ⟨B, hB, hAM, Real.exp_le_exp.mpr (by linarith),
    hBC.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  calc
    _ ≤ Real.exp ((p + a + b) ^ b) * (Real.exp q * Real.exp p * Real.exp s) := by
      apply mul_le_mul hBC
        (mul_le_mul (mul_le_mul hAM hnexp (Nat.cast_nonneg _) (Real.exp_pos _).le)
          hsexp (Nat.cast_nonneg _) (by positivity))
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (((p + a + b) ^ b) + q + p + s) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hfinal

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L G : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G] {s : ℕ}

theorem exists_slow_kernel_freezing_net
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (π : F.realification.Group →* G)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hAB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A ≤ B)
    {N : ℕ} (hN : 0 < N) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
      (∀ j, π (center j) = 1) ∧
      (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
        F.PolynomialSlowBound b w T A g →
        (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
        ∀ z : σ → ℝ, (∀ i, |z i| ≤ T i) →
          ∃ j, ∀ (v : σ → ℝ) (δ : ℝ), 0 ≤ δ →
            (∀ i, |v i| ≤ T i) → (∀ i, |v i - z i| ≤ T i * δ) →
            dist (F.adaptedPolynomialRealValueHom w v g) (center j) ≤
              bchBoxMetricConstant s (Fintype.card ι) H B *
                ((((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A *
                  Fintype.card σ * s) * δ + 4 * B / N) := by
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  obtain ⟨center, hmark, hbound, hnet⟩ := exists_bounded_kernel_net
    (b.baseChange ℝ) (lieStructureConstants b)
    (fun i j k => (realLieBasis_structure b i j k).symm) hc π B hB hN
  refine ⟨center, hmark, hbound, ?_⟩
  intro g hg hker z hz
  obtain ⟨j, hj⟩ := hnet (F.adaptedPolynomialRealValueHom w z g) (hker z)
    (fun i => (F.polynomialSlowBound_value b w hw T hT hA g hg z hz i).trans hAB)
  refine ⟨j, ?_⟩
  intro v δ hδ hv hvz
  have hmove := F.polynomialSlowBound_dist_le b w hw H hc T hT hA hδ B hB hAB
    g hg v z hv hz hvz
  calc
    _ ≤ dist (F.adaptedPolynomialRealValueHom w v g)
          (F.adaptedPolynomialRealValueHom w z g) +
        dist (F.adaptedPolynomialRealValueHom w z g) (center j) := dist_triangle _ _ _
    _ ≤ _ := by nlinarith [hmove, hj]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ ι L G : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G] {s : ℕ}

theorem exists_slow_kernel_cells
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (π : F.realification.Group →* G)
    (H : ℕ) (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {A : ℝ} (hA : 0 ≤ A)
    (B : ℝ≥0) (hB : 1 ≤ B)
    (hAB : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A ≤ B)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hd : (Fintype.card ι : ℝ) ≤ p) (hn : (Fintype.card σ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p)
    (hK : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) ≤ Real.exp p)
    (hmove : (bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s) ≤
        Real.exp p)
    (hεinv : 1 / ε ≤ Real.exp p) :
    letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
    ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
      (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + 2) * (3 * (p + 2) + 4)) ∧
      (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + 1) * (3 * (p + 1) + 4)) ∧
      ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
        (∀ j, π (center j) = 1) ∧
        (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
        ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
          F.PolynomialSlowBound b w T A g →
          (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
          ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
            ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
              (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
              dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤ ε := by
  classical
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  have hhalf : 0 < ε / 2 := by positivity
  have hexp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  have hinv : 1 / (ε / 2) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * (1 / ε) := by ring
      _ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hεinv (by norm_num)
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨N, hN, hNcard, center, hmark, hbound, hnet⟩ :=
    exists_bounded_kernel_net_with_budget (b.baseChange ℝ) (lieStructureConstants b)
      (fun i j k => (realLieBasis_structure b i j k).symm) hc π B hB hhalf
      (by linarith : 0 ≤ p + 1) (by linarith : (Fintype.card ι : ℝ) ≤ p + 1)
      (hBp.trans hexp) (hK.trans hexp) hinv
  let K : ℝ≥0 := ⟨(bchBoxMetricConstant s (Fintype.card ι) H B : ℝ) *
    (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * Fintype.card σ * s),
      by positivity⟩
  let M := boxCoverMeshCount 1 K (ε / 2)
  have hM : 0 < M := boxCoverMeshCount_pos _ _ _
  have hMcard := boxCoverCount_dimension_bound (Fintype.card σ) K
    (by norm_num : (0 : ℝ) ≤ 1) hhalf (by linarith : 0 ≤ p + 1)
    (by linarith : (Fintype.card σ : ℝ) ≤ p + 1)
    (Real.one_le_exp (by linarith)) (hmove.trans hexp) hinv
  refine ⟨N, M, hN, hM, ?_, ?_, center, hmark, hbound, ?_⟩
  · simpa only [add_assoc, one_add_one_eq_two] using hNcard
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hMcard
  · intro g hg hker
    have hz (j : σ → Fin (M + 1)) (i : σ) :
        |normalizedRealBoxGrid T M j i| ≤ T i := normalizedRealBoxGrid_bound T hT hM j i
    choose label hlabel using fun j : σ → Fin (M + 1) =>
      hnet (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
        (hker _) (fun i =>
          (F.polynomialSlowBound_value b w hw T hT hA g hg _ (hz j) i).trans hAB)
    refine ⟨label, ?_⟩
    intro j v hv hvz
    have hm := F.polynomialSlowBound_dist_le b w hw H hc T hT hA
      (by positivity : (0 : ℝ) ≤ 2 / M) B hB hAB g hg v
      (normalizedRealBoxGrid T M j) hv (hz j) hvz
    have herr : dist (F.adaptedPolynomialRealValueHom w v g)
        (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) ≤ ε / 2 := by
      apply hm.trans
      have he := boxCoverMeshCount_error (B := (1 : ℝ)) K hhalf
      change (K : ℝ) * (2 / (M : ℝ)) ≤ ε / 2
      simpa only [mul_one] using he
    calc
      _ ≤ dist (F.adaptedPolynomialRealValueHom w v g)
          (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g) +
        dist (F.adaptedPolynomialRealValueHom w (normalizedRealBoxGrid T M j) g)
          (center (label j)) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add herr (hlabel j)
      _ = ε := by ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_slow_kernel_cells (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι L G : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] [_root_.Group G]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (π : F.realification.Group →* G) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N M : ℕ, 0 < N ∧ 0 < M ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (M + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, π (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ r)) g →
            (∀ z, π (F.adaptedPolynomialRealValueHom w z g) = 1) →
            ∃ label : (σ → Fin (M + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T M j i| ≤ T i * (2 / M)) →
                dist (F.adaptedPolynomialRealValueHom w v g) (center (label j)) ≤
                  Real.exp (-((p + 2) ^ r)) := by
  obtain ⟨a, ha, hgeometry⟩ := exists_slow_kernel_net_geometry_budget s r
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + (X + 2) ^ r
  let P := Q + (Q + 2) * (3 * (Q + 2) + 4)
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L G _ _ _ _ _ _ _ _ _ _ _ F b w hw π H p hp hd hn hH hc T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  obtain ⟨B, hB, hAB, hBcap, hK, hmove⟩ := hgeometry
    (Fintype.card ι) (Fintype.card σ) H p (Real.exp ((p + 2) ^ r))
    hp hd hn hH (Real.exp_nonneg _) le_rfl
  let q : ℝ := p + (p + a) ^ a + (p + 2) ^ r
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ha0 : 0 ≤ (p + a) ^ a := by positivity
  have hr0 : 0 ≤ (p + 2) ^ r := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hrq : (p + 2) ^ r ≤ q := by dsimp [q]; linarith
  have hinv : 1 / Real.exp (-((p + 2) ^ r)) ≤ Real.exp q := by
    rw [Real.exp_neg]
    simpa only [one_div, inv_inv] using Real.exp_le_exp.mpr hrq
  obtain ⟨N, M, hN, hM, hNcard, hMcard, center, hmark, hbound, hfreeze⟩ :=
    F.exists_slow_kernel_cells b w hw π H hc T hT (Real.exp_nonneg _) B hB hAB
      (Real.exp_pos _) hq (hd.trans hpq) (hn.trans hpq)
      (hBcap.trans (Real.exp_le_exp.mpr haq))
      (hK.trans (Real.exp_le_exp.mpr haq))
      (hmove.trans (Real.exp_le_exp.mpr haq)) hinv
  have hbudget : q + (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hP p hp
  have hcard : (q + 2) * (3 * (q + 2) + 4) ≤ (p + C) ^ C := by linarith
  have hqcap : q ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) * (3 * (q + 2) + 4) := by positivity
    linarith
  refine ⟨N, M, hN, hM, hNcard.trans (Real.exp_le_exp.mpr hcard),
    hMcard.trans (Real.exp_le_exp.mpr ?_), center, hmark, ?_, hfreeze⟩
  · exact (show (q + 1) * (3 * (q + 1) + 4) ≤ (q + 2) * (3 * (q + 2) + 4) by
      nlinarith).trans hcard
  · intro j i
    exact (hbound j i).trans (hBcap.trans (Real.exp_le_exp.mpr (haq.trans hqcap)))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_actual_marked_slow_kernel_cells (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι κ L M : Type*}
      [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {t : ℕ}
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
      (b : Basis ι ℚ L) (c : Basis κ ℚ M) (ω : ι → ℕ),
      (∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
        (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j),
      Function.RightInverse S φ →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      (∀ i j, |(b.repr (S (c j)) i : ℝ)| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      letI := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
      ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
        (Fintype.card (ι → Fin (N + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : (ι → Fin (N + 1)) → F.realification.Group,
          (∀ j, realificationMap (hnil := F.lowerCentralSeries_eq_bot)
            (hM := G.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
          (∀ j i, |(b.baseChange ℝ).repr (center j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∀ (E : (F.realification.adaptedPolynomialFiltration w).Group)
            (EF : (G.realification.adaptedPolynomialFiltration w).Group),
            F.PolynomialSlowBound b w T (Real.exp ((p + 2) ^ a)) E →
            G.PolynomialSlowBound c w T (Real.exp ((p + 2) ^ a)) EF →
            F.realPolynomialGroupMap G φ hφ w E = EF →
            ∃ label : (σ → Fin (Q + 1)) → (ι → Fin (N + 1)),
              ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ T i) →
                (∀ i, |v i - normalizedRealBoxGrid T Q j i| ≤ T i * (2 / Q)) →
                dist (F.adaptedPolynomialRealValueHom w v
                  (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹))
                  (center (label j)) ≤ Real.exp (-((p + 2) ^ u)) := by
  obtain ⟨A, hA, hslow⟩ := exists_marked_polynomial_kernel_slow_bound s a
  obtain ⟨B, hB, hnet⟩ := exists_uniform_slow_kernel_cells s (A + u)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ _ _ _ _ _ t F G b c ω hF w hw φ hφ S hS
    hsection H p hH hp hι hκ hσ hHp hc hSbound T hT
  let := rightMetricSpace (hnil := F.realification.lowerCentralSeries_eq_bot) (b.baseChange ℝ)
  let π := realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := G.lowerCentralSeries_eq_bot) φ
  have hpA : p ≤ p + A := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hpA0 : 0 ≤ p + A := hp.trans hpA
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hnet F b w hw π H (p + A) hpA0 (hι.trans hpA) (hσ.trans hpA)
      (hHp.trans (Real.exp_le_exp.mpr hpA)) hc T hT
  have hcost : (p + A + B) ^ B ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hcost),
    hQcard.trans (Real.exp_le_exp.mpr hcost), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro E EF hE hEF hproj
  have hKE := (hslow F G b c ω hF w hw H p hH hp hι hκ hσ hHp hc S hS
    (by simpa only [scalarExtension_basis_coordinates] using hSbound) T hT E EF hE hEF).1
  have hbound : (p + A) ^ A ≤ (p + A + 2) ^ (A + u) :=
    (pow_le_pow_left₀ hpA0 (by linarith : p + A ≤ p + A + 2) A).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))
  have hKEslow := F.polynomialSlowBound_mono b w T hT
    (Real.exp_le_exp.mpr hbound) _ hKE
  have hmap : F.realPolynomialGroupMap G φ hφ w
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹) = 1 := by
    rw [map_mul, map_inv, hproj,
      F.realPolynomialGroupMap_filteredSection G w φ hφ S hS hsection EF, mul_inv_cancel]
  have hker (v : σ → ℝ) : π (F.adaptedPolynomialRealValueHom w v
      (E * (F.filteredRealPolynomialSection G w S hS EF)⁻¹)) = 1 := by
    rw [← F.realPolynomialGroupMap_value G φ hφ w, hmap, map_one]
  obtain ⟨label, hlabel⟩ := hfreeze _ hKEslow hker
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ p + 2)
    (by linarith : p + 2 ≤ p + A + 2) u).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + A + 2) (by omega))

end Erdos3.NilpotentLieFiltration

end

end OAI

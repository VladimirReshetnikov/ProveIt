import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Surreal.Algebra.MarkovResolvent
import Surreal.Algebra.StochasticIdempotent

/-!
# Effective-generator reconstruction

This file proves the abstract real pseudo-resolvent core of
`markov:thm:effective` of `docs/surreal/markov-generators-at-every-scale/article.tex`, and all
of that theorem's conclusions for any family `K` satisfying the hypothesis package
`IsCrossover`. The actual shadow `K_α(c) = res R_L(c t^α)` is not constructed, so the literal
theorem for it is still pending (see the last paragraph).

**Abstract real pseudo-resolvent core.** Let `H : ℝ → Matrix ι ι ℝ` satisfy the compressed
resolvent identity `markov:eq:compressed-identity`, `(e - c)H(c)H(e) = eH(c) - cH(e)` for
distinct `c, e > 0`, and `H(c) → I` as `c → ∞` (`IsPseudoResolvent`).

* `IsPseudoResolvent.existsUnique_resolvent`: exactly one `G` has `H(c) = c(cI + G)⁻¹` for
  every real `c > 0` (`markov:eq:effective-resolvent`). It is `effectiveGenerator H =
  H(1)⁻¹ - I` (`markov:eq:effective-one`, `IsGenerator.eq_effectiveGenerator`). The proof is
  the source's: some `H(e)` is invertible, and `H(c)[cI + e(H(e)⁻¹ - I)] = cI`
  (`IsPseudoResolvent.mul_smul_add_eq`); a one-sided inverse is two-sided.
* `IsPseudoResolvent.isRowLaplacian`: if every `H(c)` is row-stochastic, then `G𝟙 = 0` and
  `G_{ab} ≤ 0` for `a ≠ b`, from `H(c)G = c(I - H(c)) → G` as `c → ∞`.
* Given a limit `H(c) → Q` as `c → 0⁺`: `GQ = QG = 0`, `Q² = Q`, `ker G = range Q` and
  `ker Q = range G`, so `Q` is the zero-eigenvalue projection of `G`. There is no Jordan chain
  `Gy = x ≠ 0`, `Gx = 0` (`IsGenerator.eq_zero_of_jordan`), so the zero eigenvalue is
  semisimple. Finally `dim ker G = rank Q` and `rank G + rank Q = card ι`.
  `effective_core` bundles all of this.
* `effectiveGenerator_submatrix`: reindexing `H` only permutes `G`.

**Instantiation at a crossover.** The shadow `K_α(c) = res R_L(c t^α)` is not constructed in
the library. Its properties come from the residue part of `markov:lem:resolvent`
(`markov:eq:same-scale`), from `markov:thm:leading` (stochasticity, via `markov:prop:forest`)
and from `markov:thm:flag`, none of which is formalized for the shadow. `IsCrossover K P Q`
records exactly the properties that the source proof uses: every `K(c)` is stochastic,
`markov:eq:same-scale`, the endpoint limits `markov:eq:fast-endpoint` and
`markov:eq:slow-endpoint`, and the endpoint relations `markov:eq:endpoint-relations`.
`IsSplitting P U V` is the conclusion of `markov:lem:splitting`.

* `effective_reconstruction`: put `H(c) = VK(c)U`. The unique `G` with `H(c) = c(cI + G)⁻¹`
  and `K(c) = Uc(cI + G)⁻¹V` for all `c > 0` is `H(1)⁻¹ - I`. It is a real row Laplacian.
  Its zero-eigenvalue projection is `Q' = VQU`, the limit of `H(c)` as `c → 0⁺`, and its zero
  eigenvalue is semisimple. Moreover `UQ'V = Q`, `rank Q' = rank Q`, `dim ker G = rank Q`
  and `rank G + rank Q = rank P = p`.
* `effective_reconstruction_canonical`: the same for the canonical splitting
  `StochasticIdempotent.splitU`, `StochasticIdempotent.splitV`, indexed by the closed classes
  of `P`. That `P` is a stochastic idempotent is derived from `IsCrossover`.
* `effectiveGenerator_compress_submatrix` and `IsSplitting.submatrix`: ordering the classes
  differently only permutes `G`.

Pending: discharging `IsCrossover` for the actual shadow `K_α(c)` at a critical scale, which
needs the residue part of `markov:lem:resolvent`, `markov:prop:forest`, `markov:thm:leading`
and `markov:thm:flag`. The source's hypothesis `p > q` (criticality) is not needed for any
conclusion.
-/

namespace Surreal.MarkovEffective

open Matrix Filter Topology

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The compressed resolvent identity `markov:eq:compressed-identity` together with the
normalization `H(c) → I` as `c → ∞`. -/
structure IsPseudoResolvent (H : ℝ → Matrix ι ι ℝ) : Prop where
  resolvent_identity : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e →
    (e - c) • (H c * H e) = e • H c - c • H e
  tendsto_atTop : Tendsto H atTop (𝓝 1)

/-- The explicit effective generator `markov:eq:effective-one`: `G = H(1)⁻¹ - I`. -/
def effectiveGenerator (H : ℝ → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (H 1)⁻¹ - 1

/-- `G` generates `H`: `H(c)(cI + G) = cI` for every real `c > 0`. -/
def IsGenerator (H : ℝ → Matrix ι ι ℝ) (G : Matrix ι ι ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → H c * (c • (1 : Matrix ι ι ℝ) + G) = c • 1

/-- A real Markov row Laplacian: zero row sums and nonpositive off-diagonal entries. -/
def IsRowLaplacian (G : Matrix ι ι ℝ) : Prop :=
  G *ᵥ (fun _ => (1 : ℝ)) = 0 ∧ ∀ a b, a ≠ b → G a b ≤ 0

variable {H : ℝ → Matrix ι ι ℝ}

namespace IsPseudoResolvent

theorem resolvent_identity' (hH : IsPseudoResolvent H) {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    (e - c) • (H c * H e) = e • H c - c • H e := by
  rcases eq_or_ne c e with rfl | hce
  · simp
  · exact hH.resolvent_identity c e hc he hce

/-- Since `H(c) → I`, some `H(e)` with `e > 0` is invertible. -/
theorem exists_isUnit_det (hH : IsPseudoResolvent H) : ∃ e, 0 < e ∧ IsUnit (H e).det := by
  have hdet : Tendsto (fun c => (H c).det) atTop (𝓝 1) := by
    have hcont : Continuous fun M : Matrix ι ι ℝ => M.det := continuous_id.matrix_det
    have := (hcont.tendsto 1).comp hH.tendsto_atTop
    rw [det_one] at this
    exact this
  obtain ⟨e, he0, he⟩ := ((eventually_gt_atTop 0).and (hdet.eventually_ne one_ne_zero)).exists
  exact ⟨e, he0, isUnit_iff_ne_zero.2 he⟩

/-- The source's rearrangement of `markov:eq:compressed-identity`:
`H(c)[cI + e(H(e)⁻¹ - I)] = cI`, including `c = e`. -/
theorem mul_smul_add_eq (hH : IsPseudoResolvent H) {e : ℝ} (he : 0 < e)
    (hdet : IsUnit (H e).det) {c : ℝ} (hc : 0 < c) :
    H c * (c • (1 : Matrix ι ι ℝ) + e • ((H e)⁻¹ - 1)) = c • 1 := by
  have h := congrArg (· * (H e)⁻¹) (hH.resolvent_identity' hc he)
  simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc, mul_nonsing_inv _ hdet,
    Matrix.mul_one] at h
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one]
  linear_combination (norm := module) -h

theorem exists_isGenerator (hH : IsPseudoResolvent H) : ∃ G, IsGenerator H G := by
  obtain ⟨e, he, hdet⟩ := hH.exists_isUnit_det
  exact ⟨e • ((H e)⁻¹ - 1), fun c hc => hH.mul_smul_add_eq he hdet hc⟩

end IsPseudoResolvent

namespace IsGenerator

variable {G : Matrix ι ι ℝ}

/-- A square matrix with a right inverse is invertible: `(cI + G)H(c) = cI`. -/
theorem smul_add_mul (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) :
    (c • (1 : Matrix ι ι ℝ) + G) * H c = c • 1 := by
  have h1 : H c * (c⁻¹ • (c • (1 : Matrix ι ι ℝ) + G)) = 1 := by
    rw [Matrix.mul_smul, hG c hc, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.smul_mul] at h2
  calc (c • (1 : Matrix ι ι ℝ) + G) * H c
      = c • (c⁻¹ • ((c • (1 : Matrix ι ι ℝ) + G) * H c)) := by
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    _ = c • 1 := by rw [h2]

theorem isUnit_det_smul_add (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) :
    IsUnit (c • (1 : Matrix ι ι ℝ) + G).det :=
  isUnit_det_of_right_inverse (B := c⁻¹ • H c) (by
    rw [Matrix.mul_smul, hG.smul_add_mul hc, smul_smul, inv_mul_cancel₀ hc.ne', one_smul])

theorem isUnit_det (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) : IsUnit (H c).det :=
  isUnit_det_of_right_inverse (B := c⁻¹ • (c • (1 : Matrix ι ι ℝ) + G)) (by
    rw [Matrix.mul_smul, hG c hc, smul_smul, inv_mul_cancel₀ hc.ne', one_smul])

/-- `markov:eq:effective-resolvent`: `H(c) = c(cI + G)⁻¹`. -/
theorem eq_resolvent (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) : H c = Markov.resolvent G c :=
  (Markov.resolvent_eq_of_mul_eq hc.ne' (hG.smul_add_mul hc)).symm

/-- `H(c)G = c(I - H(c))`. -/
theorem mul_eq (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) : H c * G = c • (1 - H c) := by
  have h := hG c hc
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at h
  rw [smul_sub, ← h, add_sub_cancel_left]

/-- `GH(c) = c(I - H(c))`. -/
theorem generator_mul (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c) :
    G * H c = c • (1 - H c) := by
  have h := hG.smul_add_mul hc
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul] at h
  rw [smul_sub, ← h, add_sub_cancel_left]

/-- `markov:eq:effective-one`: a generator is `H(1)⁻¹ - I`. -/
theorem eq_effectiveGenerator (hG : IsGenerator H G) : G = effectiveGenerator H := by
  have h := hG 1 one_pos
  simp only [one_smul] at h
  rw [effectiveGenerator, inv_eq_right_inv h, add_sub_cancel_left]

/-- If one `H(c)` fixes `𝟙`, then `G𝟙 = 0`. -/
theorem mulVec_one (hG : IsGenerator H G) {c : ℝ} (hc : 0 < c)
    (h1 : H c *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1) : G *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have h := congrArg (fun M => M *ᵥ (fun _ => (1 : ℝ))) (hG.generator_mul hc)
  simp only [← Matrix.mulVec_mulVec, h1, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, sub_self, smul_zero] at h
  exact h

/-- If an off-diagonal entry of `H(c)` is eventually nonnegative, the corresponding entry of
`G = lim_{c → ∞} c(I - H(c))` is nonpositive. -/
theorem offDiag_nonpos (hG : IsGenerator H G) (hinf : Tendsto H atTop (𝓝 1)) {a b : ι}
    (hab : a ≠ b) (hnn : ∀ᶠ c in atTop, 0 ≤ H c a b) : G a b ≤ 0 := by
  have hlim : Tendsto (fun c => H c * G) atTop (𝓝 G) := by
    simpa using hinf.mul_const G
  have hent : Tendsto (fun c => (H c * G) a b) atTop (𝓝 (G a b)) :=
    ((continuous_id.matrix_elem a b).tendsto G).comp hlim
  refine le_of_tendsto hent ?_
  filter_upwards [hnn, eventually_gt_atTop 0] with c hc hc0
  rw [hG.mul_eq hc0]
  simp only [Matrix.smul_apply, Matrix.sub_apply, one_apply_ne hab, zero_sub, smul_eq_mul,
    mul_neg, neg_nonpos]
  exact mul_nonneg hc0.le hc

/-! ### The slow endpoint `c → 0⁺` -/

section Slow

variable {Q : Matrix ι ι ℝ}

omit [Fintype ι] in
theorem tendsto_smul_one_sub (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    Tendsto (fun c : ℝ => c • (1 - H c)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h : Tendsto (fun c : ℝ => c • (1 - H c)) (𝓝[>] 0) (𝓝 ((0 : ℝ) • (1 - Q))) :=
    hc.smul (tendsto_const_nhds.sub h0)
  rw [zero_smul] at h
  exact h

/-- `QG = 0`, from `H(c)G = c(I - H(c))` and boundedness of `H(c)` as `c → 0⁺`. -/
theorem zeroProj_mul_generator (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    Q * G = 0 := by
  refine tendsto_nhds_unique (h0.mul_const G) ((tendsto_smul_one_sub h0).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (hG.mul_eq hc).symm

/-- `GQ = 0`. -/
theorem generator_mul_zeroProj (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    G * Q = 0 := by
  refine tendsto_nhds_unique (h0.const_mul G) ((tendsto_smul_one_sub h0).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (hG.generator_mul hc).symm

theorem zeroProj_mul_apply (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) {c : ℝ}
    (hc : 0 < c) : Q * H c = Q := by
  have hQG := hG.zeroProj_mul_generator h0
  have h : c • (Q * H c) = c • Q := by
    calc c • (Q * H c) = Q * (c • (1 : Matrix ι ι ℝ) + G) * H c := by
          rw [Matrix.mul_add, hQG, add_zero, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = c • Q := by rw [Matrix.mul_assoc, hG.smul_add_mul hc, Matrix.mul_smul, Matrix.mul_one]
  exact smul_right_injective _ hc.ne' h

/-- The slow limit is idempotent: `Q² = Q`. -/
theorem zeroProj_mul_self (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    Q * Q = Q := by
  refine tendsto_nhds_unique (h0.const_mul Q) (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (hG.zeroProj_mul_apply h0 hc).symm

theorem mulVec_apply_eq (hG : IsGenerator H G) {x : ι → ℝ} (hx : G *ᵥ x = 0) {c : ℝ}
    (hc : 0 < c) : H c *ᵥ x = x := by
  have h := congrArg (· *ᵥ x) (hG c hc)
  simp only [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hx, add_zero, Matrix.mulVec_smul] at h
  exact smul_right_injective _ hc.ne' h

/-- `Gx = 0` exactly when `Qx = x`. -/
theorem mulVec_eq_zero_iff (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q))
    (x : ι → ℝ) : G *ᵥ x = 0 ↔ Q *ᵥ x = x := by
  constructor
  · intro hx
    have hcont : Continuous fun M : Matrix ι ι ℝ => M *ᵥ x :=
      continuous_id.matrix_mulVec continuous_const
    refine tendsto_nhds_unique ((hcont.tendsto Q).comp h0) (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (hG.mulVec_apply_eq hx hc).symm
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, hG.generator_mul_zeroProj h0, Matrix.zero_mulVec]

/-- No Jordan chain at zero: `Gy = x` and `Gx = 0` force `x = 0`, since otherwise
`H(c)y = y - x/c` would be unbounded as `c → 0⁺`. -/
theorem eq_zero_of_jordan (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q))
    {x y : ι → ℝ} (hy : G *ᵥ y = x) (hx : G *ᵥ x = 0) : x = 0 := by
  have key : ∀ c : ℝ, 0 < c → c • (y - H c *ᵥ y) = x := by
    intro c hc
    have h := congrArg (· *ᵥ y) (hG c hc)
    simp only [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hy, Matrix.mulVec_add, Matrix.mulVec_smul,
      hG.mulVec_apply_eq hx hc] at h
    rw [smul_sub, ← h, add_sub_cancel_left]
  have hcont : Continuous fun M : Matrix ι ι ℝ => M *ᵥ y :=
    continuous_id.matrix_mulVec continuous_const
  have hc : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : Tendsto (fun c : ℝ => c • (y - H c *ᵥ y)) (𝓝[>] 0)
      (𝓝 ((0 : ℝ) • (y - Q *ᵥ y))) :=
    hc.smul (tendsto_const_nhds.sub ((hcont.tendsto Q).comp h0))
  rw [zero_smul] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (key c hc).symm

/-- Semisimplicity of the zero eigenvalue: `ker G² = ker G`. -/
theorem mulVec_mulVec_eq_zero_iff (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q))
    (y : ι → ℝ) : G *ᵥ (G *ᵥ y) = 0 ↔ G *ᵥ y = 0 :=
  ⟨fun h => hG.eq_zero_of_jordan h0 rfl h, fun h => by rw [h, Matrix.mulVec_zero]⟩

/-- `ker G = range Q`. -/
theorem ker_eq_range (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    LinearMap.ker G.mulVecLin = LinearMap.range Q.mulVecLin := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hG.mulVec_eq_zero_iff h0, LinearMap.mem_range]
  constructor
  · intro hx
    exact ⟨x, by rw [Matrix.mulVecLin_apply, hx]⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hG.zeroProj_mul_self h0]

/-- The kernel of `G` has dimension `rank Q`. -/
theorem finrank_ker (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    Module.finrank ℝ (LinearMap.ker G.mulVecLin) = Q.rank := by
  rw [hG.ker_eq_range h0]
  rfl

/-- `rank G + rank Q = card ι`. -/
theorem rank_add_rank (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    G.rank + Q.rank = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  rw [hG.finrank_ker h0, Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- `ker Q = range G`, so `Q` is the projection onto `ker G` along `range G`. -/
theorem ker_zeroProj_eq_range (hG : IsGenerator H G) (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    LinearMap.ker Q.mulVecLin = LinearMap.range G.mulVecLin := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hG.zeroProj_mul_generator h0, Matrix.zero_mulVec]
  · have h1 := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
    have h2 := hG.rank_add_rank h0
    rw [Module.finrank_fintype_fun_eq_card] at h1
    change G.rank = _
    change Q.rank + _ = _ at h1
    omega

end Slow

end IsGenerator

namespace IsPseudoResolvent

theorem isGenerator_effectiveGenerator (hH : IsPseudoResolvent H) :
    IsGenerator H (effectiveGenerator H) := by
  obtain ⟨G, hG⟩ := hH.exists_isGenerator
  rw [← hG.eq_effectiveGenerator]
  exact hG

theorem eq_effectiveGenerator_of_resolvent (hH : IsPseudoResolvent H) {G : Matrix ι ι ℝ}
    (hG : ∀ c : ℝ, 0 < c → H c = Markov.resolvent G c) : G = effectiveGenerator H := by
  have hunit := hH.isGenerator_effectiveGenerator.isUnit_det one_pos
  have h1 : H 1 = (1 + G)⁻¹ := by
    rw [hG 1 one_pos, Markov.resolvent]
    simp only [one_smul]
  rw [h1, isUnit_nonsing_inv_det_iff] at hunit
  rw [effectiveGenerator, h1, nonsing_inv_nonsing_inv _ hunit, add_sub_cancel_left]

/-- `markov:thm:effective`, abstract core: there is exactly one `G` with
`H(c) = c(cI + G)⁻¹` for every real `c > 0`. -/
theorem existsUnique_resolvent (hH : IsPseudoResolvent H) :
    ∃! G : Matrix ι ι ℝ, ∀ c : ℝ, 0 < c → H c = Markov.resolvent G c :=
  ⟨effectiveGenerator H, fun _ hc => hH.isGenerator_effectiveGenerator.eq_resolvent hc,
    fun _ hG => hH.eq_effectiveGenerator_of_resolvent hG⟩

theorem isGenerator_iff (hH : IsPseudoResolvent H) {G : Matrix ι ι ℝ} :
    IsGenerator H G ↔ ∀ c : ℝ, 0 < c → H c = Markov.resolvent G c := by
  refine ⟨fun hG _ hc => hG.eq_resolvent hc, fun hG => ?_⟩
  rw [hH.eq_effectiveGenerator_of_resolvent hG]
  exact hH.isGenerator_effectiveGenerator

/-- The effective generator is a real row Laplacian when every `H(c)` is stochastic. -/
theorem isRowLaplacian (hH : IsPseudoResolvent H)
    (hst : ∀ c : ℝ, 0 < c → H c ∈ rowStochastic ℝ ι) :
    IsRowLaplacian (effectiveGenerator H) := by
  have hG := hH.isGenerator_effectiveGenerator
  refine ⟨hG.mulVec_one one_pos (one_vecMul_of_mem_rowStochastic (hst 1 one_pos)),
    fun a b hab => hG.offDiag_nonpos hH.tendsto_atTop hab ?_⟩
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact nonneg_of_mem_rowStochastic (hst c hc)

end IsPseudoResolvent

/-- Reordering the index set only permutes the effective generator. -/
theorem effectiveGenerator_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : ℝ → Matrix ι ι ℝ) (σ : κ ≃ ι) :
    effectiveGenerator (fun c => (H c).submatrix σ σ) = (effectiveGenerator H).submatrix σ σ := by
  simp only [effectiveGenerator]
  rw [inv_submatrix_equiv]
  ext a b
  simp [Matrix.one_apply]

/-- `markov:thm:effective`, abstract real pseudo-resolvent core. Let `H(c)` be a family of
real stochastic matrices satisfying the compressed resolvent identity, with `H(c) → I` as
`c → ∞` and `H(c) → Q` as `c → 0⁺`. Then exactly one `G` has `H(c) = c(cI + G)⁻¹` for all
`c > 0`, namely `G = H(1)⁻¹ - I`; it is a real row Laplacian; `Q` is the idempotent with
`GQ = QG = 0`, range `ker G` and kernel `range G`; the zero eigenvalue is semisimple; the
kernel of `G` has dimension `rank Q`; and `rank G + rank Q = card ι`. -/
theorem effective_core (hH : IsPseudoResolvent H)
    (hst : ∀ c : ℝ, 0 < c → H c ∈ rowStochastic ℝ ι) {Q : Matrix ι ι ℝ}
    (h0 : Tendsto H (𝓝[>] 0) (𝓝 Q)) :
    (∀ G : Matrix ι ι ℝ, (∀ c : ℝ, 0 < c → H c = Markov.resolvent G c) ↔
      G = effectiveGenerator H) ∧
    IsRowLaplacian (effectiveGenerator H) ∧
    Q * Q = Q ∧ effectiveGenerator H * Q = 0 ∧ Q * effectiveGenerator H = 0 ∧
    LinearMap.ker (effectiveGenerator H).mulVecLin = LinearMap.range Q.mulVecLin ∧
    LinearMap.ker Q.mulVecLin = LinearMap.range (effectiveGenerator H).mulVecLin ∧
    (∀ y : ι → ℝ, effectiveGenerator H *ᵥ (effectiveGenerator H *ᵥ y) = 0 →
      effectiveGenerator H *ᵥ y = 0) ∧
    Module.finrank ℝ (LinearMap.ker (effectiveGenerator H).mulVecLin) = Q.rank ∧
    (effectiveGenerator H).rank + Q.rank = Fintype.card ι := by
  have hG := hH.isGenerator_effectiveGenerator
  refine ⟨fun G => ⟨hH.eq_effectiveGenerator_of_resolvent, ?_⟩, hH.isRowLaplacian hst,
    hG.zeroProj_mul_self h0, hG.generator_mul_zeroProj h0, hG.zeroProj_mul_generator h0,
    hG.ker_eq_range h0, hG.ker_zeroProj_eq_range h0,
    fun y => (hG.mulVec_mulVec_eq_zero_iff h0 y).1, hG.finrank_ker h0, hG.rank_add_rank h0⟩
  rintro rfl
  exact fun _ hc => hG.eq_resolvent hc

/-! ### Instantiation at a crossover

The shadow `K_α(c) = res R_L(c t^α)` and its endpoints are not constructed here. Their
properties used by the source proof, which are the conclusions of `markov:lem:resolvent`
(`markov:eq:same-scale`), `markov:thm:leading` (stochasticity) and `markov:thm:flag`
(`markov:eq:fast-endpoint`, `markov:eq:slow-endpoint`, `markov:eq:endpoint-relations`),
are collected in `IsCrossover`. -/

section Crossover

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- The properties of a shadow family `K = K_α` (critical or not) with fast endpoint `P` and
slow endpoint `Q` that the proof of `markov:thm:effective` uses. -/
structure IsCrossover (K : ℝ → Matrix n n ℝ) (P Q : Matrix n n ℝ) : Prop where
  /-- `markov:thm:leading`: every `K(c)` is row-stochastic. -/
  stochastic : ∀ c : ℝ, 0 < c → K c ∈ rowStochastic ℝ n
  /-- `markov:eq:same-scale`. -/
  resolvent_identity : ∀ c e : ℝ, 0 < c → 0 < e → c ≠ e →
    (e - c) • (K c * K e) = e • K c - c • K e
  /-- `markov:eq:fast-endpoint`. -/
  tendsto_atTop : Tendsto K atTop (𝓝 P)
  /-- `markov:eq:slow-endpoint`. -/
  tendsto_zero : Tendsto K (𝓝[>] 0) (𝓝 Q)
  /-- `markov:eq:endpoint-relations`, `PK(c) = K(c)`. -/
  fast_mul : ∀ c : ℝ, 0 < c → P * K c = K c
  /-- `markov:eq:endpoint-relations`, `K(c)P = K(c)`. -/
  mul_fast : ∀ c : ℝ, 0 < c → K c * P = K c
  /-- `markov:eq:endpoint-relations`, `K(c)Q = Q`. -/
  mul_slow : ∀ c : ℝ, 0 < c → K c * Q = Q
  /-- `markov:eq:endpoint-relations`, `QK(c) = Q`. -/
  slow_mul : ∀ c : ℝ, 0 < c → Q * K c = Q

/-- A splitting `P = UV`, `VU = I` by nonnegative row-stochastic factors, as in
`markov:lem:splitting`. -/
structure IsSplitting (P : Matrix n n ℝ) (U : Matrix n p ℝ) (V : Matrix p n ℝ) : Prop where
  U_nonneg : ∀ i a, 0 ≤ U i a
  V_nonneg : ∀ a j, 0 ≤ V a j
  U_sum : ∀ i, ∑ a, U i a = 1
  V_sum : ∀ a, ∑ j, V a j = 1
  eq_mul : P = U * V
  mul_eq_one : V * U = 1

/-- The compressed family `H(c) = V K(c) U`. -/
def compress (V : Matrix p n ℝ) (K : ℝ → Matrix n n ℝ) (U : Matrix n p ℝ) (c : ℝ) :
    Matrix p p ℝ :=
  V * K c * U

variable {K : ℝ → Matrix n n ℝ} {P Q : Matrix n n ℝ} {U : Matrix n p ℝ} {V : Matrix p n ℝ}

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
theorem tendsto_compress {l : Filter ℝ} {M : Matrix n n ℝ} (h : Tendsto K l (𝓝 M)) :
    Tendsto (compress V K U) l (𝓝 (V * M * U)) := by
  have hcont : Continuous fun X : Matrix n n ℝ => V * X * U :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (hcont.tendsto M).comp h

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- Reordering the classes reindexes the compressed family. -/
theorem compress_submatrix {κ : Type*} (σ : κ ≃ p) :
    compress (V.submatrix σ id) K (U.submatrix id σ) =
      fun c => (compress V K U c).submatrix σ σ := by
  funext c
  ext a b
  simp [compress, Matrix.mul_apply]

namespace IsSplitting

omit [DecidableEq n] in
theorem mulVec_one_U (hs : IsSplitting P U V) : U *ᵥ (1 : p → ℝ) = 1 := by
  funext i
  simpa [mulVec, dotProduct] using hs.U_sum i

omit [DecidableEq n] in
theorem mulVec_one_V (hs : IsSplitting P U V) : V *ᵥ (1 : n → ℝ) = 1 := by
  funext a
  simpa [mulVec, dotProduct] using hs.V_sum a

omit [DecidableEq n] in
/-- Reordering the classes of a splitting gives a splitting. -/
theorem submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (hs : IsSplitting P U V) (σ : κ ≃ p) :
    IsSplitting P (U.submatrix id σ) (V.submatrix σ id) where
  U_nonneg i a := hs.U_nonneg i (σ a)
  V_nonneg a j := hs.V_nonneg (σ a) j
  U_sum i := by
    simp only [submatrix_apply, id]
    rw [σ.sum_comp (U i)]
    exact hs.U_sum i
  V_sum a := hs.V_sum (σ a)
  eq_mul := by rw [submatrix_mul_equiv, submatrix_id_id, hs.eq_mul]
  mul_eq_one := by
    rw [← submatrix_mul _ _ _ _ _ Function.bijective_id, hs.mul_eq_one, submatrix_one_equiv]

theorem compress_mem_rowStochastic (hs : IsSplitting P U V) {c : ℝ}
    (hK : K c ∈ rowStochastic ℝ n) : compress V K U c ∈ rowStochastic ℝ p := by
  refine mem_rowStochastic.2 ⟨fun a b => ?_, ?_⟩
  · simp only [compress, Matrix.mul_apply]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hs.V_nonneg a k) (nonneg_of_mem_rowStochastic hK)) (hs.U_nonneg j b)
  · rw [compress, ← Matrix.mulVec_mulVec, hs.mulVec_one_U, ← Matrix.mulVec_mulVec,
      one_vecMul_of_mem_rowStochastic hK, hs.mulVec_one_V]

end IsSplitting

namespace IsCrossover

theorem fast_mul_slow (hK : IsCrossover K P Q) : P * Q = Q := by
  refine tendsto_nhds_unique (hK.tendsto_atTop.mul_const Q) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (hK.mul_slow c hc).symm

theorem slow_mul_fast (hK : IsCrossover K P Q) : Q * P = Q := by
  refine tendsto_nhds_unique (hK.tendsto_atTop.const_mul Q) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (hK.slow_mul c hc).symm

theorem fast_mul_self (hK : IsCrossover K P Q) : P * P = P := by
  refine tendsto_nhds_unique (hK.tendsto_atTop.const_mul P) (hK.tendsto_atTop.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (hK.fast_mul c hc).symm

theorem fast_mem_rowStochastic (hK : IsCrossover K P Q) : P ∈ rowStochastic ℝ n := by
  refine mem_rowStochastic.2 ⟨fun i j => ?_, ?_⟩
  · have hent : Tendsto (fun c => K c i j) atTop (𝓝 (P i j)) :=
      ((continuous_id.matrix_elem i j).tendsto P).comp hK.tendsto_atTop
    refine ge_of_tendsto hent ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact nonneg_of_mem_rowStochastic (hK.stochastic c hc)
  · have hcont : Continuous fun M : Matrix n n ℝ => M *ᵥ (1 : n → ℝ) :=
      continuous_id.matrix_mulVec continuous_const
    refine tendsto_nhds_unique ((hcont.tendsto P).comp hK.tendsto_atTop)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with c hc
    exact (one_vecMul_of_mem_rowStochastic (hK.stochastic c hc)).symm

/-- `K(c) = UH(c)V`. -/
theorem eq_mul_compress_mul (hK : IsCrossover K P Q) (hs : IsSplitting P U V) {c : ℝ}
    (hc : 0 < c) : K c = U * compress V K U c * V := by
  calc K c = P * K c * P := by rw [hK.fast_mul c hc, hK.mul_fast c hc]
    _ = U * compress V K U c * V := by
      rw [hs.eq_mul, compress]
      simp only [Matrix.mul_assoc]

/-- The compressed family satisfies `markov:eq:compressed-identity` and `H(c) → VPU = I`. -/
theorem isPseudoResolvent (hK : IsCrossover K P Q) (hs : IsSplitting P U V) :
    IsPseudoResolvent (compress V K U) where
  resolvent_identity c e hc he hce := by
    have h1 : compress V K U c * compress V K U e = V * (K c * K e) * U := by
      calc compress V K U c * compress V K U e = V * (K c * (U * V)) * K e * U := by
            simp only [compress, Matrix.mul_assoc]
        _ = V * (K c * K e) * U := by
            rw [← hs.eq_mul, hK.mul_fast c hc]
            simp only [Matrix.mul_assoc]
    rw [h1]
    calc (e - c) • (V * (K c * K e) * U) = V * ((e - c) • (K c * K e)) * U := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = e • compress V K U c - c • compress V K U e := by
          rw [hK.resolvent_identity c e hc he hce, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
          rfl
  tendsto_atTop := by
    have h := tendsto_compress (V := V) (U := U) hK.tendsto_atTop
    have hVPU : V * P * U = 1 := by
      rw [hs.eq_mul, ← Matrix.mul_assoc, hs.mul_eq_one, Matrix.one_mul, hs.mul_eq_one]
    rwa [hVPU] at h

/-- `U Q' V = Q` for the compressed slow endpoint `Q' = VQU`. -/
theorem mul_zeroProj_mul (hK : IsCrossover K P Q) (hs : IsSplitting P U V) :
    U * (V * Q * U) * V = Q := by
  calc U * (V * Q * U) * V = (U * V) * Q * (U * V) := by simp only [Matrix.mul_assoc]
    _ = Q := by rw [← hs.eq_mul, hK.fast_mul_slow, hK.slow_mul_fast]

/-- `rank (VQU) = rank Q`. -/
theorem rank_zeroProj (hK : IsCrossover K P Q) (hs : IsSplitting P U V) :
    (V * Q * U).rank = Q.rank := by
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · calc Q.rank = (U * (V * Q * U) * V).rank := by rw [hK.mul_zeroProj_mul hs]
      _ ≤ (U * (V * Q * U)).rank := rank_mul_le_left _ _
      _ ≤ (V * Q * U).rank := rank_mul_le_right _ _

end IsCrossover

omit [DecidableEq n] in
/-- `rank P = p`, the number of classes of the splitting. -/
theorem IsSplitting.rank_eq (hs : IsSplitting P U V) : P.rank = Fintype.card p := by
  apply le_antisymm
  · rw [hs.eq_mul]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  · have h1 : V * P * U = 1 := by
      rw [hs.eq_mul, ← Matrix.mul_assoc, hs.mul_eq_one, Matrix.one_mul, hs.mul_eq_one]
    calc Fintype.card p = (1 : Matrix p p ℝ).rank := rank_one.symm
      _ = (V * P * U).rank := by rw [h1]
      _ ≤ (V * P).rank := rank_mul_le_left _ _
      _ ≤ P.rank := rank_mul_le_right _ _

omit [DecidableEq n] in
/-- Ordering the classes differently only permutes the effective generator. -/
theorem effectiveGenerator_compress_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ p) :
    effectiveGenerator (compress (V.submatrix σ id) K (U.submatrix id σ)) =
      (effectiveGenerator (compress V K U)).submatrix σ σ := by
  rw [compress_submatrix, effectiveGenerator_submatrix]

/-- `markov:thm:effective`, for an arbitrary splitting `P = UV` of the fast endpoint and a
family `K` with the crossover properties `IsCrossover` (the conclusions of
`markov:lem:resolvent`, `markov:thm:leading` and `markov:thm:flag`). Put `H(c) = VK(c)U` and
`Q' = VQU`. There is a unique `G` with `H(c) = c(cI + G)⁻¹` and `K(c) = U c(cI + G)⁻¹ V` for
all real `c > 0`; it is `G = H(1)⁻¹ - I` and is a real row Laplacian. `Q'` is the limit of
`H(c)` as `c → 0⁺`; it is the zero-eigenvalue projection of `G` (idempotent, `GQ' = Q'G = 0`,
range `ker G`, kernel `range G`); the zero eigenvalue is semisimple; `UQ'V = Q` and
`rank Q' = rank Q`; the kernel of `G` has dimension `rank Q`; and
`rank G + rank Q = rank P = p`, the number of classes of the splitting. -/
theorem effective_reconstruction (hK : IsCrossover K P Q) (hs : IsSplitting P U V) :
    ∃ G : Matrix p p ℝ, G = (compress V K U 1)⁻¹ - 1 ∧
      (∀ G' : Matrix p p ℝ, (∀ c : ℝ, 0 < c → compress V K U c = Markov.resolvent G' c ∧
          K c = U * Markov.resolvent G' c * V) ↔ G' = G) ∧
      IsRowLaplacian G ∧
      Tendsto (compress V K U) (𝓝[>] 0) (𝓝 (V * Q * U)) ∧
      (V * Q * U) * (V * Q * U) = V * Q * U ∧ G * (V * Q * U) = 0 ∧ (V * Q * U) * G = 0 ∧
      LinearMap.ker G.mulVecLin = LinearMap.range (V * Q * U).mulVecLin ∧
      LinearMap.ker (V * Q * U).mulVecLin = LinearMap.range G.mulVecLin ∧
      (∀ y : p → ℝ, G *ᵥ (G *ᵥ y) = 0 → G *ᵥ y = 0) ∧
      U * (V * Q * U) * V = Q ∧ (V * Q * U).rank = Q.rank ∧
      Module.finrank ℝ (LinearMap.ker G.mulVecLin) = Q.rank ∧
      G.rank + Q.rank = P.rank ∧ P.rank = Fintype.card p := by
  have hH := hK.isPseudoResolvent hs
  have h0 : Tendsto (compress V K U) (𝓝[>] 0) (𝓝 (V * Q * U)) :=
    tendsto_compress hK.tendsto_zero
  have hst : ∀ c : ℝ, 0 < c → compress V K U c ∈ rowStochastic ℝ p :=
    fun c hc => hs.compress_mem_rowStochastic (hK.stochastic c hc)
  obtain ⟨-, hlap, hidem, hGQ, hQG, hker, hkerQ, hss, hfin, hrank⟩ :=
    effective_core hH hst h0
  have hG := hH.isGenerator_effectiveGenerator
  refine ⟨effectiveGenerator (compress V K U), rfl, fun G' => ⟨fun h => ?_, ?_⟩, hlap, h0,
    hidem, hGQ, hQG, hker, hkerQ, hss, hK.mul_zeroProj_mul hs, hK.rank_zeroProj hs, ?_, ?_,
    hs.rank_eq⟩
  · exact hH.eq_effectiveGenerator_of_resolvent fun c hc => (h c hc).1
  · rintro rfl c hc
    refine ⟨hG.eq_resolvent hc, ?_⟩
    rw [← hG.eq_resolvent hc]
    exact hK.eq_mul_compress_mul hs hc
  · rw [hfin, hK.rank_zeroProj hs]
  · rw [← hK.rank_zeroProj hs, hrank, hs.rank_eq]

/-- The canonical splitting of `markov:lem:splitting` (`splitU`, `splitV`, indexed by the
closed communicating classes of `P`) is a splitting of the fast endpoint. -/
theorem IsCrossover.isSplitting_canonical (hK : IsCrossover K P Q) :
    IsSplitting P (StochasticIdempotent.splitU P) (StochasticIdempotent.splitV P) where
  U_nonneg := StochasticIdempotent.splitU_nonneg hK.fast_mem_rowStochastic
  V_nonneg := StochasticIdempotent.splitV_nonneg hK.fast_mem_rowStochastic
  U_sum := StochasticIdempotent.sum_splitU hK.fast_mem_rowStochastic hK.fast_mul_self
  V_sum := StochasticIdempotent.sum_splitV hK.fast_mem_rowStochastic hK.fast_mul_self
  eq_mul := (StochasticIdempotent.splitU_mul_splitV hK.fast_mem_rowStochastic
    hK.fast_mul_self).symm
  mul_eq_one := StochasticIdempotent.splitV_mul_splitU hK.fast_mem_rowStochastic
    hK.fast_mul_self

open StochasticIdempotent in
/-- `markov:thm:effective` for the canonical splitting `P = UV` of `markov:lem:splitting`
(`U = splitU P`, `V = splitV P`, indexed by the closed communicating classes of `P`), under
the crossover properties `IsCrossover`: the conclusions of `effective_reconstruction`, with
`rank P` equal to the number of closed classes. The source's clause that ordering the classes
differently only permutes `G` is `IsSplitting.submatrix` together with
`effectiveGenerator_compress_submatrix`. -/
theorem effective_reconstruction_canonical (hK : IsCrossover K P Q) :
    ∃ G : Matrix (closedClasses P) (closedClasses P) ℝ,
      G = (compress (splitV P) K (splitU P) 1)⁻¹ - 1 ∧
      (∀ G', (∀ c : ℝ, 0 < c → compress (splitV P) K (splitU P) c = Markov.resolvent G' c ∧
          K c = splitU P * Markov.resolvent G' c * splitV P) ↔ G' = G) ∧
      IsRowLaplacian G ∧
      Tendsto (compress (splitV P) K (splitU P)) (𝓝[>] 0) (𝓝 (splitV P * Q * splitU P)) ∧
      (splitV P * Q * splitU P) * (splitV P * Q * splitU P) = splitV P * Q * splitU P ∧
      G * (splitV P * Q * splitU P) = 0 ∧ (splitV P * Q * splitU P) * G = 0 ∧
      LinearMap.ker G.mulVecLin = LinearMap.range (splitV P * Q * splitU P).mulVecLin ∧
      LinearMap.ker (splitV P * Q * splitU P).mulVecLin = LinearMap.range G.mulVecLin ∧
      (∀ y, G *ᵥ (G *ᵥ y) = 0 → G *ᵥ y = 0) ∧
      splitU P * (splitV P * Q * splitU P) * splitV P = Q ∧
      (splitV P * Q * splitU P).rank = Q.rank ∧
      Module.finrank ℝ (LinearMap.ker G.mulVecLin) = Q.rank ∧
      G.rank + Q.rank = P.rank ∧ P.rank = (closedClasses P).card := by
  obtain ⟨G, hG, huniq, hlap, h0, hidem, hGQ, hQG, hker, hkerQ, hss, hUQV, hrQ, hfin, hrank,
    hrP⟩ := effective_reconstruction hK hK.isSplitting_canonical
  refine ⟨G, hG, huniq, hlap, h0, hidem, hGQ, hQG, hker, hkerQ, hss, hUQV, hrQ, hfin, hrank, ?_⟩
  rw [hrP, Fintype.card_coe]

end Crossover

end

end Surreal.MarkovEffective

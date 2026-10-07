import OAI.Combinatorics.Progressions.Estimates.RelativePatchRecoveredEndpoint
import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialBufferedScore
import OAI.Combinatorics.Progressions.Sampling.NativeMarkedFreezingSliceScore

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_spatially_frozen_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q : ℕ) (hq : 0 < q)
    (score : (∀ i, Fin (N i)) → ℝ) (F : (ι → ℝ) → (∀ i, Fin (N i)) → ℝ)
    (Λ : ℝ≥0) (hF : ∀ x, LipschitzWith Λ (fun z => F z x))
    {C τ ρ θ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hscoreBound : ∀ x, |score x| ≤ 1)
    (hcap : ∀ x, F (normalizedPoint x) x ∈ Set.Icc (0 : ℝ) C)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 x, score x * F (normalizedPoint x) x)
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      τ < 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * F A.center (A.point j) := by
  obtain ⟨H, hH, hfit, hwidth, hlower⟩ := exists_box_block_mesh N q hq hρ hρ1 hlarge
  let P := fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)
  let L : ι → ℝ := fun i => θ * H i / (2 * (Fintype.card ι + 1))
  have hL (i) : 0 ≤ L i := by dsimp only [L]; positivity
  have hsmall : (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) ≤ θ :=
    boxBlock_short_side_budget N H q hN hH hfit hθ.le
  have hwidthP (a : ∀ i, (P i).Label) (i) :
      ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i := by
    have hlen : ((P i).length (a i) : ℝ) ≤ H i := by
      exact_mod_cast truncatedProgressionLength_le (N i) (progressionBlockStart (a i)) q (H i)
    exact (mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg q)).trans (hwidth i)
  obtain ⟨a, ha, hs⟩ := exists_long_spatially_frozen_box P hN L hL score F Λ hF hC hτ hρ.le
    hscoreBound hcap hwidthP hscore
    ((add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hC)).trans_lt hbudget)
  let A := ResidueBoxSlice.ofBlocks H hq hH a
  have hlen (i) : θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ) := by
    apply le_trans _ (ha i)
    dsimp only [L]
    calc
      _ = θ * (ρ * N i / (2 * q)) / (2 * (Fintype.card ι + 1)) := by
        have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
        have hn0 : (Fintype.card ι : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hlower i) hθ.le) (by positivity)
  refine ⟨A, hlen, ?_, ?_⟩
  · intro i
    have hp : (0 : ℝ) < θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) := by
      have hNi : (0 : ℝ) < N i := by exact_mod_cast hN i
      have hqi : (0 : ℝ) < q := by exact_mod_cast hq
      positivity
    exact_mod_cast hp.trans_le (hlen i)
  · have hcenter : A.center = normalizedStart P a := rfl
    have hpoint (j : ∀ i, Fin (A.length i)) : A.point j = point P a j :=
      ResidueBoxSlice.ofBlocks_point H hq hH a j
    simpa only [hcenter, hpoint] using hs

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def bufferedSpatialWeight {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (z : Θ) (u : Ω) : ℝ :=
  ∑' b, χ.value (fun i => x u i - (b i : ℝ)) * G z u b * T u b

theorem bufferedSpatialWeight_eq_nearest {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (z : Θ) (u : Ω) :
    bufferedSpatialWeight χ x T G z u =
      χ.value (fun i => x u i - (nearestIntegerLift (x u) i : ℝ)) *
        G z u (nearestIntegerLift (x u)) * T u (nearestIntegerLift (x u)) := by
  simpa only [bufferedSpatialWeight, mul_assoc] using
    χ.buffered_sum_eq_nearest (x u) (fun b => G z u b * T u b)

theorem bufferedSpatialWeight_mem_Icc {Ω Θ : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) {C : ℝ}
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ z u b, G z u b ∈ Set.Icc (0 : ℝ) C) (z : Θ) (u : Ω) :
    bufferedSpatialWeight χ x T G z u ∈ Set.Icc (0 : ℝ) C := by
  rw [bufferedSpatialWeight_eq_nearest]
  have ht := hT u (nearestIntegerLift (x u))
  have hg := hG z u (nearestIntegerLift (x u))
  constructor
  · exact mul_nonneg (mul_nonneg (χ.nonneg _) hg.1) ht.1
  · calc
      _ = (χ.value _ * T u (nearestIntegerLift (x u))) * G z u (nearestIntegerLift (x u)) := by ring
      _ ≤ G z u (nearestIntegerLift (x u)) :=
        mul_le_of_le_one_left hg.1 ((mul_le_of_le_one_left ht.1 (χ.le_one _)).trans ht.2)
      _ ≤ C := hg.2

theorem bufferedSpatialWeight_lipschitz {Ω Θ : Type*} [PseudoMetricSpace Θ] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (G : Θ → Ω → (Fin m → ℤ) → ℝ) (Λ : ℝ≥0)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ u b, LipschitzWith Λ (fun z => G z u b)) (u : Ω) :
    LipschitzWith Λ (fun z => bufferedSpatialWeight χ x T G z u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [bufferedSpatialWeight_eq_nearest, bufferedSpatialWeight_eq_nearest, Real.dist_eq]
  let b := nearestIntegerLift (x u)
  let c := χ.value (fun i => x u i - (b i : ℝ)) * T u b
  have hc0 : 0 ≤ c := mul_nonneg (χ.nonneg _) (hT u b).1
  have hc1 : c ≤ 1 := (mul_le_of_le_one_left (hT u b).1 (χ.le_one _)).trans (hT u b).2
  have heq : χ.value (fun i => x u i - (b i : ℝ)) * G z u b * T u b -
      χ.value (fun i => x u i - (b i : ℝ)) * G w u b * T u b = c * (G z u b - G w u b) := by
    dsimp only [c]
    ring
  change |χ.value _ * G z u b * T u b - χ.value _ * G w u b * T u b| ≤ _
  rw [heq, abs_mul, abs_of_nonneg hc0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans
    (by simpa only [Real.dist_eq] using (hG u b).dist_le_mul z w)

theorem exists_spatially_frozen_buffered_slice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q : ℕ) (hq : 0 < q) {m : ℕ}
    (χ : PatchKernel m) (x : (∀ i, Fin (N i)) → Fin m → ℝ)
    (T : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    (G : (ι → ℝ) → (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    (score : (∀ i, Fin (N i)) → ℝ) (Λ : ℝ≥0)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ u b, LipschitzWith Λ (fun z => G z u b))
    {C τ ρ θ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hGcap : ∀ z u b, G z u b ∈ Set.Icc (0 : ℝ) C)
    (hscoreBound : ∀ u, |score u| ≤ 1) (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 u, score u * bufferedSpatialWeight χ x T G (BoxProgressionPartition.normalizedPoint u) u)
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, θ * ρ * N i / (4 * q * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      τ < 𝔼 j : (∀ i, Fin (A.length i)),
        score (A.point j) * bufferedSpatialWeight χ x T G A.center (A.point j) := by
  exact exists_spatially_frozen_slice N hN q hq score (bufferedSpatialWeight χ x T G) Λ
    (bufferedSpatialWeight_lipschitz χ x T G Λ hT hG) hC hτ hρ hρ1 hθ hscoreBound
    (fun u => bufferedSpatialWeight_mem_Icc χ x T G hT hGcap _ u) hlarge hscore hbudget

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal BigOperators

theorem ResidueBoxSlice.point_cast {ι : Type*} {N : ι → ℕ} {q : ℕ}
    (A : ResidueBoxSlice N q) (j : ∀ i, Fin (A.length i)) :
    (fun i => ((A.point j i).val : ZMod q)) = fun i => (A.start i : ZMod q) := by
  funext i
  simp [ResidueBoxSlice.point]

theorem exists_spatially_localized_patch {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (ι → ℝ) → (ι → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ L C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith L (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : (∀ i, Fin (N i)) → σ → ℝ) (score : (∀ i, Fin (N i)) → ℝ)
    {τ ρ θ S : ℝ} (hτ : 0 ≤ τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hθ : 0 < θ)
    (hscoreBound : ∀ u, |score u| ≤ 1) (hlarge : ∀ i, 2 * (q₀ : ℝ) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 u, score u * ∑' b : Fin m → ℤ,
      χ.value (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) b
          (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (b i : ℝ)) *
        B.value (Sum.elim (t u) (fun i => (b i : ℝ))))
    (hbudget : τ + Λ * ρ + C * θ < S) :
    ∃ (A : ResidueBoxSlice N q₀) (Q : PolynomialPatch σ s (d + E)),
      (∀ i, θ * ρ * N i / (4 * q₀ * (Fintype.card ι + 1)) ≤ (A.length i : ℝ)) ∧
      (∀ i, 0 < A.length i) ∧
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      τ / ((C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * Q.value (t (A.point j)) := by
  let x : (∀ i, Fin (N i)) → Fin m → ℝ :=
    fun u => realIntegerMatrix M (fun j => aeval (t u) (P j))
  let T : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ :=
    fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))
  let W : (ι → ℝ) → (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ :=
    fun z u b => G z (fun i => ((u i).val : ZMod q₀)) b (fun i => x u i - (b i : ℝ))
  obtain ⟨A, hlength, hpos, hs⟩ := exists_spatially_frozen_buffered_slice N hN q₀ hq₀ χ x T W
    score Λ (fun u b => B.value_mem_Icc _) (fun u b => hGspace _ _ _) C.coe_nonneg hτ hρ hρ1 hθ
    (fun z u b => hGcap _ _ _ _) hscoreBound hlarge hscore hbudget
  let F := G A.center (fun i => (A.start i : ZMod q₀))
  have hlocalized : τ ≤ 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * ∑' b : Fin m → ℤ,
      χ.value (fun i => x (A.point j) i - (b i : ℝ)) *
        F b (fun i => x (A.point j) i - (b i : ℝ)) * T (A.point j) b := by
    apply hs.le.trans_eq
    apply Finset.expect_congr rfl
    intro j _
    apply congrArg (fun a => score (A.point j) * a)
    apply tsum_congr
    intro b
    change χ.value _ * G A.center (fun i => ((A.point j i).val : ZMod q₀)) b _ * _ = _
    rw [A.point_cast j]
  obtain ⟨Q, hQlip, hQscore⟩ := exists_fiberwise_weighted_patch w hw hws hmono P hP p B χ F L C hC
    (hGlift A.center _) (hGcap A.center _) M K hM hweight (hinvariant A.center _) q hq hmesh
    (fun j => t (A.point j)) (fun j => score (A.point j)) hlocalized
  exact ⟨A, Q, hlength, hpos, hQlip, hQscore⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def spatialPatchExtractionCost (L : ℝ) : ℝ := 20 * (L + 1) ^ 2

private theorem extraction_exp_two {L : ℝ} (hL : 1 ≤ L) : 2 ≤ Real.exp L := by
  linarith only [hL, Real.add_one_le_exp L]

private theorem extraction_exp_four {L : ℝ} (hL : 1 ≤ L) : 4 ≤ Real.exp (2 * L) := by
  have h := extraction_exp_two hL
  have he : Real.exp (2 * L) = Real.exp L * Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith

theorem spatialPatchExtraction_radius {L : ℝ} (hL : 1 ≤ L) :
    0 < Real.exp (-4 * L) ∧ Real.exp (-4 * L) ≤ 1 := by
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩

theorem spatialPatchExtraction_strict_budget {L Λ C S : ℝ}
    (hL : 1 ≤ L) (hΛ : Λ ≤ Real.exp L) (hC : C ≤ Real.exp L)
    (hS : Real.exp (-L) ≤ S) :
    Real.exp (-3 * L) + Λ * Real.exp (-4 * L) + C * Real.exp (-4 * L) < S := by
  have hprod : Real.exp L * Real.exp (-4 * L) = Real.exp (-3 * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hΛ' : Λ * Real.exp (-4 * L) ≤ Real.exp (-3 * L) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right hΛ (Real.exp_nonneg _)
  have hC' : C * Real.exp (-4 * L) ≤ Real.exp (-3 * L) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
  have he : Real.exp (2 * L) * Real.exp (-3 * L) = Real.exp (-L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right (extraction_exp_four hL) (Real.exp_nonneg (-3 * L))
  rw [he] at hh
  have hp := Real.exp_pos (-3 * L)
  linarith

theorem spatialPatchExtraction_side_lower {L : ℝ} (hL : 1 ≤ L)
    (q₀ n : ℕ) (hq₀ : 0 < q₀) (hq₀bound : (q₀ : ℝ) ≤ Real.exp L)
    (hn : (n : ℝ) ≤ L) :
    Real.exp (-spatialPatchExtractionCost L) ≤
      Real.exp (-4 * L) * Real.exp (-4 * L) / (4 * (q₀ : ℝ) * (n + 1)) := by
  have hdenpos : 0 < 4 * (q₀ : ℝ) * (n + 1) := by positivity
  have hnexp : (n : ℝ) + 1 ≤ Real.exp L := by
    linarith only [hn, Real.add_one_le_exp L]
  have hden : 4 * (q₀ : ℝ) * (n + 1) ≤ Real.exp (4 * L) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp L * Real.exp L := by
        exact mul_le_mul (mul_le_mul (extraction_exp_four hL) hq₀bound
          (by positivity) (Real.exp_nonneg _)) hnexp (by positivity) (by positivity)
      _ = Real.exp (4 * L) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hcost : 12 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  have hbase : Real.exp (-12 * L) ≤
      Real.exp (-4 * L) * Real.exp (-4 * L) / (4 * (q₀ : ℝ) * (n + 1)) := by
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ Real.exp (-12 * L) * Real.exp (4 * L) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = Real.exp (-4 * L) * Real.exp (-4 * L) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  exact (Real.exp_le_exp.mpr (by linarith : -spatialPatchExtractionCost L ≤ -12 * L)).trans hbase

theorem spatialPatchExtraction_large {L N : ℝ} (hL : 1 ≤ L)
    (q₀ : ℕ) (hq₀ : (q₀ : ℝ) ≤ Real.exp L)
    (hN : Real.exp (spatialPatchExtractionCost L) ≤ N) :
    2 * (q₀ : ℝ) ≤ Real.exp (-4 * L) * N := by
  have hcost : 6 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  calc
    _ ≤ 2 * Real.exp L := mul_le_mul_of_nonneg_left hq₀ (by norm_num)
    _ ≤ Real.exp L * Real.exp L :=
      mul_le_mul_of_nonneg_right (extraction_exp_two hL) (Real.exp_nonneg L)
    _ = Real.exp (2 * L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-4 * L + spatialPatchExtractionCost L) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-4 * L) * Real.exp (spatialPatchExtractionCost L) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg _)

theorem spatialPatchExtraction_gain_lower {L C : ℝ} (hL : 1 ≤ L)
    (hCpos : 0 < C) (hC : C ≤ Real.exp L) (q d : ℕ) (hq : 0 < q)
    (hqd : (q : ℝ) ^ d ≤ Real.exp (6 * L ^ 2)) :
    Real.exp (-spatialPatchExtractionCost L) ≤
      Real.exp (-3 * L) / (C * (q : ℝ) ^ d) := by
  have hdenpos : 0 < C * (q : ℝ) ^ d := by positivity
  have hden : C * (q : ℝ) ^ d ≤ Real.exp (L + 6 * L ^ 2) := by
    calc
      _ ≤ Real.exp L * Real.exp (6 * L ^ 2) :=
        mul_le_mul hC hqd (by positivity) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hcost : 6 * L ^ 2 + 4 * L ≤ spatialPatchExtractionCost L := by
    unfold spatialPatchExtractionCost
    nlinarith [sq_nonneg L]
  have hbase : Real.exp (-(6 * L ^ 2 + 4 * L)) ≤
      Real.exp (-3 * L) / (C * (q : ℝ) ^ d) := by
    apply (le_div_iff₀ hdenpos).mpr
    calc
      _ ≤ Real.exp (-(6 * L ^ 2 + 4 * L)) * Real.exp (L + 6 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = Real.exp (-3 * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact (Real.exp_le_exp.mpr (by linarith :
    -spatialPatchExtractionCost L ≤ -(6 * L ^ 2 + 4 * L))).trans hbase

end Erdos3

end

section

namespace Erdos3

theorem spatialPatchExtractionCost_le_power {p L : ℝ} {a : ℕ}
    (hp : 2 ≤ p) (hL : 0 ≤ L) (hbudget : L ≤ (p + 2) ^ a) :
    spatialPatchExtractionCost L ≤ (p + 2) ^ (2 * a + 4) := by
  have hb : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ a := one_le_pow₀ hb
  have hplus : L + 1 ≤ 2 * (p + 2) ^ a := by linarith
  have hfour : (80 : ℝ) ≤ (p + 2) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4)
      (by linarith : (4 : ℝ) ≤ p + 2) 4
    norm_num at h
    linarith
  unfold spatialPatchExtractionCost
  calc
    20 * (L + 1) ^ 2 ≤ 20 * (2 * (p + 2) ^ a) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hplus 2) (by norm_num)
    _ = 80 * ((p + 2) ^ a) ^ 2 := by ring
    _ ≤ (p + 2) ^ 4 * ((p + 2) ^ a) ^ 2 :=
      mul_le_mul_of_nonneg_right hfour (sq_nonneg _)
    _ = (p + 2) ^ (2 * a + 4) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem relativePatchSliceScore_reparamPatch {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target (S.reparamPatch A) =
      (𝔼 j : (∀ i, Fin (S.length i)),
        (f (fun i => ((S.point j i).val : ℤ)) - target) *
          A.value (fun i => ((S.point j i).val : ℝ))) := by
  unfold relativePatchSliceScore
  apply Finset.expect_congr rfl
  intro j _
  rw [S.reparamPatch_value]

theorem relativePatchSliceConclusion_of_spatially_localized_patch
    {X : Type*} [Fintype X] {s d q rankBound : ℕ} {N : X → ℕ}
    (S : ResidueBoxSlice N q) (hq : 0 < q)
    (f : (X → ℤ) → ℝ) (target cost gain : ℝ)
    (A : PolynomialPatch X s d) (lip : ℝ≥0)
    (hrank : d ≤ rankBound)
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤ S.length i)
    (hlip : A.kernel.lip ≤ lip)
    (hbudget : (d : ℝ) + Real.log (1 + (lip : ℝ)) ≤ cost)
    (hgain : Real.exp (-cost) ≤ gain)
    (hscore : gain ≤
      (𝔼 j : (∀ i, Fin (S.length i)),
        (f (fun i => ((S.point j i).val : ℤ)) - target) *
          A.value (fun i => ((S.point j i).val : ℝ)))) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  refine ⟨q, hq, S, d, S.reparamPatch A, hlength, hrank, ?_, ?_⟩
  · apply le_trans _ hbudget
    unfold relativePatchComplexity
    rw [S.reparamPatch_kernel]
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    exact add_le_add le_rfl (show (A.kernel.lip : ℝ) ≤ lip from hlip)
  · rw [relativePatchSliceScore_reparamPatch]
    exact hgain.trans hscore

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

theorem relativePatchSliceConclusion_of_discounted_spatial_buffered_score
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m rankBound : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial X ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (X ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (X → ℝ) → (X → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ L C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith L (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (full : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    {lam δ ε gain surplus meshWidth shortLoss cost : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) ≤ full u β)
    (hupper : ∀ u β, full u β ≤ (1 + δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)))
    (hscore : gain ≤ 𝔼 u : (∀ i, Fin (N i)),
      (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin m → ℤ,
        χ.value (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) * full u β *
        B.value (Sum.elim (fun i => ((u i).val : ℝ)) (fun i => (β i : ℝ))))
    (hsurplus : 0 ≤ surplus) (hmeshWidth : 0 < meshWidth) (hmeshWidth1 : meshWidth ≤ 1)
    (hshortLoss : 0 < shortLoss) (hlarge : ∀ i, 2 * (q₀ : ℝ) ≤ meshWidth * N i)
    (hfreeze : surplus + Λ * meshWidth + C * shortLoss < gain / (1 + δ))
    (hrank : d + E ≤ rankBound)
    (hlength : ∀ i, Real.exp (-cost) * (N i : ℝ) ≤
      shortLoss * meshWidth * N i / (4 * q₀ * (Fintype.card X + 1)))
    (hbudget : ((d + E : ℕ) : ℝ) + Real.log (1 +
      ((q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip : ℝ≥0)) ≤ cost)
    (hgain : Real.exp (-cost) ≤ surplus / ((C : ℝ) * (q : ℝ) ^ d)) :
    RelativePatchSliceConclusion s N f ((1 - ε) * lam) rankBound cost := by
  let t : (∀ i, Fin (N i)) → X → ℝ := fun u i => ((u i).val : ℝ)
  let input : (∀ i, Fin (N i)) → ℝ := fun u => f (fun i => ((u i).val : ℤ))
  let x : (∀ i, Fin (N i)) → Fin m → ℝ :=
    fun u => realIntegerMatrix M (fun j => aeval (t u) (P j))
  let T := fun (u : ∀ i, Fin (N i)) (β : Fin m → ℤ) =>
    B.value (Sum.elim (t u) (fun i => (β i : ℝ)))
  let reduced := fun (u : ∀ i, Fin (N i)) (β : Fin m → ℤ) =>
    G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
      (fun i => x u i - (β i : ℝ))
  have hinput (u : ∀ i, Fin (N i)) : input u ∈ Set.Icc (0 : ℝ) 1 :=
    hf _ ((mem_integerBox N _).mpr (fun i =>
      ⟨by positivity, by exact_mod_cast (u i).isLt⟩))
  have htarget : (1 - ε) * lam ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr hε.2) hlam.1
    · exact (mul_le_of_le_one_left hlam.1 (by linarith only [hε.1])).trans hlam.2
  have hdiscounted := buffered_score_discount χ x T full reduced input hδ
    (fun u => (hinput u).1) hlam.1 (fun u β => (B.value_mem_Icc _).1)
    (fun u β => (hGcap _ _ _ _).1) hlower hupper hdiscount hscore
  obtain ⟨S, Q, hlen, _, hQl, hQs⟩ := exists_spatially_localized_patch N hN q₀ hq₀
    w hw hws hmono P hP p B χ M K hM hweight G Λ L C hC hGspace hGlift hGcap
    hinvariant q hq hmesh t (fun u => input u - (1 - ε) * lam)
    hsurplus hmeshWidth hmeshWidth1 hshortLoss
    (fun u => abs_le.mpr ⟨by linarith only [(hinput u).1, htarget.2],
      by linarith only [(hinput u).2, htarget.1]⟩)
    hlarge hdiscounted hfreeze
  apply relativePatchSliceConclusion_of_spatially_localized_patch S hq₀ f
    ((1 - ε) * lam) cost (surplus / ((C : ℝ) * (q : ℝ) ^ d)) Q _ hrank
    (fun i => (hlength i).trans (hlen i)) hQl hbudget hgain
  apply hQs.trans_eq
  apply Finset.expect_congr
  · ext j
    simp
  · intro j _
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialPatchExtractionMesh (L : ℝ) : ℕ :=
  ⌈Real.exp (5 * L)⌉₊

theorem spatialPatchExtractionMesh_exp_le (L : ℝ) :
    Real.exp (5 * L) ≤ (spatialPatchExtractionMesh L : ℝ) := Nat.le_ceil _

theorem spatialPatchExtractionMesh_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (spatialPatchExtractionMesh L : ℝ) ≤ Real.exp (6 * L) := by
  have hfive : 0 ≤ 5 * L := by linarith
  exact (ceil_exp_le_exp_add_one hfive).trans (Real.exp_le_exp.mpr (by linarith))

theorem spatialPatchExtractionMesh_bounds {L : ℝ} (hL : 1 ≤ L)
    (K : ℝ≥0) (hK : (K : ℝ) ≤ Real.exp L) :
    8 ≤ spatialPatchExtractionMesh L ∧
      16 * (K : ℝ) ≤ (spatialPatchExtractionMesh L : ℝ) ∧
      (spatialPatchExtractionMesh L : ℝ) ≤ Real.exp (6 * L) := by
  have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hfour : (16 : ℝ) ≤ Real.exp (4 * L) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp 4
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ)^4 = 16 by norm_num] using hp
  have hlarge : 16 * Real.exp L ≤ Real.exp (5 * L) := by
    calc
      _ ≤ Real.exp (4 * L) * Real.exp L :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hq := spatialPatchExtractionMesh_exp_le L
  have height : (8 : ℝ) ≤ (spatialPatchExtractionMesh L : ℝ) := by
    linarith
  refine ⟨by exact_mod_cast height, ?_, spatialPatchExtractionMesh_le_exp hL⟩
  exact (mul_le_mul_of_nonneg_left hK (by norm_num)).trans (hlarge.trans hq)

theorem spatialPatchExtractionMesh_pow_le {L : ℝ} (hL : 1 ≤ L)
    (d : ℕ) (hd : (d : ℝ) ≤ L) :
    (spatialPatchExtractionMesh L : ℝ)^d ≤ Real.exp (6 * L^2) := by
  have hp := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _)
    (spatialPatchExtractionMesh_le_exp hL) (by linarith : 0 ≤ 6 * L) d hd
  convert hp using 1
  congr 1
  ring

theorem spatialPatchExtraction_log_complexity_le_of_mesh {L E : ℝ}
    (hL : 1 ≤ L) (hE : E ≤ L) (d q : ℕ) (hd : (d : ℝ) ≤ L)
    (hq : (q : ℝ) ≤ Real.exp (6 * L))
    (hqd : (q : ℝ)^d ≤ Real.exp (6 * L^2))
    (K χlip Llift Blip C : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hχ : (χlip : ℝ) ≤ Real.exp L)
    (hLift : (Llift : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC : 1 ≤ C) :
    ((d : ℝ) + E) + Real.log
      (1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
        ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ 20 * (L + 1)^2 := by
  let T : ℝ := 6 * L^2 + 6 * L
  have hL0 : 0 ≤ L := by linarith
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hTtwo : 2 * L ≤ T := by dsimp only [T]; nlinarith [sq_nonneg L]
  have hTL : L ≤ T := by linarith
  have hbase : 1 ≤ Real.exp T := Real.one_le_exp hT0
  have hpbase : 1 ≤ Real.exp (6 * L^2) := Real.one_le_exp (by positivity)
  have hinner : 2 * (q : ℝ)^d + 1 ≤ 3 * Real.exp (6 * L^2) := by linarith
  have hmesh : (q : ℝ) * (2 * (q : ℝ)^d + 1) ≤ 3 * Real.exp T := by
    calc
      _ ≤ Real.exp (6 * L) * (3 * Real.exp (6 * L^2)) :=
        mul_le_mul hq hinner (by positivity) (Real.exp_nonneg _)
      _ = _ := by dsimp only [T]; rw [Real.exp_add]; ring
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hdiv : (Llift : ℝ) / C ≤ Llift := div_le_self Llift.coe_nonneg hCr
  have hsum : (χlip : ℝ) + (Llift : ℝ) / C ≤ 2 * Real.exp L := by linarith
  have hlift : ((χlip : ℝ) + (Llift : ℝ) / C) * K ≤ 2 * Real.exp T := by
    calc
      _ ≤ (2 * Real.exp L) * Real.exp L :=
        mul_le_mul hsum hK K.coe_nonneg (by positivity)
      _ = 2 * Real.exp (2 * L) := by rw [show 2 * L = L + L by ring, Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTtwo) (by norm_num)
  have hBlip : (Blip : ℝ) ≤ Real.exp T := hB.trans (Real.exp_le_exp.mpr hTL)
  have htotal : 1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
      ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip ≤ Real.exp (T + 7) := by
    calc
      _ ≤ 7 * Real.exp T := by linarith
      _ ≤ Real.exp 7 * Real.exp T := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (7 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog : Real.log (1 + (q : ℝ) * (2 * (q : ℝ)^d + 1) +
      ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ T + 7 :=
    (Real.log_le_iff_le_exp (by positivity)).mpr htotal
  dsimp only [T] at hlog
  nlinarith [sq_nonneg L]

theorem spatialPatchExtraction_log_complexity_le {L E : ℝ}
    (hL : 1 ≤ L) (hE : E ≤ L) (d : ℕ) (hd : (d : ℝ) ≤ L)
    (K χlip Llift Blip C : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hχ : (χlip : ℝ) ≤ Real.exp L)
    (hLift : (Llift : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC : 1 ≤ C) :
    ((d : ℝ) + E) + Real.log
      (1 + (spatialPatchExtractionMesh L : ℝ) *
        (2 * (spatialPatchExtractionMesh L : ℝ)^d + 1) +
        ((χlip : ℝ) + (Llift : ℝ) / C) * K + Blip) ≤ 20 * (L + 1)^2 :=
  spatialPatchExtraction_log_complexity_le_of_mesh hL hE d (spatialPatchExtractionMesh L) hd
    (spatialPatchExtractionMesh_le_exp hL) (spatialPatchExtractionMesh_pow_le hL d hd)
    K χlip Llift Blip C hK hχ hLift hB hC

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_spatialPatchExtraction_parameters {L S : ℝ} (hL : 1 ≤ L)
    (d E n : ℕ) (hd : (d : ℝ) ≤ L) (hE : (E : ℝ) ≤ L) (hn : (n : ℝ) ≤ L)
    (K Λ C Llift χlip Blip : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp L) (hΛ : (Λ : ℝ) ≤ Real.exp L)
    (hC : (C : ℝ) ≤ Real.exp L) (hLift : (Llift : ℝ) ≤ Real.exp L)
    (hχ : (χlip : ℝ) ≤ Real.exp L) (hB : (Blip : ℝ) ≤ Real.exp L)
    (hC1 : 1 ≤ C) (q₀ : ℕ) (hq₀ : 0 < q₀) (hq₀bound : (q₀ : ℝ) ≤ Real.exp L)
    (hS : Real.exp (-L) ≤ S) :
    ∃ (q : ℕ) (ρ θ τ : ℝ),
      8 ≤ q ∧ 16 * (K : ℝ) ≤ q ∧ 0 < ρ ∧ ρ ≤ 1 ∧ 0 < θ ∧ 0 ≤ τ ∧
      τ + (Λ : ℝ) * ρ + (C : ℝ) * θ < S ∧
      Real.exp (-spatialPatchExtractionCost L) ≤ θ * ρ / (4 * (q₀ : ℝ) * (n + 1)) ∧
      Real.exp (-spatialPatchExtractionCost L) ≤ τ / ((C : ℝ) * (q : ℝ) ^ d) ∧
      (d + E : ℝ) + Real.log
        (1 + (q : ℝ) * (2 * (q : ℝ) ^ d + 1) +
          ((χlip : ℝ) + (Llift : ℝ) / (C : ℝ)) * (K : ℝ) + (Blip : ℝ)) ≤
        spatialPatchExtractionCost L ∧
      (∀ N : ℝ, Real.exp (spatialPatchExtractionCost L) ≤ N →
        2 * (q₀ : ℝ) ≤ ρ * N) := by
  let q := spatialPatchExtractionMesh L
  obtain ⟨hq8, hqK, hqupper⟩ := spatialPatchExtractionMesh_bounds hL K hK
  obtain ⟨hρ, hρ1⟩ := spatialPatchExtraction_radius hL
  have hCpos : 0 < (C : ℝ) := by
    have hc : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC1
    linarith
  refine ⟨q, Real.exp (-4 * L), Real.exp (-4 * L), Real.exp (-3 * L),
    hq8, hqK, hρ, hρ1, hρ, (Real.exp_pos _).le,
    spatialPatchExtraction_strict_budget hL hΛ hC hS,
    spatialPatchExtraction_side_lower hL q₀ n hq₀ hq₀bound hn,
    spatialPatchExtraction_gain_lower hL hCpos hC q d (by omega)
      (spatialPatchExtractionMesh_pow_le hL d hd), ?_,
    fun N hN => spatialPatchExtraction_large hL q₀ hq₀bound hN⟩
  exact spatialPatchExtraction_log_complexity_le hL hE d hd K χlip Llift Blip C
    hK hχ hLift hB hC1

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators NNReal Classical

theorem relativePatchSliceConclusion_of_budgeted_spatial_buffered_score
    {X : Type*} [Fintype X] [DecidableEq X] (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (q₀ : ℕ) (hq₀ : 0 < q₀) {s d E m rankBound : ℕ}
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial X ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (X ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (G : (X → ℝ) → (X → ZMod q₀) → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ r b y, LipschitzWith Λ (fun z => G z r b y))
    (hGlift : ∀ z r b, LipschitzWith Llift (G z r b))
    (hGcap : ∀ z r b y, G z r b y ∈ Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ z r c k, G z r (recoveredIntegerLift M c k) = G z r c)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (full : (∀ i, Fin (N i)) → (Fin m → ℤ) → ℝ)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ u β, (1 - δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) ≤ full u β)
    (hupper : ∀ u β, full u β ≤ (1 + δ) *
      G (BoxProgressionPartition.normalizedPoint u) (fun i => ((u i).val : ZMod q₀)) β
        (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)))
    (hscore : gain ≤ 𝔼 u : (∀ i, Fin (N i)),
      (f (fun i => ((u i).val : ℤ)) - lam) * ∑' β : Fin m → ℤ,
        χ.value (fun i => realIntegerMatrix M (fun j => aeval (fun x => ((u x).val : ℝ)) (P j)) i -
          (β i : ℝ)) * full u β *
        B.value (Sum.elim (fun i => ((u i).val : ℝ)) (fun i => (β i : ℝ))))
    (hL : 1 ≤ L) (hd : (d : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (B.kernel.lip : ℝ) ≤ Real.exp L)
    (hq₀budget : (q₀ : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (N i : ℝ))
    (hrank : d + E ≤ rankBound) :
    RelativePatchSliceConclusion s N f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  obtain ⟨q, ρ, θ, surplus, hq, hmesh, hρ, hρ1, hθ, hsurplus, hfreeze,
    hside, hgain, hcomplex, hbig⟩ := exists_spatialPatchExtraction_parameters hL d E
      (Fintype.card X) hd hE hn K Λ C Llift χ.lip B.kernel.lip hKbudget hΛbudget
      hCbudget hLiftbudget hχbudget hBbudget hC q₀ hq₀ hq₀budget hgainBudget
  have hlength (i : X) : Real.exp (-spatialPatchExtractionCost L) * (N i : ℝ) ≤
      θ * ρ * N i / (4 * q₀ * (Fintype.card X + 1)) := by
    calc
      _ ≤ (θ * ρ / (4 * (q₀ : ℝ) * (Fintype.card X + 1))) * (N i : ℝ) :=
        mul_le_mul_of_nonneg_right hside (Nat.cast_nonneg _)
      _ = _ := by ring
  apply relativePatchSliceConclusion_of_discounted_spatial_buffered_score N hN q₀ hq₀
    w hw hws hmono P hP p B χ M K hM hweight G Λ Llift C hC hGspace hGlift hGcap
    hinvariant q hq hmesh f hf full hlam hδ hε hdiscount hlower hupper hscore
    hsurplus hρ hρ1 hθ (fun i => hbig (N i) (hlarge i)) hfreeze hrank
    hlength ?_ hgain
  simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one, Nat.cast_add, add_assoc] using hcomplex

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

noncomputable def scaledRetainedRecoveredG (cutoff : ℕ) (κ : ℝ)
    (v : X → ℝ) (r : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  κ * slice.retainedRecoveredG selected hB o bW hb e cutoff v r β y

theorem relativePatchSliceConclusion_of_actual_retained_forecast_score
    (hmpos : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j q, coefficients (poly j) q ∈ U j)
    (hN : ∀ i, 0 < physicalN i)
    {s r E rankBound : ℕ}
    (w : Fin r → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (Pscalar : Fin r → MvPolynomial X ℝ)
    (hP : ∀ j, Pscalar j ∈ weightedSupportLE (fun _ : X => 1) (w j))
    (p : Fin d → ℕ)
    (Bpatch : WeightedParameterPatch (X ⊕ Fin d) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel d) (M : Fin d → Fin r → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hcoords : ∀ x : X → ℤ,
      fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val) x =
        realIntegerMatrix M (fun j => MvPolynomial.aeval (fun i => (x i : ℝ)) (Pscalar j)))
    (Λ Llift C : ℝ≥0) (hC : 1 ≤ C)
    (hGspace : ∀ residue β y, LipschitzWith Λ
      (fun v => slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y))
    (hGlift : ∀ v residue β, LipschitzWith Llift
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β))
    (hGcap : ∀ v residue β y,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y ∈
        Set.Icc (0 : ℝ) C)
    (hinvariant : ∀ v residue β k,
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue
        (recoveredIntegerLift M β k) =
      slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox physicalN, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam δ ε gain L : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (haccuracy : 4 / (cutoff : ℝ) ≤ δ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hscore : gain ≤ 𝔼 x : ↥(integerBox physicalN),
      (slice.targetAt selected hB o bW hb poly hm κ x.val).re *
        bufferedScalarScore χ
          (fullTaggedBufferedCoordinates e poly (fun j => (slice.path.center j).val))
          (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ))))
          f lam x.val)
    (hL : 1 ≤ L) (hr : (r : ℝ) ≤ L) (hE : (E : ℝ) ≤ L)
    (hn : (Fintype.card X : ℝ) ≤ L)
    (hKbudget : (K : ℝ) ≤ Real.exp L) (hΛbudget : (Λ : ℝ) ≤ Real.exp L)
    (hCbudget : (C : ℝ) ≤ Real.exp L) (hLiftbudget : (Llift : ℝ) ≤ Real.exp L)
    (hχbudget : (χ.lip : ℝ) ≤ Real.exp L) (hBbudget : (Bpatch.kernel.lip : ℝ) ≤ Real.exp L)
    (hqbudget : (slice.path.referenceRetainedCRTModulus cutoff : ℝ) ≤ Real.exp L)
    (hgainBudget : Real.exp (-L) ≤ gain / (1 + δ))
    (hlarge : ∀ i, Real.exp (spatialPatchExtractionCost L) ≤ (physicalN i : ℝ))
    (hrank : r + E ≤ rankBound) :
    RelativePatchSliceConclusion s physicalN f ((1 - ε) * lam) rankBound
      (spatialPatchExtractionCost L) := by
  let full : (∀ i, Fin (physicalN i)) → (Fin d → ℤ) → ℝ := fun u β =>
    κ * slice.recoveredG selected hB o bW hb e
      (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i - (β i : ℝ))
  have hscoreFin := hscore.trans_eq
    (slice.targetAt_mean_mul_bufferedScalarScore_eq_fin selected hB o bW hb e poly hm κ χ
      (fun u β => Bpatch.value (Sum.elim (fun i => (u i : ℝ)) (fun i => (β i : ℝ)))) f lam)
  apply relativePatchSliceConclusion_of_budgeted_spatial_buffered_score physicalN hN
    (slice.path.referenceRetainedCRTModulus cutoff)
    (slice.path.referenceRetainedCRTModulus_pos cutoff)
    w hw hws hmono Pscalar hP p Bpatch χ M K hM hweight
    (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ)
    Λ Llift C hC hGspace hGlift hGcap hinvariant f hf full hlam hδ hε hdiscount
    ?_ ?_ ?_ hL hr hE hn hKbudget hΛbudget hCbudget hLiftbudget hχbudget hBbudget
    hqbudget hgainBudget hlarge hrank
  · intro u β
    have h := (slice.recoveredG_retained_comparison selected hB o bW hb e hmpos hD
      cutoff hcutoff hsmall hδ haccuracy (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i -
          (β i : ℝ))).1
    have hs := mul_le_mul_of_nonneg_left h hκ
    simpa only [full, scaledRetainedRecoveredG, map_natCast, mul_left_comm κ (1 - δ)] using hs
  · intro u β
    have h := (slice.recoveredG_retained_comparison selected hB o bW hb e hmpos hD
      cutoff hcutoff hsmall hδ haccuracy (BoxProgressionPartition.normalizedPoint u)
      (fun i => ((u i).val : ZMod slice.path.referenceModulus)) β
      (fun i => realIntegerMatrix M
        (fun j => MvPolynomial.aeval (fun x => ((u x).val : ℝ)) (Pscalar j)) i -
          (β i : ℝ))).2
    have hs := mul_le_mul_of_nonneg_left h hκ
    simpa only [full, scaledRetainedRecoveredG, map_natCast, mul_left_comm κ (1 + δ)] using hs
  · apply hscoreFin.trans_eq
    apply Finset.expect_congr
    · ext u
      simp
    · intro u _
      simp only [full, hcoords, Int.cast_natCast]
      unfold BoxProgressionPartition.normalizedPoint
      rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI

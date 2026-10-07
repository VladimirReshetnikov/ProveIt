/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
import OAI.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
import OAI.Combinatorics.Progressions.Geometry.SupportedTriangularSum

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def patchKernelGridRadius (N : ℕ) : ℝ≥0 := 1 / (2 * N)

theorem patchKernelGridRadius_pos {N : ℕ} (hN : 0 < N) : 0 < patchKernelGridRadius N := by
  have : (0 : ℝ≥0) < N := by exact_mod_cast hN
  unfold patchKernelGridRadius
  positivity

theorem patchKernelGridRadius_small {N : ℕ} (hN : 8 ≤ N) :
    2 * (patchKernelGridRadius N : ℝ) ≤ 1 / 8 := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  field_simp
  linarith

noncomputable def gridPatchKernel (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PatchKernel d where
  value x := regularizedTentPartition (uniformBoxGrid (1 / 4) N)
    (patchKernelGridRadius N) i (x + uniformBoxGrid (1 / 4) N i)
  nonneg x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).1
  le_one x := (regularizedTentPartition_range _ (patchKernelGridRadius_pos (N := N) (by omega)) _ _).2
  support x hx j := by
    have hnear : dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) <
        2 * (patchKernelGridRadius N : ℝ) := by
      by_contra! hfar
      exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
    have hj := dist_le_pi_dist (x + uniformBoxGrid (1 / 4) N i) (uniformBoxGrid (1 / 4) N i) j
    simp only [Real.dist_eq, Pi.add_apply, add_sub_cancel_right] at hj
    exact (hj.trans hnear.le).trans ((patchKernelGridRadius_small hN).trans (by norm_num))
  lip := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  lipschitz := by
    have h := (regularizedTentPartition_lipschitz (uniformBoxGrid (ι := Fin d) (1 / 4) N)
      (patchKernelGridRadius_pos (N := N) (by omega)) i).comp
      (isometry_add_right (uniformBoxGrid (1 / 4) N i)).lipschitzWith
    simpa only [Fintype.card_fun, Fintype.card_fin, mul_one, Function.comp_def] using h

theorem gridPatchKernel_translate (d N : ℕ) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ) :
    (gridPatchKernel d N hN i).value (x - uniformBoxGrid (1 / 4) N i) =
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x := by
  simp only [gridPatchKernel, sub_add_cancel]

theorem gridPatchKernel_original_support {d N : ℕ} (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : Fin d → ℝ)
    (hx : regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x ≠ 0)
    (j : Fin d) : |x j| ≤ 3 / 8 := by
  have hnear : dist x (uniformBoxGrid (1 / 4) N i) < 2 * (patchKernelGridRadius N : ℝ) := by
    by_contra! hfar
    exact hx (regularizedTentPartition_zero _ _ _ _ hfar)
  have hcoord := dist_le_pi_dist x (uniformBoxGrid (1 / 4) N i) j
  rw [Real.dist_eq] at hcoord
  have hcenter := uniformBoxGrid_mem (by norm_num : (0 : ℝ) ≤ 1 / 4) (by omega : 0 < N) i j
  have htriangle : |x j| ≤ |x j - uniformBoxGrid (1 / 4) N i j| +
      |uniformBoxGrid (1 / 4) N i j| := by
    simpa only [sub_add_cancel] using
      abs_add_le (x j - uniformBoxGrid (1 / 4) N i j) (uniformBoxGrid (1 / 4) N i j)
  linarith [patchKernelGridRadius_small hN]

theorem PatchKernel.grid_approx {d N : ℕ} (Φ : PatchKernel d) (hN : 8 ≤ N) (x : Fin d → ℝ) :
    |Φ.value x - ∑ i : Fin d → Fin (N + 1),
      Φ.value (uniformBoxGrid (1 / 4) N i) *
        regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i x| ≤
      2 * Φ.lip * (patchKernelGridRadius N : ℝ) := by
  have hcover (y : Fin d → ℝ) (hy : Φ.value y ≠ 0) :=
    exists_uniformBoxGrid_approx (by norm_num : (0 : ℝ) < 1 / 4) (by omega : 0 < N) y (Φ.support y hy)
  have hr : (patchKernelGridRadius N : ℝ) = 2 * (1 / 4 : ℝ) / N := by
    simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
    ring
  have h := regularizedTentPartition_approx (uniformBoxGrid (1 / 4) N)
    (show 0 < (patchKernelGridRadius N : ℝ) from patchKernelGridRadius_pos (N := N) (by omega))
    Φ.value Φ.lipschitz (fun y hy => by rw [hr]; exact hcover y hy) x
  simpa only [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_combination_term {I : Type*} [Fintype I] [Nonempty I]
    (c a : I → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (hsum : δ ≤ ∑ i, c i * a i) :
    ∃ i, δ / Fintype.card I ≤ a i := by
  have hn : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hmean : δ / Fintype.card I ≤ 𝔼 i, c i * a i := by
    rw [Fintype.expect_eq_sum_div_card]
    exact div_le_div_of_nonneg_right hsum hn.le
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  have ha : 0 ≤ a i := by
    by_contra! hneg
    have hmul := mul_nonpos_of_nonneg_of_nonpos (hc i).1 hneg.le
    linarith [div_pos hδ hn]
  exact ⟨i, hi.trans (mul_le_of_le_one_left ha (hc i).2)⟩

namespace PolynomialPatch

variable {X : Type*} {s d N : ℕ}

noncomputable def gridKernelReplacement (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) : PolynomialPatch X s d :=
  A.shiftedKernel (uniformBoxGrid (1 / 4) N i) (gridPatchKernel d N hN i)

theorem gridKernelReplacement_value (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (i : Fin d → Fin (N + 1)) (x : X → ℝ) :
    (A.gridKernelReplacement hN i).value x = ∑' z,
      regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N) i
        ((A.form.slots x).residual z) := by
  simp only [gridKernelReplacement, shiftedKernel_value, gridPatchKernel_translate]

theorem gridKernelReplacement_approx (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    (x : X → ℝ) :
    |A.value x - ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) * (A.gridKernelReplacement hN i).value x| ≤
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
  have h := (A.form.slots x).tsum_approx_finite_family A.kernel.value
    (regularizedTentPartition (uniformBoxGrid (1 / 4) N) (patchKernelGridRadius N))
    (fun i => A.kernel.value (uniformBoxGrid (1 / 4) N i))
    (R := 3 / 8) (by norm_num) (by positivity)
    (fun y hy j => (A.kernel.support y hy j).trans (by norm_num))
    (fun i y hy j => gridPatchKernel_original_support hN i y hy j)
    (A.kernel.grid_approx hN)
  simp_rw [gridKernelReplacement_value]
  exact h

theorem gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1) :
    p.mean (fun x => score x * A.value (point x)) - 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤
      ∑ i : Fin d → Fin (N + 1), A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  let c := fun i : Fin d → Fin (N + 1) => A.kernel.value (uniformBoxGrid (1 / 4) N i)
  let g := fun x => ∑ i : Fin d → Fin (N + 1), c i * (A.gridKernelReplacement hN i).value (point x)
  have hpoint (x) : score x * A.value (point x) ≤ score x * g x +
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
    have hbound : |score x * (A.value (point x) - g x)| ≤
        2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore x) (abs_nonneg _)).trans
        (by simpa only [one_mul, g, c] using A.gridKernelReplacement_approx hN (point x))
    linarith [le_abs_self (score x * (A.value (point x) - g x))]
  have hmean := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const] at hmean
  have hidentity : p.mean (fun x => score x * g x) =
      ∑ i, c i * p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    rw [p.mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← p.mean_const_mul]
    congr 1
    funext x
    ring
  rw [hidentity] at hmean
  exact (sub_le_iff_le_add).mpr hmean

theorem exists_gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpositive : δ ≤ p.mean (fun x => score x * A.value (point x)))
    (hmesh : 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤ δ / 2) :
    ∃ i : Fin d → Fin (N + 1), δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  have h := A.gridKernelReplacement_score hN p point score hscore
  have hs : δ / 2 ≤ ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by linarith
  obtain ⟨i, hi⟩ := exists_positive_combination_term _ _
    (fun i => ⟨A.kernel.nonneg _, A.kernel.le_one _⟩) (by positivity : 0 < δ / 2) hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_div] using hi

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_patch_kernel_mesh (d : ℕ) {L p : ℝ} (hp : 0 ≤ p) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 8 ≤ N ∧ ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) ∧
      2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 ∧
      (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 1) * (2 * p + 11)) ∧
      (((2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N : ℝ≥0) : ℝ) ≤
        Real.exp (2 * ((p + 1) * (2 * p + 11)) + 2) := by
  let b := 2 * p + 8
  let N := ⌈Real.exp b⌉₊
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hNlo : Real.exp b ≤ (N : ℝ) := Nat.le_ceil _
  have h8 : (8 : ℝ) ≤ N := by
    have hexp : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    exact (hexp.trans (Real.exp_le_exp.mpr (by dsimp only [b]; linarith))).trans hNlo
  have hN : 8 ≤ N := by exact_mod_cast h8
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (b + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg b)).le
    have h1 := Real.one_le_exp hb
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg b)
    dsimp only [N] at *
    linarith
  have hbound : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 10) := by
    convert hNhi using 1; dsimp only [b]; congr 1; ring
  have herr : L / N ≤ Real.exp (-p - 8) := by
    calc
      L / N ≤ L / Real.exp b := div_le_div_of_nonneg_left hL (Real.exp_pos b) hNlo
      _ ≤ Real.exp p / Real.exp b := div_le_div_of_nonneg_right hLp (Real.exp_nonneg b)
      _ = Real.exp (-p - 8) := by
        rw [← Real.exp_sub]
        congr 1
        dsimp only [b]
        ring
  have h8exp : (2 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h8exp
  have haccuracy : 2 * L * (patchKernelGridRadius N : ℝ) ≤ Real.exp (-p) / 2 := by
    have heq : 2 * L * (patchKernelGridRadius N : ℝ) = L / N := by
      simp only [patchKernelGridRadius, NNReal.coe_div, NNReal.coe_mul,
        NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_natCast]
      ring
    rw [heq]
    apply herr.trans
    rw [sub_eq_add_neg, Real.exp_add]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  let q := (p + 1) * (2 * p + 11)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hq2 : 2 * p + 11 ≤ q := by dsimp only [q]; nlinarith
  have hcount : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (by positivity) hbound d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ 2 * p + 10)
    dsimp only [q]
    nlinarith
  have hradius : 1 / (patchKernelGridRadius N : ℝ) ≤ Real.exp q := by
    have heq : 1 / (patchKernelGridRadius N : ℝ) = 2 * (N : ℝ) := by
      simp [patchKernelGridRadius]
    rw [heq]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ 2 * ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ Real.exp 1 * Real.exp (2 * p + 10) := mul_le_mul h2 hbound (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 11) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq2
  exact ⟨N, hN, hbound, haccuracy, hcount,
    metricPartition_constant_le_exp ((N + 1) ^ d) (patchKernelGridRadius N) hq hcount hradius⟩

end Erdos3

end

end OAI

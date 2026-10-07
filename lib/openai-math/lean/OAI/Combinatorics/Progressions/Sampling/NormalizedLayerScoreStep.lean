import OAI.Combinatorics.Progressions.Estimates.PreparedLayerFreezing

namespace OAI

section

namespace Erdos3.FiniteProgressionPartition

open scoped BigOperators

theorem exists_large_score_cell {N H : ℕ} (P : FiniteProgressionPartition N)
    (hN : 0 < N) (hH : 0 < H) (f B : ℕ → ℝ) (V : P.Label → ℕ → ℝ)
    {b σ ε C : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ) (hC : 0 < C)
    (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    (hB : ∀ n < N, B n ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : 4 * ε ≤ σ) (hcount : (Fintype.card P.Label : ℝ) * H ≤ C * N)
    (hclose : ∀ i n, n < P.length i → dist (B (P.start i + P.step i * n)) (V i n) ≤ ε)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * B n.val) :
    ∃ i, σ * H / (8 * C) ≤ P.length i ∧
      σ / 2 < 𝔼 n : Fin (P.length i), (f (P.start i + P.step i * n.val) - b) * V i n.val := by
  let : NeZero N := ⟨hN.ne'⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcost : (Fintype.card P.Label : ℝ) * (σ * H / (8 * C)) / N ≤ σ / 8 := by
    apply (div_le_iff₀ hNR).mpr
    rw [show (Fintype.card P.Label : ℝ) * (σ * H / (8 * C)) =
      ((Fintype.card P.Label : ℝ) * H * σ) / (8 * C) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 8 * C)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcount hσ.le]
  have hg (n : Fin N) : (f n.val - b) * B n.val ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (show f n.val - b ≤ 1 by linarith [(hf n.val n.isLt).2, hb.1])
      (hB n.val n.isLt).1
    nlinarith [(hB n.val n.isLt).2]
  obtain ⟨i, hlarge, hcell⟩ := exists_large_cell_score P.cell
    (fun n => (f n.val - b) * B n.val) (L := σ * H / (8 * C)) (τ := 3 * σ / 4)
    (by positivity) (by positivity) hg hscore (by simp only [Fintype.card_fin]; linarith)
  rw [P.card_cell] at hlarge
  have hlen : 0 < P.length i := by
    have hpos : (0 : ℝ) < σ * H / (8 * C) := by positivity
    have hlenR : (0 : ℝ) < P.length i := hpos.trans_le hlarge
    exact_mod_cast hlenR
  let : NeZero (P.length i) := ⟨hlen.ne'⟩
  have hcell' : 3 * σ / 4 < 𝔼 n : Fin (P.length i),
      (f (P.start i + P.step i * n.val) - b) * B (P.start i + P.step i * n.val) := by
    rw [P.expect_cell i (fun n => (f n - b) * B n)] at hcell
    exact hcell
  have hpoint (n : Fin (P.length i)) := weighted_score_le_of_close
    (hf _ (P.point_lt i n.isLt)) hb (hclose i n.val n.isLt)
  have hmean : (𝔼 n : Fin (P.length i),
      (f (P.start i + P.step i * n.val) - b) * B (P.start i + P.step i * n.val)) ≤
      (𝔼 n : Fin (P.length i), (f (P.start i + P.step i * n.val) - b) * V i n.val) + ε := by
    calc
      _ ≤ 𝔼 n : Fin (P.length i), ((f (P.start i + P.step i * n.val) - b) * V i n.val + ε) :=
        Finset.expect_le_expect fun n _ => hpoint n
      _ = _ := by rw [Finset.expect_add_distrib]; simp
  exact ⟨i, hlarge, by linarith⟩

end Erdos3.FiniteProgressionPartition

end

section

namespace Erdos3

open scoped BigOperators

theorem PolynomialCoordinatePartitionBound.layer_score_step {h p : ℕ} {K : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{0} h K p)
    {s D E N H : ℕ} (A : PolynomialPatch Unit s (D + E)) (L : A.LowestLayerModel h)
    (hH : 0 < H) (hscale : K * ((D : ℝ) + 1) ≤ H)
    (hsize : H ^ (p * (D + 1) ^ (2 * h)) ≤ N)
    (hsmall : (2 : ℝ) ^ (h + 1) * ((h : ℝ) / H) < 1)
    (hfreeze : (D : ℝ) * (2 * ((h : ℝ) / H)) < 1 / 12)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b σ : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) (hσ : 0 < σ)
    (hroom : 8 * (A.kernel.lip : ℝ) * D * h ≤ σ * H)
    (hscore : σ ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) :
    ∃ (q a len : ℕ) (F : PolynomialPatch Unit s E), 0 < q ∧
      σ * H / (2 : ℝ) ^ (h + 3) ≤ len ∧ (∀ n < len, a + q * n < N) ∧
      F.kernel.lip = A.kernel.lip ∧ (∀ j, F.weight j = A.weight (j.natAdd D)) ∧
      σ / 2 < 𝔼 n : Fin len, (f (a + q * n.val) - b) * F.value (fun _ => (n.val : ℝ)) := by
  obtain ⟨Q, F, hcount, hproperties⟩ := hpartition.freeze_layer A L hH hscale hsize hsmall hfreeze
  have hN : 0 < N := (pow_pos hH _).trans_le hsize
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hcountR : (Fintype.card Q.Label : ℝ) * H ≤ (2 : ℝ) ^ h * N := by exact_mod_cast hcount
  have hroom' : 4 * ((A.kernel.lip : ℝ) * ((D : ℝ) * (2 * ((h : ℝ) / H)))) ≤ σ := by
    rw [show 4 * ((A.kernel.lip : ℝ) * ((D : ℝ) * (2 * ((h : ℝ) / H)))) =
      (8 * (A.kernel.lip : ℝ) * D * h) / H by ring]
    exact (div_le_iff₀ hHR).mpr hroom
  obtain ⟨i, hlarge, hretained⟩ := Q.exists_large_score_cell hN hH f
    (fun n => A.value (fun _ => (n : ℝ))) (fun i n => (F i).value (fun _ => (n : ℝ)))
    hb hσ (by positivity : 0 < (2 : ℝ) ^ h) hf (fun n _ => A.value_mem_Icc _)
    hroom' hcountR (fun i => (hproperties i).2.2) hscore
  refine ⟨Q.step i, Q.start i, Q.length i, F i, Q.step_pos i, ?_,
    (fun n hn => Q.point_lt i hn), (hproperties i).1, (hproperties i).2.1, hretained⟩
  have heq : (2 : ℝ) ^ (h + 3) = 8 * (2 : ℝ) ^ h := by rw [pow_add]; ring
  simpa only [heq] using hlarge

end Erdos3

end

end OAI

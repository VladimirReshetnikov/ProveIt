import OAI.Combinatorics.Progressions.Lattices.NormalizedResidueBlockCells
import OAI.Combinatorics.Progressions.Lattices.ResidueBlockLongSideBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal
open BoxProgressionPartition

theorem exists_long_frozen_box {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i)
    (score W : (∀ i, Fin (N i)) → ℝ) (V : (∀ i, (P i).Label) → (∀ i, Fin (N i)) → ℝ)
    {C τ ε S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hW : ∀ x, score x * W x ≤ C)
    (hclose : ∀ x, dist (W x) (V (cell P x) x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x)
    (hbudget : τ + ε + C * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S) :
    ∃ a : ∀ i, (P i).Label, (∀ i, L i ≤ ((P i).length (a i) : ℝ)) ∧
      τ < 𝔼 j : (∀ i, Fin ((P i).length (a i))), score (point P a j) * V a (point P a j) := by
  classical
  let : ∀ i, Nonempty (Fin (N i)) := fun i => ⟨⟨0, hN i⟩⟩
  obtain ⟨a, ha, hs⟩ := exists_good_frozen_partition_score (cell P)
    (fun a => ∀ i, L i ≤ ((P i).length (a i) : ℝ)) score W V hC hτ hε hscoreBound hW
    (short_box_side_mass_le P hN L hL) hclose hscore hbudget
  exact ⟨a, ha, by simpa only [expect_cell] using hs⟩

theorem exists_long_spatially_frozen_box {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i)) (hN : ∀ i, 0 < N i)
    (L : ι → ℝ) (hL : ∀ i, 0 ≤ L i)
    (score : (∀ i, Fin (N i)) → ℝ) (F : (ι → ℝ) → (∀ i, Fin (N i)) → ℝ)
    (Λ : ℝ≥0) (hF : ∀ x, LipschitzWith Λ (fun z => F z x))
    {C τ ρ S : ℝ} (hC : 0 ≤ C) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hscoreBound : ∀ x, |score x| ≤ 1)
    (hcap : ∀ x, F (normalizedPoint x) x ∈ Set.Icc (0 : ℝ) C)
    (hwidth : ∀ a : ∀ i, (P i).Label, ∀ i,
      ((P i).step (a i) : ℝ) * (P i).length (a i) ≤ ρ * N i)
    (hscore : S ≤ 𝔼 x, score x * F (normalizedPoint x) x)
    (hbudget : τ + Λ * ρ + C * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S) :
    ∃ a : ∀ i, (P i).Label, (∀ i, L i ≤ ((P i).length (a i) : ℝ)) ∧
      τ < 𝔼 j : (∀ i, Fin ((P i).length (a i))),
        score (point P a j) * F (normalizedStart P a) (point P a j) := by
  apply exists_long_frozen_box P hN L hL score (fun x => F (normalizedPoint x) x)
    (fun a x => F (normalizedStart P a) x) hC hτ (mul_nonneg Λ.coe_nonneg hρ) hscoreBound
    _ _ hscore hbudget
  · intro x
    have hs : score x ≤ 1 := (le_abs_self _).trans (hscoreBound x)
    exact (mul_le_mul_of_nonneg_right hs (hcap x).1).trans (by simpa using (hcap x).2)
  · intro x
    have hid : point P (cell P x) (fun i => (P i).offset (x i)) = x := by
      funext i
      exact (P i).point_cell_offset (x i)
    have hd := normalizedPoint_dist_start P hN hρ (cell P x) (hwidth (cell P x))
      (fun i => (P i).offset (x i))
    rw [hid] at hd
    exact ((hF x).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd Λ.coe_nonneg)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open BoxProgressionPartition

theorem exists_long_residue_cell_frozen_score
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) (q Q : ℕ) (hq : 0 < q) (hQ : 0 < Q)
    (origin : ι → ℝ) (step : ℝ) (hstep : 0 ≤ step)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (hparent : ∀ i n, n < N i → |origin i + step * n| ≤ T i)
    (hparentwidth : ∀ i, step * N i ≤ 2 * T i)
    (hlarge : ∀ i, 2 * (q : ℝ) ≤ (1 / (Q : ℝ)) * N i)
    (score W : (∀ i, Fin (N i)) → ℝ)
    (V : (ι → ZMod q) → (ι → Fin (Q + 1)) → (∀ i, Fin (N i)) → ℝ)
    {B τ ε θ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    (hscoreBound : ∀ x, |score x| ≤ 1) (hcap : ∀ x, score x * W x ≤ B)
    (hclose : ∀ r z x, (∀ i, ((x i).val : ZMod q) = r i) →
      (∀ i, |origin i + step * (x i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) →
      dist (W x) (V r z x) ≤ ε)
    (hscore : S ≤ 𝔼 x, score x * W x) (hbudget : τ + ε + B * θ < S) :
    ∃ A : ResidueBoxSlice N q, (∀ i, 0 < A.length i) ∧
      (∀ i, θ * N i / (4 * q * Q * (Fintype.card ι + 1 : ℝ)) ≤ A.length i) ∧
      ∃ r : ι → ZMod q, ∃ z : ι → Fin (Q + 1),
        (∀ j : ∀ i, Fin (A.length i), ∀ i, ((A.point j i).val : ZMod q) = r i) ∧
        (∀ j : ∀ i, Fin (A.length i), ∀ i,
          |origin i + step * (A.point j i).val - normalizedRealBoxGrid T Q z i| ≤ T i * (2 / Q)) ∧
        τ < 𝔼 j : (∀ i, Fin (A.length i)), score (A.point j) * V r z (A.point j) := by
  classical
  obtain ⟨H, hH, hfit, hwidth, hHlower, hcells⟩ :=
    exists_normalized_residue_block_cells N q Q hq hQ origin step hstep T hT hparent
      hparentwidth hlarge
  let P := fun i => FiniteProgressionPartition.blocks (N i) q (H i) hq (hH i)
  choose z hz using hcells
  let r := fun a : ∀ i, (P i).Label => fun i => ((P i).start (a i) : ZMod q)
  let Vcell := fun a : ∀ i, (P i).Label => V (r a) (z a)
  let L := fun i => θ * H i / (2 * (Fintype.card ι + 1 : ℝ))
  have hL (i) : 0 < L i :=
    (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i) (Fintype.card ι)).2
  have hres (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i) :
      ((point P a j i).val : ZMod q) = r a i := by
    rw [point_val]
    change (((P i).start (a i) + q * (j i).val : ℕ) : ZMod q) = _
    simp [r]
  have hcellclose (x : ∀ i, Fin (N i)) : dist (W x) (Vcell (cell P x) x) ≤ ε := by
    let a := cell P x
    let j := fun i => (P i).offset (x i)
    have hid : point P a j = x := by
      funext i
      exact (P i).point_cell_offset (x i)
    apply hclose (r a) (z a) x
    · intro i
      rw [← hid]
      exact hres a j i
    · have hp : (ResidueBoxSlice.ofBlocks H hq hH a).point j = x :=
        (ResidueBoxSlice.ofBlocks_point H hq hH a j).trans hid
      simpa only [hp] using hz a j
  have hshort : (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) ≤ θ :=
    boxBlock_short_side_budget N H q hN hH hfit hθ.le
  have hbudget' : τ + ε + B * (∑ i, (Fintype.card (P i).Label : ℝ) * L i / N i) < S :=
    by linarith [mul_le_mul_of_nonneg_left hshort hB]
  obtain ⟨a, ha, hs⟩ := exists_long_frozen_box P hN L (fun i => (hL i).le)
    score W Vcell hB hτ hε hscoreBound hcap hcellclose hscore hbudget'
  let A := ResidueBoxSlice.ofBlocks H hq hH a
  have hlength (i) : 0 < A.length i := by
    have hpos : (0 : ℝ) < (P i).length (a i) := (hL i).trans_le (ha i)
    exact_mod_cast hpos
  refine ⟨A, hlength, ?_, r a, z a, ?_, hz a, ?_⟩
  · intro i
    exact (residueBlock_long_side_budget hθ (hN i) hq hQ (hHlower i)
      (Fintype.card ι)).1.trans (ha i)
  · intro j i
    rw [ResidueBoxSlice.ofBlocks_point]
    exact hres a j i
  · simpa only [A, ResidueBoxSlice.ofBlocks_point] using hs

end Erdos3

end

end OAI

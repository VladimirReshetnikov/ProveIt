import OAI.Combinatorics.Progressions.Estimates.PhysicalResidualCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedGridLength_bounds (N : ℕ) (H ρ : ℝ)
    (hlarge : 4 ≤ ρ * H) (hwhole : ρ * H ≤ 2 * (N : ℝ)) :
    0 < ⌊ρ * H / 2⌋₊ ∧ ⌊ρ * H / 2⌋₊ ≤ N ∧
      ρ * H / 4 ≤ (⌊ρ * H / 2⌋₊ : ℝ) ∧ (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := by
  have hpos : 0 < ⌊ρ * H / 2⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hN : ⌊ρ * H / 2⌋₊ ≤ N := Nat.floor_le_of_le (by linarith)
  have hup : (⌊ρ * H / 2⌋₊ : ℝ) ≤ ρ * H / 2 := Nat.floor_le (by linarith)
  have hnext := Nat.lt_floor_add_one (ρ * H / 2)
  exact ⟨hpos, hN, by linarith, hup⟩

noncomputable def normalizedBoxPartitions {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ)) :
    ∀ i, FiniteProgressionPartition (N i) :=
  comparableBoxPartitions N (fun i => ⌊ρ * H i / 2⌋₊)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).2.1)

theorem normalizedBoxPartitions_step {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    (normalizedBoxPartitions N H ρ hlarge hwhole i).step c = 1 := rfl

theorem normalizedBoxPartitions_positive {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    0 < (normalizedBoxPartitions N H ρ hlarge hwhole i).length c := by
  exact (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1.trans_le
    (comparableBoxPartitions_length N _ _ _ i c).1

theorem normalizedBoxPartitions_lengths {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    ρ * H i / 4 ≤ ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ∧
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ≤ ρ * H i := by
  obtain ⟨_, _, hlo, hup⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
  have hl := comparableBoxPartitions_length N (fun j => ⌊ρ * H j / 2⌋₊)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).1)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).2.1) i c
  have hl' : (⌊ρ * H i / 2⌋₊ : ℝ) ≤
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) := by exact_mod_cast hl.1
  have hu' : ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) <
      2 * (⌊ρ * H i / 2⌋₊ : ℝ) := by exact_mod_cast hl.2
  exact ⟨hlo.trans hl', by linarith⟩

theorem normalizedBoxPartitions_card {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ)) :
    Fintype.card (∀ i, (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) =
      ∏ i, N i / ⌊ρ * H i / 2⌋₊ := comparableBoxPartitions_card N _ _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_physical_residual_correlation {J I ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|) (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hmoduli : ∀ j, (q j : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (S : Finset ι) (hS : S.card ≤ degree) (hm : affinePairModulus t u ∣ ∏ j ∈ S, q j) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos q degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos q degree g (smoothAffineSample u z.val))| ≤
      ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
        ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap ι degree eta) ^ 2 +
          (fullSmoothPairError (Fintype.card I) k Q C κ δ +
            (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
              (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap ι degree eta ^ 2)) := by
  let P : ∀ i, FiniteProgressionPartition (N i) := normalizedBoxPartitions N H ρ hlarge hwhole
  let hpos : ∀ i c, 0 < (P i).length c := normalizedBoxPartitions_positive N H ρ hlarge hwhole
  have hstep : ∀ i c, (P i).step c = 1 := normalizedBoxPartitions_step N H ρ hlarge hwhole
  have hN (i : I) : 0 < N i := by
    have hr : (0 : ℝ) < N i := by linarith [hlarge i, hwhole i]
    exact_mod_cast hr
  let : Nonempty (translatedIntegerBox lo N) := ⟨⟨lo, (mem_translatedIntegerBox lo N lo).mpr
    (fun i => ⟨le_rfl, lt_add_of_pos_right _ (by exact_mod_cast hN i)⟩)⟩⟩
  have hwidth (i : I) : (affinePairModulus t u : ℝ) ≤ (N i : ℝ) :=
    (by exact_mod_cast hQ : (affinePairModulus t u : ℝ) ≤ Q).trans (hside i)
  have hlength' (i : I) (c : (P i).Label) :
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ((P i).length c : ℝ) :=
    (hlength i).trans (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).1
  have hcf (c : ∀ i, (P i).Label) :
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree f eta :=
    physicalBoxResidual_control_of_lengths lo N P hstep hpos q hpair degree f hf
      modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim hlength' c
  have hcg (c : ∀ i, (P i).Label) :
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree g eta :=
    physicalBoxResidual_control_of_lengths lo N P hstep hpos q hpair degree g hg
      modLog dimLog accLog eta hmodLog heta hacc hmoduli hdim hlength' c
  exact physical_box_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ hmesh hsmall
    origin hZ lo N hwidth P hstep hpos q hpair degree f g eta ρ ((Real.exp_pos _).le.trans hacc) hρ
    (fun i c => (normalizedBoxPartitions_lengths N H ρ hlarge hwhole i c).2) hcf hcg S hS hm

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Geometry.BoxPairCorrelation
import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxControl
import OAI.Combinatorics.Progressions.Linear.PhysicalBoxKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem physical_box_residual_correlation {J I ι : Type*}
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
    (lo : I → ℤ) (N : I → ℕ) [Nonempty (translatedIntegerBox lo N)]
    (hside : ∀ i, (affinePairModulus t u : ℝ) ≤ (N i : ℝ))
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (degree : ℕ) (f g : (I → ℤ) → ℝ) (eta ρ : ℝ) (heta : 0 ≤ eta) (hρ : 0 ≤ ρ)
    (hgrid : ∀ i c, ((P i).length c : ℝ) ≤ ρ * H i)
    (hcf : ∀ c : (∀ i, (P i).Label),
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree f eta)
    (hcg : ∀ c : (∀ i, (P i).Label),
      ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q degree g eta)
    (S : Finset ι) (hS : S.card ≤ degree) (hm : affinePairModulus t u ∣ ∏ j ∈ S, q j) :
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
  let : NeZero (affinePairModulus t u) := ⟨(affinePairModulus_pos t u k hne).ne'⟩
  let e : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos q degree f
  let d : (I → ℤ) → ℝ := physicalBoxResidual lo N P hpos q degree g
  let cell : (∀ i, (P i).Label) → (∀ i, (P i).Label) → (I → ZMod (affinePairModulus t u)) → ℝ :=
    fun c c' _ => shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) origin
      (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => intervalCellLower (lo i) (P i) (c' i))
  have hlen (i : I) : lo i < lo i + (N i : ℤ) := by
    have hmpos : (0 : ℝ) < affinePairModulus t u := by exact_mod_cast affinePairModulus_pos t u k hne
    have hN : 0 < N i := by exact_mod_cast hmpos.trans_le (hside i)
    exact lt_add_of_pos_right _ (by exact_mod_cast hN)
  have hw (i : I) : (affinePairModulus t u : ℝ) ≤ ((lo i + N i - lo i : ℤ) : ℝ) := by
    simpa only [add_sub_cancel_left, Int.cast_natCast] using hside i
  have hbound := box_smooth_pair_correlation
    (alpha := eta * residueTruncationCap ι degree eta) (beta := eta * residueTruncationCap ι degree eta)
    t u k hne H Q hH hL hC hκ hδ hδ1
    ht hu hgap hQ hmesh hsmall origin hZ lo (fun i => lo i + N i) lo (fun i => lo i + N i)
    hlen hlen hw hw (translatedIntegerBox lo N) (translatedIntegerBox lo N)
    (translatedIntegerBox_eq_piFinset lo N) (translatedIntegerBox_eq_piFinset lo N)
    e d (physicalBoxResidual_zero_off lo N P hpos q degree f)
    (physicalBoxResidual_zero_off lo N P hpos q degree g)
    (physicalBoxCell lo N P) (physicalBoxCell lo N P) cell
    (mul_nonneg heta (residueTruncationCap_nonneg ι degree heta))
    (smoothPairKernelCap (Fintype.card I) k C κ).coe_nonneg
    (mul_nonneg (smoothPairKernelLip (Fintype.card I) k C κ).coe_nonneg hρ)
    (fun c r => by
      simpa only [mul_div_assoc] using
        physicalBoxResidual_cell_residue lo N P hstep hpos q hpair degree f eta c (hcf c) S hS _ hm r)
    (fun c r => by
      simpa only [mul_div_assoc] using
        physicalBoxResidual_cell_residue lo N P hstep hpos q hpair degree g eta c (hcg c) S hS _ hm r)
    (fun c c' _ => shiftedPairLocationKernel_cap t u k hne H L hH (zero_lt_one.trans_le hL)
      hC hκ (ht k) (hu k) hgap origin _ _)
    (fun x y _ => physicalBox_pair_kernel_grid_error t u k hne H L hH (zero_lt_one.trans_le hL)
      hC hκ hρ (ht k) (hu k) hgap origin lo N P hstep hgrid x y)
  have he := physicalBoxResidual_energy lo N P hstep hpos q degree f eta hcf
  have hd := physicalBoxResidual_energy lo N P hstep hpos q degree g eta hcg
  have herr : 0 ≤ fullSmoothPairError (Fintype.card I) k Q C κ δ +
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ :=
    add_nonneg (fullSmoothPairError_nonneg _ k Q C κ δ hδ)
      (mul_nonneg (NNReal.coe_nonneg _) hρ)
  apply hbound.trans
  calc
    _ ≤ ((translatedIntegerBox lo N).card : ℝ) * (translatedIntegerBox lo N).card / (∏ i, H i ^ 2) *
      ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap ι degree eta) *
        (eta * residueTruncationCap ι degree eta) +
       (fullSmoothPairError (Fintype.card I) k Q C κ δ +
          (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
        ((2 : ℝ) ^ Fintype.card I / 2 * ((1 + eta * residueTruncationCap ι degree eta ^ 2) +
          (1 + eta * residueTruncationCap ι degree eta ^ 2)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ herr
      exact mul_le_mul_of_nonneg_left (add_le_add he hd) (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI

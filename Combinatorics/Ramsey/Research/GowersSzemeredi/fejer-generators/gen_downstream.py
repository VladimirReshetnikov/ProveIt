"""Proofs05Downstream: the two phase refinements follow from the two diameter refinements.

Both pairs were the same proof with a different per-cell conclusion. A partition whose cells
have phi-image of diameter at most eta*N/(4π) costs at most eta/2*|P| in the phase
(`section5_phase_error_of_diameter`, from `cor57_cell_norm_le`), so the phase forms are
corollaries. The diameter theorems move in front of their phase twins; statements unchanged.
"""
from foldlib import Fold

M = 'Proofs05Downstream'
F = Fold()
s = F.get(M)
# the diameter refinement and the new lemma go before the local phase refinement's comment block
local_d = F.take(M, 'section5_local_diameter_refinement_of_corollary_5_6')
eff_d = F.take(M, 'section5_efficient_diameter_refinement_of_corollary_5_6')
LEMMA = '''/-- A partition of `P` into cells whose `phi`-images have diameter at most
`η·N/(4π)` changes a disc-valued sum by at most `η/2·|P|` under the phase
`exponential (-phi)`. -/
private lemma section5_phase_error_of_diameter {N L : Nat} [NeZero N]
    (P : Finset (ZMod N)) (R : Fin L → Finset (ZMod N)) (phi : ZMod N → ZMod N) (eta : Real)
    (hrefine : IsPartition R P)
    (hdiam : ∀ j, diameterAtMostReal ((R j).image phi) (eta * N / (4 * Real.pi)))
    (f : ZMod N → Complex) (hf : DiscValued f) :
    ‖∑ s ∈ P, f s * exponential (-(phi s))‖ ≤
      (∑ j, ‖∑ s ∈ R j, f s‖) + eta / 2 * P.card := by
  have hcell (j : Fin L) : ‖∑ s ∈ R j, f s * exponential (-(phi s))‖ ≤
      ‖∑ s ∈ R j, f s‖ + eta / 2 * (R j).card := by
    have hinj := (ZMod.val_injective N).injOn (s := ((R j : Finset (ZMod N)) : Set (ZMod N)))
    have key := cor57_cell_norm_le ((R j).image ZMod.val) f phi eta (eta * N / (4 * Real.pi)) hf
      (by simpa only [Finset.image_image, Function.comp_def, ZMod.natCast_zmod_val] using hdiam j)
      le_rfl
    simpa only [Finset.sum_image hinj, Finset.card_image_of_injective _ (ZMod.val_injective N),
      ZMod.natCast_zmod_val] using key
  calc
    ‖∑ s ∈ P, f s * exponential (-(phi s))‖ =
        ‖∑ j, ∑ s ∈ R j, f s * exponential (-(phi s))‖ := by
      rw [downstream_sum_partition R P hrefine]
    _ ≤ ∑ j, ‖∑ s ∈ R j, f s * exponential (-(phi s))‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖∑ s ∈ R j, f s‖ + eta / 2 * (R j).card) :=
      Finset.sum_le_sum fun j _ => hcell j
    _ = (∑ j, ‖∑ s ∈ R j, f s‖) + eta / 2 * P.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, IsPartition.sum_card hrefine]
'''
anchor = '/-!\nThe strengthened local form used in the proof of Lemma 5.14.'
s = F.get(M)
i = s.index(anchor)
F.text[M] = s[:i] + local_d + '\n' + LEMMA + '\n' + s[i:]
F.insert(M, eff_d, 'section5_efficient_local_phase_refinement_of_corollary_5_6')
F.reprove(M, 'section5_local_phase_refinement_of_corollary_5_6', ''' by
  obtain ⟨L, R, hrefine, hRproper, hdiam⟩ :=
    section5_local_diameter_refinement_of_corollary_5_6 h56 P phi eta hP hk hphi heta hlarge hv
      hvupper
  exact ⟨L, R, hrefine, hRproper,
    section5_phase_error_of_diameter P.carrier _ phi eta hrefine hdiam⟩''')
F.reprove(M, 'section5_efficient_local_phase_refinement_of_corollary_5_6', ''' by
  obtain ⟨L, R, hrefine, hproper, hcount, hdiam⟩ :=
    section5_efficient_diameter_refinement_of_corollary_5_6 h56 P phi eta hP hk hphi heta
  exact ⟨L, R, hrefine, hproper, hcount,
    section5_phase_error_of_diameter P.carrier _ phi eta hrefine hdiam⟩''')
F.commit()

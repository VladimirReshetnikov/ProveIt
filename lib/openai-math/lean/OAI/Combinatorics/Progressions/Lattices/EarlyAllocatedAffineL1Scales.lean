import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_l1_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target Pk F Tmod D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hPk : 0 ≤ Pk) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {p : ℝ}, 0 ≤ p → (∀ j, (R j)⁻¹ ≤ Real.exp p) →
        let P := p + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) := by
  intro maskLog E η Prho Ptail K
  have hD := hdim.nonneg
  have hm : 0 ≤ maskLog := by dsimp [maskLog]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcoeff : 0 ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold affineProfileCoefficientEnvelope; positivity
  have hinput : 0 ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F :=
    jointAffineSourceEnvelope_nonneg hD hcoeff (by positivity) hF
  have hr : 0 ≤ Prho := by dsimp [Prho]; positivity
  have htail : 0 ≤ Ptail := by
    dsimp [Ptail, affineProfileToleranceEnvelope]
    positivity
  obtain ⟨ρ, hρ, _, t, ht, htone, htlog, _, hs⟩ :=
    exists_early_allocated_affine_bounded_source.{uJ,uQ} B rows hrows hcard ψ hψ hrange hzero hone
      A T hLip hTransition block hblock hdim hδ hδone htarget hm hF hδF
  refine ⟨hr, htail, ρ, ?_, t, ht, htone, htlog, hs, ?_⟩
  · intro partition
    refine ⟨(hρ partition).1, (hρ partition).2.1, ?_⟩
    have hlow := (hρ partition).2.2
    rw [Real.exp_neg] at hlow
    exact (inv_le_comm₀ (show 0 < (ρ partition : ℝ) from (hρ partition).1) (Real.exp_pos Prho)).mpr hlow
  · intro J _ U basis R hR p hp hRi P
    have hP : 0 ≤ P := add_nonneg hp htail
    have hRbound (j) : (R j)⁻¹ ≤ Real.exp P :=
      (hRi j).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right htail))
    have htbound : t⁻¹ ≤ Real.exp P :=
      htlog.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hp))
    let S := allocatedAffineScale (G := G) B U basis hR (fun _ => ht) D P Prho Pk target F Tmod
    refine ⟨S, hRbound, fun _ => htbound,
      allocatedAffineScale_lower B U basis hR (fun _ => ht) D P Prho Pk target F Tmod, ?_⟩
    exact (allocatedAffineScale_upper B U basis hR (fun _ => ht) hdim hP hr hPk htarget hF hTmod
      hRbound (fun _ => htbound)).trans (Real.exp_le_exp.mpr
        ((Classical.choose_spec (exists_allocatedAffineScaleLog_bound m)).2
          D P Prho Pk target F Tmod hD hP hr hPk htarget hF hTmod))

end Erdos3.VectorPolynomial

end

end OAI

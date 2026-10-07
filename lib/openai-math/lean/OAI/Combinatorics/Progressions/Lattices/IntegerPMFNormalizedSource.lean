import OAI.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
import OAI.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem pmf_interval_toReal_mass (L : ℕ) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ)) :
    (∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal) = 1 := by
  have hm : (∑ k ∈ Finset.Ico 0 (L : ℤ), p k) = 1 := by
    rw [← p.tsum_coe]
    apply (tsum_eq_sum (s := Finset.Ico 0 (L : ℤ)) _).symm
    intro k hk
    by_contra hn
    exact hk (hs k hn)
  rw [← ENNReal.toReal_sum (fun k _ => p.apply_ne_top k), hm, ENNReal.toReal_one]

theorem scalarCubeResidueWeights_empty_one_mean (L : ℕ) (hL : 0 < L) (f : ℤ → ℝ) :
    (scalarCubeResidueWeights Empty L 1 hL (fun _ => 1) (fun _ => 0)
      (fun _ => by norm_num) (fun _ => le_rfl) (by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL)).mean
      (fun x => f (x none : ℤ)) =
        (∑ k ∈ Finset.Ico 0 (L : ℤ), f k) / (L : ℝ) := by
  rw [scalarCubeResidueWeights_mean]
  calc
    _ = 𝔼 k : coefficientResidueSet L 1 0, f k :=
      Fintype.expect_equiv (emptyScalarCubeResidueEquiv L (fun _ => 1) (fun _ => 0))
        _ _ (fun _ => rfl)
    _ = _ := by
      have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
        ext k
        simp only [coefficientResidueSet, Finset.mem_filter]
        exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
      rw [hr, Fintype.expect_eq_sum_div_card]
      simp [Finset.sum_attach]

noncomputable def normalizedScalarCubeSourceOfIntegerPMF
    (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
    (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
    (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal) :
    NormalizedScalarCubeSource Empty where
  length := L
  modulusBound := 1
  length_pos := hL
  modulus := fun _ => 1
  residue := fun _ => 0
  modulus_pos := fun _ => by norm_num
  modulus_le := fun _ => le_rfl
  size := by change 1 ≤ L; exact Nat.succ_le_iff.mpr hL
  weight := w
  weightBound := B
  weightLipschitz := T
  weightBound_pos := hB
  weight_range := hw
  weight_lipschitz := hLip
  normalized := by
    have he (x : IntegerScalarCubeBox Empty L) :
        w (fun i => (x i : ℝ) / L) = w (fun _ => (x none : ℝ) / L) := by
      congr 1
      funext i
      cases i with
      | none => rfl
      | some e => exact e.elim
    simp only [he]
    refine (scalarCubeResidueWeights_empty_one_mean L hL
      (fun k => w (fun _ => (k : ℝ) / L))).trans ?_
    simp_rw [hgrid]
    rw [← Finset.mul_sum, pmf_interval_toReal_mass L p hs, mul_one]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hL))

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

theorem normalizedScalarCubeSourceOfIntegerPMF_mean (f : ℤ → ℝ) :
    (intervalSource).source.mean (fun x => f (x none : ℤ)) =
      ∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal * f k := by
  apply ((intervalSource).source_coefficient_mean f).trans
  change (FiniteProbabilityWeights.ofDensity _ _ _).mean _ = _
  rw [FiniteProbabilityWeights.ofDensity_mean]
  change (𝔼 k : coefficientResidueSet L 1 0,
    w (fun _ => (k.val : ℝ) / L) * f k.val) = _
  have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
    ext k
    simp only [coefficientResidueSet, Finset.mem_filter]
    exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
  rw [hr, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Int.card_Ico, sub_zero, Int.toNat_natCast]
  simp_rw [hgrid, mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  exact Finset.sum_coe_sort (Finset.Ico 0 (L : ℤ)) (fun k => (p k).toReal * f k)

theorem normalizedScalarCubeSourceOfIntegerPMF_law :
    (intervalSource).source.toPMF.map (fun x => (x none : ℤ)) = p := by
  ext z
  let q := (intervalSource).source.toPMF.map (fun x => (x none : ℤ))
  have hreal : (q z).toReal = (p z).toReal := by
    change (((intervalSource).source.toPMF.map (fun x => (x none : ℤ))) z).toReal = _
    rw [FiniteProbabilityWeights.toPMF_map_toReal]
    refine (normalizedScalarCubeSourceOfIntegerPMF_mean L hL p hs w B T hB hw hLip hgrid
      (fun k => @ite ℝ (k = z) (Classical.propDecidable (k = z)) 1 0)).trans ?_
    by_cases hz : z ∈ Finset.Ico 0 (L : ℤ)
    · simp [mul_ite, hz]
    · have hpz : p z = 0 := by
        by_contra h
        exact hz (hs z h)
      simp [mul_ite, hz, hpz]
  exact (ENNReal.ofReal_toReal (q.apply_ne_top z)).symm.trans
    ((congrArg ENNReal.ofReal hreal).trans (ENNReal.ofReal_toReal (p.apply_ne_top z)))

end IntegerSourceLaw

end Erdos3

end

end OAI

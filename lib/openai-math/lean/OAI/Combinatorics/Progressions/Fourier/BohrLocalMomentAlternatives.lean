import OAI.Combinatorics.Progressions.Estimates.LocalMomentScale
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem local_alternatives_of_regular_bohr
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (S : Finset (ZMod N)) (hS : S.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    (hfsum : ∑ x, f x = L.carrier.card) (hgsum : ∑ x, g x = L.carrier.card)
    {M delta : ℝ} (hf : ∀ x, |f x| ≤ M) (hg : ∀ x, |g x| ≤ M)
    (hdelta : 0 < delta)
    (hsmall : 1200 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ) * M ≤
      min (delta / 2) (localMomentGain delta))
    {m : ℕ} (hm : 0 < m) :
    sumLp S (fun x => convolution L.carrier f g x - 1) (2 * m) ≤ delta ∨
      ∃ h : ZMod N → ℝ, (h = f ∨ h = g) ∧ ∃ m' : ℕ,
        0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
        1 + localMomentGain delta ≤ differenceLp S (correlation L.carrier h h) (2 * m') := by
  have hM1 := normalized_cap_ge_one L.carrier_nonempty f hfsupport hfsum hf
  have hM : 0 ≤ M := by linarith
  let eta : ℝ := 400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hbudget : 3 * M * eta ≤ min (delta / 2) (localMomentGain delta) := by
    calc
      _ = 1200 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ) * M := by
        dsimp [eta]
        ring
      _ ≤ _ := hsmall
  have hTV (t : ZMod N) (ht : t ∈ L.ndilate (kappa + kappa)) :
      (∑ x, |realUniformMass L.carrier (x - t) - realUniformMass L.carrier x|) ≤ eta :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hkappa ht
  apply local_alternatives_of_boundary L.carrier S hS f g hdelta hm
  · intro s hs t ht
    have hsum : s + t ∈ L.ndilate (kappa + kappa) :=
      CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht)
    have hsymm : ∀ x, -x ∈ L.carrier ↔ x ∈ L.carrier := fun x => L.neg_mem_iff x
    calc
      _ ≤ M * ∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x| :=
        convolution_indicator_sub_one_le L.carrier_nonempty hsymm g hgsupport hgsum hg (s + t)
      _ ≤ M * eta := mul_le_mul_of_nonneg_left (hTV _ hsum) hM
      _ ≤ 3 * M * eta := by nlinarith [mul_nonneg hM heta]
      _ ≤ delta / 2 := hbudget.trans (min_le_left _ _)
  · intro s hs t ht
    have hsub : s - t ∈ L.ndilate (kappa + kappa) :=
      CyclicBohr.Set.sub_mem_ndilate (hSL hs) (hSL ht)
    have hneg : -(s - t) ∈ L.ndilate (kappa + kappa) :=
      ((L.ndilate (kappa + kappa)).neg_mem_iff _).2 hsub
    exact (centered_correlation_error_le L.carrier_nonempty f hfsupport hfsum hf heta
      (s - t) (hTV _ hsub) (hTV _ hneg)).trans (hbudget.trans (min_le_right _ _))

end Erdos3.LocalConvolution

end

end OAI

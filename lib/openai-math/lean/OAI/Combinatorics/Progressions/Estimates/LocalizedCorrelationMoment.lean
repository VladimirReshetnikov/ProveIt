import OAI.Combinatorics.Progressions.Fourier.BohrLocalizedAverage
import OAI.Combinatorics.Progressions.Fourier.TranslatedBohrDifference

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_localized_correlation_moment_at_scale
    (L : Finset (ZMod N)) (hL : L.Nonempty)
    (S : CyclicBohr.Set N) (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular)
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M c : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hc : 0 < c)
    (q : ℕ) (hq : 0 < q) (heven : Even q)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L f f) q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier,
        (1 + c / 2) ^ q ≤
          (𝔼 a ∈ S.carrier, 𝔼 y ∈ C.carrier.image (fun t => b + t), correlation L f f (a - y) ^ q) ∧
        (S.carrier - C.carrier.image (fun t => b + t)).card ≤ 2 * S.carrier.card := by
  have hM : 0 ≤ M := (hf 0).1.trans (hf 0).2
  have hR : 0 ≤ M ^ (2 * q) := pow_nonneg hM _
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  have hmoment : (1 + c) ^ q ≤ differenceMoment S.carrier (correlation L f f) q := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1 + c by linarith) hlarge q
    rwa [differenceLp_pow S.carrier (correlation L f f) hq heven] at h
  obtain ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, havg⟩ :=
    S.exists_localized_difference_average_at_scale hSpos hSreg (fun x => correlation L f f x ^ q)
      hR (fun x => abs_correlation_self_pow_le L hL f hsupport hf x q) hgap kappa hkappa0 hscale
  have hlocalized : (1 + c / 2) ^ q ≤
      𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, correlation L f f (a - (b + t)) ^ q := by
    unfold differenceMoment at hmoment
    linarith
  refine ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, ?_, ?_⟩
  · have himage :
        (𝔼 a ∈ S.carrier, 𝔼 y ∈ C.carrier.image (fun t => b + t), correlation L f f (a - y) ^ q) =
          𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, correlation L f f (a - (b + t)) ^ q := by
      apply Finset.expect_congr rfl
      intro a _
      exact Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)
    exact hlocalized.trans_eq himage.symm
  · have hkappa := hscale.trans (localizedAverageScale_spec S.rank hR hgap).2.1
    exact S.card_sub_translated_small_le_two_mul hSreg hkappa C.carrier hsub b

theorem exists_localized_correlation_moment
    (L : Finset (ZMod N)) (hL : L.Nonempty)
    (S : CyclicBohr.Set N) (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular)
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M c : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hc : 0 < c)
    (q : ℕ) (hq : 0 < q) (heven : Even q)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L f f) q) :
    let kappa := localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q)
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier,
        (1 + c / 2) ^ q ≤
          (𝔼 a ∈ S.carrier, 𝔼 y ∈ C.carrier.image (fun t => b + t), correlation L f f (a - y) ^ q) ∧
        (S.carrier - C.carrier.image (fun t => b + t)).card ≤ 2 * S.carrier.card := by
  have hM : 0 ≤ M := (hf 0).1.trans (hf 0).2
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  exact exists_localized_correlation_moment_at_scale L hL S hSpos hSreg f hsupport
    hf hc q hq heven hlarge _
    (localizedAverageScale_spec S.rank (pow_nonneg hM _) hgap).1 le_rfl

end Erdos3.LocalConvolution

end

end OAI

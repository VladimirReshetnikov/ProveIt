import OAI.Combinatorics.Progressions.Estimates.TranslatedLocalAverage
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation

namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_localized_difference_average_at_scale (S : Set N)
    (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular) (f : ZMod N → ℝ)
    {R epsilon : ℝ} (hR : 0 ≤ R) (hf : ∀ x, |f x| ≤ R) (hepsilon : 0 < epsilon)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank R epsilon) :
    ∃ C : Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier, (𝔼 a ∈ S.carrier, 𝔼 x ∈ S.carrier, f (a - x)) - epsilon ≤
        𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, f (a - (b + t)) := by
  obtain ⟨_, hlimit, hbound⟩ := localizedAverageScale_spec S.rank hR hepsilon
  have hkappa := hscale.trans hlimit
  have hscaleR : (kappa : ℝ) ≤ localizedAverageScale S.rank R epsilon := by
    exact_mod_cast hscale
  have herror : R * (400 * (max S.rank 1 : ℕ) * (kappa : ℝ)) ≤ epsilon := by
    apply le_trans _ hbound
    gcongr
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max S.rank 1) by omega)
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    S.exists_controlled_regular_subdilate hSpos kappa hkappa0 hkappa1
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hCpos : 0 < C.radius := (show 0 < (kappa : ℝ) * S.radius / 2 by positivity).trans_le hlo
  have hTV : ∀ t ∈ C.carrier,
      (∑ x, |realUniformMass S.carrier (x - t) - realUniformMass S.carrier x|) ≤
        400 * (max S.rank 1 : ℕ) * (kappa : ℝ) := by
    intro t ht
    exact uniformMass_translation_le_of_rankRegular hSreg hkappa (hsub ht)
  obtain ⟨b, hb, havg⟩ := exists_translated_local_average S.carrier C.carrier
    S.carrier_nonempty C.carrier_nonempty f hR hf hTV
  refine ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, ?_⟩
  linarith

theorem exists_localized_difference_average (S : Set N)
    (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular) (f : ZMod N → ℝ)
    {R epsilon : ℝ} (hR : 0 ≤ R) (hf : ∀ x, |f x| ≤ R) (hepsilon : 0 < epsilon) :
    let kappa := localizedAverageScale S.rank R epsilon
    ∃ C : Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier, (𝔼 a ∈ S.carrier, 𝔼 x ∈ S.carrier, f (a - x)) - epsilon ≤
        𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, f (a - (b + t)) := by
  exact S.exists_localized_difference_average_at_scale hSpos hSreg f hR hf hepsilon
    (localizedAverageScale S.rank R epsilon)
    (localizedAverageScale_spec S.rank hR hepsilon).1 le_rfl

end Erdos3.CyclicBohr.Set

end

end OAI

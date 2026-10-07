import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement
import OAI.Combinatorics.Progressions.Fourier.BohrTorusApproximation

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_parent_truncated_comparison
    (B L S : CyclicBohr.Set N) (hB : B.IsRankRegular) (hL : L.IsRankRegular)
    {ell sigma delta : ℝ≥0}
    (hLB : L.carrier ⊆ (B.ndilate ell).carrier)
    (hSB : S.carrier ⊆ (B.ndilate sigma).carrier)
    (hSL : S.carrier ⊆ (L.ndilate delta).carrier)
    (hparent : ell + sigma + sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hlocal : delta + delta ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (a f g : ZMod N → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |bilinearIntegral B.carrier B.carrier a f g -
      parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤
      M * (2 * (400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ)) +
        400 * (max L.rank 1 : ℕ) * ((delta + delta : ℝ≥0) : ℝ)) := by
  have hsymm : -L.carrier = L.carrier := by
    ext x
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Finset.mem_neg.mp h
      exact (L.neg_mem_iff y).2 hy
    · intro h
      exact Finset.mem_neg.mpr ⟨-x, (L.neg_mem_iff x).2 h, neg_neg x⟩
  have hfirst : ∀ r ∈ L.carrier,
      (∑ x, |realUniformMass B.carrier (x - r) - realUniformMass B.carrier x|) ≤
        400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ) := by
    intro r hr
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hparent
    exact CyclicBohr.Set.carrier_ndilate_mono
      (show ell ≤ ell + sigma + sigma from (le_self_add).trans le_self_add) (hLB hr)
  have hsecond : ∀ r ∈ L.carrier, ∀ s ∈ S.carrier, ∀ t ∈ S.carrier,
      (∑ x, |realUniformMass B.carrier (x - (-r + s + t)) - realUniformMass B.carrier x|) ≤
        400 * (max B.rank 1 : ℕ) * ((ell + sigma + sigma : ℝ≥0) : ℝ) := by
    intro r hr s hs t ht
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hparent
    have hmem := CyclicBohr.Set.sub_mem_ndilate
      (CyclicBohr.Set.add_mem_ndilate (hSB hs) (hSB ht)) (hLB hr)
    have hscale : sigma + sigma + ell = ell + sigma + sigma := by ac_rfl
    have hpoint : (s + t) - r = -r + s + t := by abel
    rwa [hscale, hpoint] at hmem
  have hboundary : ∀ s ∈ S.carrier, ∀ t ∈ S.carrier,
      (∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x|) ≤
        400 * (max L.rank 1 : ℕ) * ((delta + delta : ℝ≥0) : ℝ) := by
    intro s hs t ht
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hlocal
      (CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht))
  have h := parent_integral_truncated_comparison B.carrier B.carrier L.carrier S.carrier
    B.carrier_nonempty B.carrier_nonempty L.carrier_nonempty S.carrier_nonempty hsymm
    a f g hM ha hf hg hfirst hsecond hboundary
  simpa only [two_mul] using h

theorem bohr_matched_independent_integral_error
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular) (hS : S.IsRankRegular)
    (C : Finset (ZMod N)) (hC : C.Nonempty) {ell sigma : ℝ≥0}
    (hCL : C ⊆ (L.ndilate ell).carrier) (hCS : C ⊆ (S.ndilate sigma).carrier)
    (hell : ell ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hsigma : sigma + sigma ≤ 1 / (100 * (2 * max S.rank 1 : ℕ) : ℝ≥0))
    (a f g : ZMod N → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
      matchedIntegral L.carrier S.carrier a f g| ≤
      M * (400 * (max L.rank 1 : ℕ) * (ell : ℝ) +
        400 * (max S.rank 1 : ℕ) * ((sigma + sigma : ℝ≥0) : ℝ)) := by
  have hfirst : ∀ u ∈ C,
      (∑ x, |realUniformMass L.carrier (x - u) - realUniformMass L.carrier x|) ≤
        400 * (max L.rank 1 : ℕ) * (ell : ℝ) := by
    intro u hu
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hell (hCL hu)
  have hsecond : ∀ u ∈ C, ∀ v ∈ C,
      (∑ x, |realUniformMass S.carrier (x - (u + v)) - realUniformMass S.carrier x|) ≤
        400 * (max S.rank 1 : ℕ) * ((sigma + sigma : ℝ≥0) : ℝ) := by
    intro u hu v hv
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hS hsigma
      (CyclicBohr.Set.add_mem_ndilate (hCS hu) (hCS hv))
  have h := abs_matchedIndependentAverage_sub_le L.carrier S.carrier C L.carrier_nonempty
    S.carrier_nonempty hC (fun x y => f x * g y * a (x + y)) hM
    (fun x y => abs_unit_weighted_mul_le (hf x) (hg y) (ha (x + y))) hfirst hsecond
  rw [matchedIndependentAverage_eq_cells] at h
  exact h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_matching_scales_with_scales
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon)
    (kappa tau : ℝ≥0) (hkappa0 : 0 < kappa)
    (hkappaScale : kappa ≤ localizedAverageScale B.rank M (epsilon / 4))
    (htau0 : 0 < tau) (htau : tau ≤ kappa / 2) :
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = B.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      (kappa : ℝ) * B.radius / 6 ≤ L.radius ∧ L.radius ≤ (kappa : ℝ) * B.radius / 3 ∧
      (kappa : ℝ) * (tau : ℝ) * B.radius / 12 ≤ S.radius ∧ S.radius ≤ (tau : ℝ) * L.radius ∧
      L.carrier ⊆ (B.ndilate (kappa / 3)).carrier ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ M) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ epsilon := by
  obtain ⟨_, hlimit, hbound⟩ := localizedAverageScale_spec B.rank hM
    (show 0 < epsilon / 4 by positivity)
  have hkappa := hkappaScale.trans hlimit
  have hscaleR : (kappa : ℝ) ≤ localizedAverageScale B.rank M (epsilon / 4) := by
    exact_mod_cast hkappaScale
  have herror : M * (400 * (max B.rank 1 : ℕ) * (kappa : ℝ)) ≤ epsilon / 4 := by
    apply le_trans _ hbound
    gcongr
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have hell0 : 0 < kappa / 3 := div_pos hkappa0 (by norm_num)
  have hell1 : kappa / 3 ≤ 1 :=
    (div_le_self (by positivity) (by norm_num)).trans hkappa1
  obtain ⟨L, hLfreq, hLreg, hLlo, hLhi, hLB, _⟩ :=
    B.exists_controlled_regular_subdilate hBpos (kappa / 3) hell0 hell1
  change (kappa : ℝ) / 3 * B.radius / 2 ≤ L.radius at hLlo
  change L.radius ≤ (kappa : ℝ) / 3 * B.radius at hLhi
  have hLlower : (kappa : ℝ) * B.radius / 6 ≤ L.radius := by nlinarith [hLlo]
  have hLupper : L.radius ≤ (kappa : ℝ) * B.radius / 3 := by nlinarith [hLhi]
  have hLpos : 0 < L.radius := (show 0 < (kappa : ℝ) * B.radius / 6 by positivity).trans_le hLlower
  have hLrank : L.rank = B.rank := by simp only [CyclicBohr.Set.rank, hLfreq]
  have htau1 : tau ≤ 1 := htau.trans
    ((div_le_self (by positivity) (by norm_num)).trans hkappa1)
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau0
  obtain ⟨S, hSfreq, hSreg, hSlo, hShi, hSL, _⟩ :=
    L.exists_controlled_regular_subdilate hLpos tau htau0 htau1
  have hSpos : 0 < S.radius :=
    (show 0 < (tau : ℝ) * L.radius / 2 by positivity).trans_le hSlo
  have hSlower : (kappa : ℝ) * (tau : ℝ) * B.radius / 12 ≤ S.radius := by
    have h := mul_le_mul_of_nonneg_left hLlower (show (0 : ℝ) ≤ tau / 2 by positivity)
    nlinarith [hSlo]
  have hSLbase : S.carrier ⊆ L.carrier := by
    have h := hSL.trans (CyclicBohr.Set.carrier_ndilate_mono (B := L) htau1)
    simpa only [CyclicBohr.Set.ndilate_one] using h
  refine ⟨L, S, hLfreq, hSfreq.trans hLfreq, hLreg, hSreg, hLpos, hSpos,
    hLlower, hLupper, hSlower, hShi, hLB, hSL, ?_⟩
  intro a f g ha hf hg
  have hthirds : kappa / 3 + kappa / 3 + kappa / 3 = kappa := by ring
  have htaus : tau + tau ≤ kappa := by
    have h := add_le_add htau htau
    simpa only [add_halves] using h
  have hparent : kappa / 3 + kappa / 3 + kappa / 3 ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by rwa [hthirds]
  have hlocal : tau + tau ≤
      1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) := by
    rw [hLrank]
    exact htaus.trans hkappa
  have h := bohr_parent_truncated_comparison B L S hB hLreg hLB (hSLbase.trans hLB) hSL
    hparent hlocal a f g hM ha hf hg
  rw [hthirds, hLrank] at h
  have htausR : ((tau + tau : ℝ≥0) : ℝ) ≤ kappa := by exact_mod_cast htaus
  have hlocalError : M * (400 * (max B.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ epsilon / 4 := by
    apply le_trans _ herror
    gcongr
  exact h.trans (by nlinarith [herror, hlocalError])

theorem exists_bohr_matching_scales
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    {M epsilon : ℝ} (hM : 0 ≤ M) (hepsilon : 0 < epsilon) :
    let kappa := localizedAverageScale B.rank M (epsilon / 4)
    ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = B.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      (kappa : ℝ) * B.radius / 6 ≤ L.radius ∧ L.radius ≤ (kappa : ℝ) * B.radius / 3 ∧
      (kappa : ℝ) ^ 2 * B.radius / 24 ≤ S.radius ∧ S.radius ≤ (kappa : ℝ) * L.radius / 2 ∧
      L.carrier ⊆ (B.ndilate (kappa / 3)).carrier ∧
      S.carrier ⊆ (L.ndilate (kappa / 2)).carrier ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ M) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ epsilon := by
  intro kappa
  have hkappa0 : 0 < kappa :=
    (localizedAverageScale_spec B.rank hM (show 0 < epsilon / 4 by positivity)).1
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
      hLlo, hLhi, hSlo, hShi, hLB, hSL, hcompare⟩ :=
    exists_bohr_matching_scales_with_scales B hBpos hB hM hepsilon kappa (kappa / 2)
      hkappa0 le_rfl (div_pos hkappa0 (by norm_num)) le_rfl
  refine ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
    hLlo, hLhi, ?_, ?_, hLB, hSL, hcompare⟩
  · change (kappa : ℝ) * ((kappa : ℝ) / 2) * B.radius / 12 ≤ S.radius at hSlo
    nlinarith [hSlo]
  · change S.radius ≤ (kappa : ℝ) / 2 * L.radius at hShi
    nlinarith [hShi]

end Erdos3.CellRefinement

end

end OAI

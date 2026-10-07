import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
import OAI.Combinatorics.Progressions.Estimates.MatchedFlatDecay
import OAI.Combinatorics.Progressions.Estimates.PeelingCellCaps
import OAI.Combinatorics.Progressions.Estimates.PeelingChildBound
import OAI.Combinatorics.Progressions.Estimates.RefinementErrorNormalization

namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def admissibleBohrShape (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (C : CyclicBohr.Set N) : Prop :=
  C.IsRankRegular ∧ C.carrier ⊆ (B.ndilate scale).carrier ∧
    C.rank ≤ B.rank + rankExtra ∧ minimumWidth ≤ C.radius

def admissibleBohrCarriers (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (A : Finset (ZMod N)) : Prop :=
  ∃ C : CyclicBohr.Set N, admissibleBohrShape B scale rankExtra minimumWidth C ∧ A = C.carrier

theorem removed_cell_has_admissible_shape
    {B : CyclicBohr.Set N} {scale : ℝ≥0} {rankExtra : ℕ} {minimumWidth K kappa : ℝ}
    {f g : ZMod N → ℝ} {cs : List (Finset (ZMod N))}
    (h : Chain B.carrier (translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa f g cs) {A : Finset (ZMod N)} (hA : A ∈ cs) :
    ∃ C : CyclicBohr.Set N, ∃ z : ZMod N,
      admissibleBohrShape B scale rankExtra minimumWidth C ∧ A = C.carrier.image (fun t => z + t) := by
  obtain ⟨D, ⟨C, hC, hD⟩, z, hAz⟩ := h.admissible_mem A hA
  exact ⟨C, z, hC, by simpa only [hD] using hAz⟩

theorem exists_budgeted_bohr_peeling
    (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ) (minimumWidth : ℝ)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0) :
    let Shapes := admissibleBohrCarriers B scale rankExtra minimumWidth
    ∃ f' g' cs ds, Chain B.carrier (translatedCellFamily Shapes) K kappa f f' cs ∧
      Chain B.carrier (translatedCellFamily Shapes) K kappa g g' ds ∧
      cs.length + ds.length ≤ (positiveSupport f).card + (positiveSupport g).card ∧
      (∀ x, 0 ≤ f' x ∧ f' x ≤ f x) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ g x) ∧
      (∀ x, x ∉ B.carrier → f' x = 0) ∧ (∀ x, x ∉ B.carrier → g' x = 0) ∧
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
          (potentialCost B.carrier (𝔼 x ∈ B.carrier, g x) f cs +
            potentialCost B.carrier (𝔼 x ∈ B.carrier, f' x) g ds) ≤
        ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) ∧
      coefficientCost B.carrier cs + coefficientCost B.carrier ds ≤
        ((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa) ∧
      ((𝔼 x ∈ B.carrier, f' x) < kappa ∨ (𝔼 x ∈ B.carrier, g' x) < kappa ∨
        ((∀ C, admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
            cellAverage C.carrier f' z ≤ K * (𝔼 x ∈ B.carrier, f' x)) ∧
         (∀ C, admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
            cellAverage C.carrier g' z ≤ K * (𝔼 x ∈ B.carrier, g' x)))) := by
  intro Shapes
  obtain ⟨f', g', cs, ds, hF, hG, hterminal⟩ :=
    exists_terminal_pair_with_cell_caps B.carrier Shapes hK hkappa f g
  refine ⟨f', g', cs, ds, hF, hG,
    Nat.add_le_add (hF.length_le_support hK hkappa) (hG.length_le_support hK hkappa),
    hF.bounds hf, hG.bounds hg, hF.supported hf hfsupport, hG.supported hg hgsupport,
    pair_potential_budget hF hG hK hkappa hf hg hfsupport hgsupport,
    pair_coefficientCost_le hF hG hK hkappa hf hg hfsupport hgsupport, ?_⟩
  rcases hterminal with hfsmall | hgsmall | ⟨hfcap, hgcap⟩
  · exact Or.inl hfsmall
  · exact Or.inr (Or.inl hgsmall)
  · exact Or.inr (Or.inr ⟨fun C hC z => hfcap C.carrier ⟨C, hC, rfl⟩ z,
      fun C hC z => hgcap C.carrier ⟨C, hC, rfl⟩ z⟩)

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_average_square_mean
    (L A B : Finset (ZMod N)) (hL : L.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : CyclicBohr.Set N) (hRpos : 0 < R.radius) (hRreg : R.IsRankRegular)
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M beta epsilon : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hepsilon : 0 < epsilon)
    (hlarge : beta ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L f f (a - b + t)) :
    let sigma := localizedAverageScale R.rank (M ^ 2) epsilon
    ∃ C : CyclicBohr.Set N, C.frequencies = R.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (sigma : ℝ) * R.radius / 4 ≤ C.radius ∧ C.radius ≤ sigma * R.radius / 2 ∧
      C.carrier ⊆ R.carrier ∧
      beta - epsilon ≤ (∑ x, (𝔼 c ∈ C.carrier, f (x + c)) ^ 2) / L.card := by
  intro sigma
  obtain ⟨hsigma0, hsigma, herror⟩ := localizedAverageScale_spec R.rank (sq_nonneg M) hepsilon
  change 0 < sigma at hsigma0
  change sigma ≤ _ at hsigma
  change M ^ 2 * (400 * (max R.rank 1 : ℕ) * (sigma : ℝ)) ≤ epsilon at herror
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max R.rank 1) by omega)
  let kappa : ℝ≥0 := sigma / 2
  have hkappa0 : 0 < kappa := by dsimp [kappa]; positivity
  have hkappa1 : kappa ≤ 1 :=
    (div_le_self hsigma0.le (by norm_num : (1 : ℝ≥0) ≤ 2)).trans hsigma1
  have hkappasum : kappa + kappa = sigma := by dsimp [kappa]; ring
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    R.exists_controlled_regular_subdilate hRpos kappa hkappa0 hkappa1
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hCpos : 0 < C.radius := (show 0 < (kappa : ℝ) * R.radius / 2 by positivity).trans_le hlo
  have hlo' : (sigma : ℝ) * R.radius / 4 ≤ C.radius := by
    have h : (kappa : ℝ) * R.radius / 2 = (sigma : ℝ) * R.radius / 4 := by
      dsimp [kappa]
      ring
    rwa [h] at hlo
  have hhi' : C.radius ≤ (sigma : ℝ) * R.radius / 2 := by
    have h : (kappa : ℝ) * R.radius = (sigma : ℝ) * R.radius / 2 := by
      dsimp [kappa]
      ring
    rwa [h] at hhi
  have hCR : C.carrier ⊆ R.carrier := by
    apply hsub.trans
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := R) hkappa1
  have hTV : ∀ c ∈ C.carrier, ∀ d ∈ C.carrier,
      (∑ x, |realUniformMass R.carrier (x - (c - d)) - realUniformMass R.carrier x|) ≤
        400 * (max R.rank 1 : ℕ) * (sigma : ℝ) := by
    intro c hc d hd
    have hdiff := CyclicBohr.Set.sub_mem_ndilate (hsub hc) (hsub hd)
    rw [hkappasum] at hdiff
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hRreg hsigma hdiff
  have henergy := triple_smoothed_correlation_le_square_mean L A B R.carrier C.carrier
    hL hA hB R.carrier_nonempty C.carrier_nonempty f hsupport hf hTV
  refine ⟨C, hfreq, hreg, hCpos, hlo', hhi', hCR, ?_⟩
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_average_local_second_moment
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (A B : Finset (ZMod N)) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : CyclicBohr.Set N) (hRpos : 0 < R.radius) (hRreg : R.IsRankRegular)
    {kappa : ℝ≥0} (hRL : R.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M beta epsilon : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hepsilon : 0 < epsilon)
    (hlarge : beta ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L.carrier f f (a - b + t)) :
    let sigma := localizedAverageScale R.rank (M ^ 2) epsilon
    ∃ C : CyclicBohr.Set N, C.frequencies = R.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (sigma : ℝ) * R.radius / 4 ≤ C.radius ∧ C.radius ≤ sigma * R.radius / 2 ∧
      C.carrier ⊆ R.carrier ∧
      beta - epsilon - 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 ≤
        𝔼 x ∈ L.carrier, (𝔼 c ∈ C.carrier, f (x + c)) ^ 2 := by
  intro sigma
  obtain ⟨C, hfreq, hreg, hpos, hlo, hhi, hCR, henergy⟩ :=
    exists_bohr_average_square_mean L.carrier A B L.carrier_nonempty hA hB R hRpos hRreg
      f hsupport hf hepsilon hlarge
  have hlocal := square_mean_le_local_add_boundary L hL C.carrier C.carrier_nonempty
    (hCR.trans hRL) hkappa f hsupport hf
  refine ⟨C, hfreq, hreg, hpos, hlo, hhi, hCR, ?_⟩
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_admissible_shape_selection
    (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ) (minimumWidth : ℝ) :
    ∃ shape : Finset (ZMod N) → CyclicBohr.Set N, ∀ D,
      translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D →
        admissibleBohrShape B scale rankExtra minimumWidth (shape D) ∧
          ∃ z, D = (shape D).carrier.image (fun t => z + t) := by
  classical
  have hex : ∀ D : Finset (ZMod N), ∃ C : CyclicBohr.Set N,
      translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D →
        admissibleBohrShape B scale rankExtra minimumWidth C ∧
          ∃ z, D = C.carrier.image (fun t => z + t) := by
    intro D
    by_cases hD : translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D
    · obtain ⟨E, ⟨C, hC, hE⟩, z, hz⟩ := hD
      exact ⟨C, fun _ => ⟨hC, z, by simpa only [hE] using hz⟩⟩
    · exact ⟨B, fun h => False.elim (hD h)⟩
  choose shape hshape using hex
  exact ⟨shape, hshape⟩

theorem admissible_shape_translation_control
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {rankExtra : ℕ} {minimumWidth : ℝ} (D : Finset (ZMod N)) (C : CyclicBohr.Set N)
    (hC : admissibleBohrShape B scale rankExtra minimumWidth C)
    (hD : ∃ z, D = C.carrier.image (fun t => z + t)) :
    D.Nonempty ∧ C.carrier.Nonempty ∧ ∀ t ∈ C.carrier,
      (∑ y, |realUniformMass B.carrier (y - t) - realUniformMass B.carrier y|) ≤
        400 * (max B.rank 1 : ℕ) * (scale : ℝ) := by
  refine ⟨?_, C.carrier_nonempty, ?_⟩
  · obtain ⟨z, rfl⟩ := hD
    obtain ⟨x, hx⟩ := C.carrier_nonempty
    exact ⟨z + x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro t ht
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hscale
    simpa only [CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hC.2.1 ht

end Erdos3.Peeling

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_replacement_family
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (rankExtra : ℕ) (minimumWidth : ℝ) {K kappa M : ℝ}
    (hK : 0 < K) (hkappa : 0 < kappa) (hM : 0 ≤ M)
    (a f g : ZMod N → ℝ) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ B.carrier → g x = 0)
    {f' g' : ZMod N → ℝ} {cs ds : List (Finset (ZMod N))}
    (hF : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa f f' cs)
    (hG : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa g g' ds) :
    ∃ shape : Finset (ZMod N) → CyclicBohr.Set N,
      (∀ D, Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth) D →
        Peeling.admissibleBohrShape B scale rankExtra minimumWidth (shape D) ∧
          ∃ z, D = (shape D).carrier.image (fun t => z + t)) ∧
      |bilinearIntegral B.carrier B.carrier a f g -
        (bilinearIntegral B.carrier B.carrier a f' g' +
          replacementIntegralSum B.carrier B.carrier (fun D => (shape D).carrier) a g f cs +
          replacementIntegralSum B.carrier B.carrier (fun D => (shape D).carrier) a f' g ds)| ≤
        (M * (400 * (max B.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa)) ∧
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
        (replacementPotentialSum B.carrier B.carrier (fun D => (shape D).carrier) g f cs +
          replacementPotentialSum B.carrier B.carrier (fun D => (shape D).carrier) f' g ds) ≤
        ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) := by
  obtain ⟨shape, hshape⟩ := Peeling.exists_admissible_shape_selection B scale rankExtra minimumWidth
  refine ⟨shape, hshape, ?_, ?_⟩
  · apply pair_replacement_integral_error_le_mass hF hG hK hkappa _ a hM
      (by positivity) ha hf hg hfsupport hgsupport
    intro D hD
    exact Peeling.admissible_shape_translation_control B hB hscale D (shape D)
      (hshape D hD).1 (hshape D hD).2
  · exact pair_replacement_potential_budget B.carrier_nonempty hF hG hK hkappa _
      (fun D _ => (shape D).carrier_nonempty) (fun x => (hf x).1) (fun x => (hg x).1)
      hfsupport hgsupport

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_bohr_second_moment_at_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ S.carrier ∧ C.carrier ⊆ (S.ndilate kappa).carrier ∧
      (C.rank : ℝ) ≤ S.rank + almostPeriodicityWidthConstant (c / 64) * (1 + D) ^ 4 ∧
      ((kappa : ℝ) * (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) * S.radius / 8) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ C.radius ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  intro D
  have htol : 0 < c / 64 := by positivity
  have hcontrol := unbalanced_error_control hc hc1
  obtain ⟨C₀, hfreq₀, _, _, hlow₀, _, hC₀S, hC₀small, _, _, A, _, B, _, hA, hB, _, _,
      R, hRreg, hRpos, hRwidth, hRC₀, hRrank, hRlow, hlargeR⟩ :=
    exists_smoothing_of_large_correlation_at_scale L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      f hsupport hM hc htol htol hcontrol.2.1 hp hH hcap hf q hq heven hqp hlarge hseparation kappa hkappa0 hscale
  have hRSL : R.carrier ⊆ (L.ndilate kappa₀).carrier := (hRC₀.trans hC₀S).trans hSL
  obtain ⟨C, hfreq, hCreg, hCpos, hClow, hChi, hCR, hsecond⟩ :=
    exists_bohr_average_local_second_moment L hL A B hA hB R hRpos hRreg hRSL hkappa₀
      f hsupport hf htol hlargeR
  have hCrank : C.rank = R.rank := congrArg Finset.card hfreq
  have hC₀rank : C₀.rank = S.rank := congrArg Finset.card hfreq₀
  have hsigma1 : (localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) ≤ 1 := by
    exact_mod_cast localizedAverageScale_le_one R.rank (sq_nonneg M) htol
  have hCwidth : C.radius ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hsigma1 R.radius_nonneg
    have hnonneg := (localizedAverageScale R.rank (M ^ 2) (c / 64)).coe_nonneg
    have hRnonneg := R.radius_nonneg
    linarith
  refine ⟨C, hCreg, hCpos, hCwidth, hCR.trans (hRC₀.trans hC₀S),
    hCR.trans (hRC₀.trans hC₀small), ?_, ?_, ?_⟩
  · rw [hCrank]
    simpa only [hC₀rank] using hRrank
  · rw [hCrank]
    have hRlow' : ((kappa : ℝ) * S.radius / 2) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ R.radius := by
      have h := mul_le_mul_of_nonneg_right hlow₀
        (Real.exp_nonneg (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))))
      exact h.trans (by simpa only [hC₀rank] using hRlow)
    calc
      _ = ((localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) / 4) *
          (((kappa : ℝ) * S.radius / 2) *
            Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
              (1 + D + Real.log (2 + S.rank))))) := by ring
      _ ≤ ((localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) / 4) * R.radius :=
        mul_le_mul_of_nonneg_left hRlow' (by positivity)
      _ = (localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) * R.radius / 4 := by ring
      _ ≤ C.radius := hClow
  · change (1 + c / 4) * (1 - c / 64 - c / 64) - c / 64 -
      200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤
        𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 at hsecond
    have hgain := hcontrol.2.2.2
    linarith

theorem exists_unbalanced_bohr_second_moment
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q) :
    let kappa := localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ S.carrier ∧
      (C.rank : ℝ) ≤ S.rank + almostPeriodicityWidthConstant (c / 64) * (1 + D) ^ 4 ∧
      ((kappa : ℝ) * (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) * S.radius / 8) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ C.radius ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  intro kappa D
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  obtain ⟨C, hreg, hpos, hwidth, hCS, _, hrank, hlower, hsecond⟩ :=
    exists_unbalanced_bohr_second_moment_at_scale L S hL hSpos hSwidth hSreg hSrank
      hSL hkappa₀ f hsupport hM hc hc1 hp hH hcap hf hboundary q hq heven hqp
      hlarge hseparation kappa
      (localizedAverageScale_spec S.rank (pow_nonneg hM.le _) hgap).1 le_rfl
  exact ⟨C, hreg, hpos, hwidth, hCS, hrank, hlower, hsecond⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_peeling_parent_bound
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (rankExtra : ℕ) (minimumWidth : ℝ) {K kappa T rho error W : ℝ}
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hW : 0 ≤ W)
    (a f g : ZMod N → ℝ) (origin : ZMod N) (ha : ∀ x, |a x| ≤ W)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0)
    {f' g' : ZMod N → ℝ} {cs ds : List (Finset (ZMod N))}
    (hF : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa f f' cs)
    (hG : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa g g' ds)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C →
      CellBilinearBound C.carrier a T)
    (hremainder : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + error) :
    bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f g ≤
      T * rho * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + error +
        (W * (400 * (max B.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa)) := by
  obtain ⟨shape, hshape⟩ := Peeling.exists_admissible_shape_selection B scale rankExtra minimumWidth
  apply peeling_parent_bound_of_remainder B.carrier_nonempty hF hG hK hkappa hKfactor hT hrho
    hW (by positivity) (fun D => (shape D).carrier) a origin ha hf hg hfsupport hgsupport _ hremainder
  intro D hD
  obtain ⟨hC, htranslate⟩ := hshape D hD
  obtain ⟨hDn, hCn, hTV⟩ := Peeling.admissible_shape_translation_control B hB hscale D (shape D) hC htranslate
  exact ⟨hDn, hCn, htranslate, hchildren (shape D) hC, hTV⟩

theorem bohr_parent_bound_from_capped
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (rankExtra : ℕ) (minimumWidth : ℝ) {K kappa T rho epsilon eta W : ℝ}
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (htiny : W * kappa ^ (3 / 4 : ℝ) ≤ epsilon)
    (a f g : ZMod N → ℝ) (origin : ZMod N) (ha : ∀ x, |a x| ≤ W)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C →
      CellBilinearBound C.carrier a T)
    (hcapped : ∀ f' g' : ZMod N → ℝ,
      (∀ x, 0 ≤ f' x ∧ f' x ≤ 1) → (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) →
      (∀ x, x ∉ B.carrier → f' x = 0) → (∀ x, x ∉ B.carrier → g' x = 0) →
      kappa ≤ (𝔼 x ∈ B.carrier, f' x) → kappa ≤ (𝔼 x ∈ B.carrier, g' x) →
      (∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
        cellAverage C.carrier f' z ≤ K * (𝔼 x ∈ B.carrier, f' x)) →
      (∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
        cellAverage C.carrier g' z ≤ K * (𝔼 x ∈ B.carrier, g' x)) →
      bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
        (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + eta) :
    bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f g ≤
      (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + eta +
        (W * (400 * (max B.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa)) := by
  obtain ⟨f', g', cs, ds, hF, hG, _, hfb, hgb, hfs, hgs, _, _, hterminal⟩ :=
    Peeling.exists_budgeted_bohr_peeling B scale rankExtra minimumWidth hK hkappa f g
      (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := fun x => ⟨(hfb x).1, (hfb x).2.trans (hf x).2⟩
  have hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1 := fun x => ⟨(hgb x).1, (hgb x).2.trans (hg x).2⟩
  have hPhi := quarter_cell_potential_mono B.carrier f f' g g' (fun x => (hfb x).1)
    (fun x => (hgb x).1) (fun x => (hfb x).2) (fun x => (hgb x).2)
  have hPhi0 : 0 ≤ ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun x _ => (hf' x).1))
      (Finset.expect_nonneg (fun x _ => (hg' x).1))) _
  have hrem : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + eta := by
    by_cases hsmall : min (𝔼 x ∈ B.carrier, f' x) (𝔼 x ∈ B.carrier, g' x) < kappa
    · have h := tiny_cell_integral_le B.carrier B.carrier_nonempty a f' g' origin hW
        (fun x => (le_abs_self (a x)).trans (ha x)) hf' hg' hsmall
      have hcoef := mul_nonneg hT (show 0 ≤ rho by linarith)
      have ht := mul_le_mul_of_nonneg_right htiny hPhi0
      nlinarith only [h, ht, mul_nonneg hcoef hPhi0, heta]
    · have hlower := le_min_iff.mp (le_of_not_gt hsmall)
      rcases hterminal with hsmallF | hsmallG | ⟨hcapF, hcapG⟩
      · exact False.elim (hsmall (min_lt_iff.mpr (Or.inl hsmallF)))
      · exact False.elim (hsmall (min_lt_iff.mpr (Or.inr hsmallG)))
      · exact hcapped f' g' hf' hg' hfs hgs hlower.1 hlower.2 hcapF hcapG
  have hrem' : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) +
        (epsilon * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + eta) := by
    have h := mul_le_mul_of_nonneg_left hPhi hepsilon
    nlinarith only [hrem, h]
  have h := bohr_peeling_parent_bound B hB hscale rankExtra minimumWidth hK hkappa hKfactor
    hT hrho hW a f g origin ha hf hg hfsupport hgsupport hF hG hchildren hrem'
  nlinarith only [h]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

noncomputable def unbalancedRankExtra (c p H : ℝ) : ℕ :=
  ⌈almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4⌉₊

noncomputable def unbalancedMinimumWidth (S : CyclicBohr.Set N) (M c p H : ℝ) (q : ℕ) : ℝ :=
  (localizedAverageScale S.rank (M ^ (2 * q)) ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ) *
    (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
    S.radius / 8 * Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
      (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank))))

theorem unbalancedMinimumWidth_pos (S : CyclicBohr.Set N) (hS : 0 < S.radius)
    {M c p H : ℝ} (hM : 0 ≤ M) (hc : 0 < c) {q : ℕ} (hq : 0 < q) :
    0 < unbalancedMinimumWidth S M c p H q := by
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  have hκ := (localizedAverageScale_spec S.rank (pow_nonneg hM (2 * q)) hgap).1
  have hσ := (localizedAverageScale_spec (S.rank + unbalancedRankExtra c p H)
    (sq_nonneg M) (show 0 < c / 64 by positivity)).1
  have hκR : (0 : ℝ) < localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q) := by exact_mod_cast hκ
  have hσR : (0 : ℝ) < localizedAverageScale (S.rank + unbalancedRankExtra c p H)
      (M ^ 2) (c / 64) := by exact_mod_cast hσ
  unfold unbalancedMinimumWidth
  positivity

theorem exists_unbalanced_admissible_shape
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (unbalancedMinimumWidth S M c p H q) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  obtain ⟨C, hCreg, hCpos, hCwidth, hCS, hrank, hwidth, hsecond⟩ :=
    exists_unbalanced_bohr_second_moment L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      f hsupport hM hc hc1 hp hH hcap hf hboundary q hq heven hqp hlarge hseparation
  have hbound : C.rank ≤ S.rank + unbalancedRankExtra c p H := by
    have hceil := Nat.le_ceil
      (almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4)
    have hreal : (C.rank : ℝ) ≤ (S.rank : ℝ) + (unbalancedRankExtra c p H : ℝ) :=
      hrank.trans (add_le_add le_rfl hceil)
    exact_mod_cast hreal
  have hσ := localizedAverageScale_antitone_rank (sq_nonneg M)
    (show 0 ≤ c / 64 by positivity) hbound
  have hσR : (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) ≤
      (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) := by exact_mod_cast hσ
  refine ⟨C, ⟨hCreg, ?_, hbound, ?_⟩, hCpos, hCwidth, hsecond⟩
  · simpa only [CyclicBohr.Set.ndilate_one] using hCS
  · apply le_trans _ hwidth
    unfold unbalancedMinimumWidth
    gcongr

end Erdos3.LocalConvolution

end

end OAI

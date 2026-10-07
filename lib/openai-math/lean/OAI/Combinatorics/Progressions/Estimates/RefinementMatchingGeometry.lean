import OAI.Combinatorics.Progressions.Estimates.ParentControlledMatching
import OAI.Combinatorics.Progressions.Fourier.BohrMatchedContraction
import OAI.Combinatorics.Progressions.Polynomial.UnbalancedPolynomialBudget

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_matched_contraction
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (unbalancedMinimumWidth S M c p H q) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (unbalancedMinimumWidth S M c p H q) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hkappa₀ : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) :=
    le_trans le_self_add hkappa
  have hboundary : 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 ≤ c / 64 := by
    have heq : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) =
        4 * (200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2) := by
      rw [NNReal.coe_add]
      ring
    rw [heq] at herror
    linarith
  have hdata : (∀ x, x ∉ L.carrier → h x = 0) ∧ (∀ x, 0 ≤ h x ∧ h x ≤ M) := by
    rcases hchoice with rfl | rfl
    · exact ⟨fun x hx => by dsimp only; rw [hfsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hf x) hu.le, hcapf x⟩⟩
    · exact ⟨fun x hx => by dsimp only; rw [hgsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hg x) hv.le, hcapg x⟩⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hsecond⟩ :=
    exists_unbalanced_admissible_shape L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      h hdata.1 hM hc hc1 hp hH hMcap hdata.2 hboundary q hq heven hqp hlarge hseparation
  have hsecond' :
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => f y / u) x ^ 2) ∨
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => g y / v) x ^ 2) := by
    rcases hchoice with hchoice | hchoice
    · exact Or.inl (by simpa only [hchoice] using hsecond)
    · exact Or.inr (by simpa only [hchoice] using hsecond)
  have hcontraction := bohr_matched_potential_contraction L hL S.carrier C.carrier
    S.carrier_nonempty C.carrier_nonempty hSL hkappa f g hf hg hfsupport hgsupport
    hu hv (show 0 < c / 16 by positivity) (show c / 16 ≤ 1 by linarith)
    hmeanf hmeang hcapg (hcells C hshape).1 (hcells C hshape).2
    (by convert herror using 1; ring) hsecond'
  refine ⟨C, hshape, hCpos, hCwidth, ?_⟩
  have heq : c / 16 / (8 * (1 + Real.sqrt K) ^ 2) =
      c / (128 * (1 + Real.sqrt K) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using hcontraction

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_small_scale_unbalanced_shape
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
    (zeta : ℝ≥0) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  let kappa := localizedAverageScale S.rank (M ^ (2 * q))
    ((1 + c) ^ q - (1 + c / 2) ^ q)
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q :=
    lt_of_lt_of_le (by positivity : 0 < c / 2) (unbalanced_power_gap hc hq)
  have hkappa : 0 < kappa := (localizedAverageScale_spec S.rank
    (pow_nonneg hM.le _) hgap).1
  have hkappa1 : kappa ≤ 1 := localizedAverageScale_le_one S.rank
    (pow_nonneg hM.le _) hgap
  have hscale : zeta * kappa ≤ kappa := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hzeta1 (show 0 ≤ kappa by positivity)
  have hsmall : zeta * kappa ≤ zeta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hkappa1 (show 0 ≤ zeta by positivity)
  obtain ⟨C, hCreg, hCpos, hCwidth, _, hCS, hrank, hwidth, hsecond⟩ :=
    exists_unbalanced_bohr_second_moment_at_scale L S hL hSpos hSwidth hSreg hSrank
      hSL hkappa₀ f hsupport hM hc hc1 hp hH hcap hf hboundary q hq heven hqp
      hlarge hseparation (zeta * kappa) (mul_pos hzeta hkappa) hscale
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
  have hminimum : (zeta : ℝ) * unbalancedMinimumWidth S M c p H q ≤ C.radius := by
    apply le_trans _ hwidth
    rw [NNReal.coe_mul]
    unfold unbalancedMinimumWidth
    dsimp only [kappa]
    calc
      _ = ((zeta : ℝ) * (localizedAverageScale S.rank (M ^ (2 * q))
          ((1 + c) ^ q - (1 + c / 2) ^ q) : ℝ)) *
          (localizedAverageScale (S.rank + unbalancedRankExtra c p H) (M ^ 2) (c / 64) : ℝ) *
          S.radius / 8 * Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
            (1 + (3 * H + 1) * p ^ 2 + Real.log (2 + S.rank)))) := by ring
      _ ≤ _ := by gcongr
  refine ⟨C, ⟨hCreg, hCS.trans (CyclicBohr.Set.carrier_ndilate_mono hsmall),
    hbound, ?_⟩, hCpos, hCwidth, hsecond⟩
  have h := mul_le_mul_of_nonneg_left
    (unbalancedMinimumWidth_exp_lower S hM.le hc hc1 hp hH hcap hq hqp) zeta.coe_nonneg
  simpa only [← mul_assoc] using h.trans hminimum

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_small_scale_unbalanced_contraction
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (zeta : ℝ≥0) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hkappa₀ : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) :=
    le_trans le_self_add hkappa
  have hboundary : 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 ≤ c / 64 := by
    have heq : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) =
        4 * (200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2) := by
      rw [NNReal.coe_add]
      ring
    rw [heq] at herror
    linarith
  have hdata : (∀ x, x ∉ L.carrier → h x = 0) ∧ (∀ x, 0 ≤ h x ∧ h x ≤ M) := by
    rcases hchoice with rfl | rfl
    · exact ⟨fun x hx => by dsimp only; rw [hfsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hf x) hu.le, hcapf x⟩⟩
    · exact ⟨fun x hx => by dsimp only; rw [hgsupport x hx, zero_div],
        fun x => ⟨div_nonneg (hg x) hv.le, hcapg x⟩⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hsecond⟩ :=
    exists_small_scale_unbalanced_shape L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      h hdata.1 hM hc hc1 hp hH hMcap hdata.2 hboundary q hq heven hqp hlarge hseparation
      zeta hzeta hzeta1
  have hsecond' :
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => f y / u) x ^ 2) ∨
      (1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier (fun y => g y / v) x ^ 2) := by
    rcases hchoice with hchoice | hchoice
    · exact Or.inl (by simpa only [hchoice] using hsecond)
    · exact Or.inr (by simpa only [hchoice] using hsecond)
  have hcontraction := bohr_matched_potential_contraction L hL S.carrier C.carrier
    S.carrier_nonempty C.carrier_nonempty hSL hkappa f g hf hg hfsupport hgsupport
    hu hv (show 0 < c / 16 by positivity) (show c / 16 ≤ 1 by linarith)
    hmeanf hmeang hcapg (hcells C hshape).1 (hcells C hshape).2
    (by convert herror using 1; ring) hsecond'
  refine ⟨C, hshape, hCpos, hCwidth, ?_⟩
  have heq : c / 16 / (8 * (1 + Real.sqrt K) ^ 2) =
      c / (128 * (1 + Real.sqrt K) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using hcontraction

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem unbalanced_shape_to_uniform
    (S C : CyclicBohr.Set N) {M c p H : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) {q : ℕ} (hq : 0 < q) (hqp : (q : ℝ) ≤ H * p)
    (hshape : Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
      (unbalancedMinimumWidth S M c p H q) C) :
    Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
      (S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C :=
  ⟨hshape.1, hshape.2.1, hshape.2.2.1,
    (unbalancedMinimumWidth_exp_lower S hM hc hc1 hp hH hcap hq hqp).trans hshape.2.2.2⟩

theorem exists_uniform_unbalanced_matched_contraction
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hconvert (C : CyclicBohr.Set N) :=
    unbalanced_shape_to_uniform S C hM.le hc hc1 hp hH hMcap hq hqp
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction⟩ :=
    exists_unbalanced_matched_contraction L S hL hSpos hSwidth hSreg hSrank hSL hkappa
      f g hf hg hfsupport hgsupport hu hv hmeanf hmeang hM hc hc1 hp hH hMcap hcapf hcapg
      herror q hq heven hqp h hchoice hlarge hseparation
      (fun C hC => hcells C (hconvert C hC))
  exact ⟨C, hconvert C hshape, hCpos, hCwidth, hcontraction⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

noncomputable def unbalancedReturnWidthLoss (rank : ℕ) (c p H A E : ℝ) : ℝ :=
  (rank : ℝ) + A + E + 1602 + unbalancedWidthLoss rank c p H

theorem unbalanced_return_width_lower {N : ℕ} [NeZero N]
    (S : CyclicBohr.Set N) (c p H : ℝ) {W A E : ℝ}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E) ≤
      (CellRefinement.independentReturnScale S.rank W (Real.exp (-E)) : ℝ) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
  have h := CellRefinement.independentReturnScale_exp_lower S.rank hW hWcap hA hE
  calc
    _ = Real.exp (-((S.rank : ℝ) + A + E + 1602)) * S.radius *
        Real.exp (-unbalancedWidthLoss S.rank c p H) := by
      unfold unbalancedReturnWidthLoss
      rw [neg_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h S.radius_nonneg) (Real.exp_nonneg _)

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_independent_refinement
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hwidth : S.radius ≤ L.radius)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M K c p H : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) ≤ u) (hmeang : (𝔼 x ∈ L.carrier, g x) ≤ v)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun x => f x / u) ∨ h = (fun x => g x / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    {W A E : ℝ} (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hcells : ∀ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C →
      (∀ x, cellAverage C.carrier f x / u ≤ K) ∧
        (∀ x, cellAverage C.carrier g x / v ≤ K)) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape S (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - c / (128 * (1 + Real.sqrt K) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            CellRefinement.bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          CellRefinement.matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  let zeta := CellRefinement.independentReturnScale S.rank W (Real.exp (-E))
  obtain ⟨hzeta, hzeta1, _, _⟩ := CellRefinement.independentReturnScale_spec S.rank hW
    (Real.exp_pos (-E))
  have hconvert (C : CyclicBohr.Set N)
      (hshape : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        ((zeta : ℝ) * S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C) :
      Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C :=
    ⟨hshape.1, hshape.2.1, hshape.2.2.1,
      (unbalanced_return_width_lower S c p H hW hWcap hA hE).trans hshape.2.2.2⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction⟩ :=
    exists_small_scale_unbalanced_contraction L S hL hSpos hSwidth hSreg hSrank hSL hkappa
      f g (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport hu hv hmeanf hmeang
      hM hc hc1 hp hH hMcap hcapf hcapg herror q hq heven hqp h hchoice hlarge hseparation
      zeta hzeta hzeta1 (fun C hC => hcells C (hconvert C hC))
  refine ⟨C, hconvert C hshape, hCpos, hCwidth, hcontraction, ?_⟩
  intro a ha
  exact CellRefinement.bohr_matched_independent_at_return_scale L S hL hSreg hfreq hwidth
    C.carrier C.carrier_nonempty a f g hW (Real.exp_pos (-E)) hshape.2.1 ha hf hg

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem admissibleBohrShape_transfer
    {B S C : CyclicBohr.Set N} {scaleB scaleS : ℝ≥0}
    {extraB extraS : ℕ} {widthB widthS : ℝ}
    (hsub : (S.ndilate scaleS).carrier ⊆ (B.ndilate scaleB).carrier)
    (hrank : S.rank + extraS ≤ B.rank + extraB) (hwidth : widthB ≤ widthS)
    (hC : admissibleBohrShape S scaleS extraS widthS C) :
    admissibleBohrShape B scaleB extraB widthB C :=
  ⟨hC.1, hC.2.1.trans hsub, hC.2.2.1.trans hrank, hwidth.trans hC.2.2.2⟩

theorem uniform_unbalanced_shape_in_parent
    {B S C : CyclicBohr.Set N} {scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H : ℝ}
    (hsub : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + LocalConvolution.unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-LocalConvolution.unbalancedWidthLoss S.rank c p H))
    (hC : admissibleBohrShape S 1 (LocalConvolution.unbalancedRankExtra c p H)
      (S.radius * Real.exp (-LocalConvolution.unbalancedWidthLoss S.rank c p H)) C) :
    admissibleBohrShape B scale extra minimumWidth C :=
  admissibleBohrShape_transfer
    (by simpa only [CyclicBohr.Set.ndilate_one] using hsub) hrank hwidth hC

theorem normalized_local_caps_from_parent
    {B S : CyclicBohr.Set N} {scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H : ℝ}
    (hsub : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + LocalConvolution.unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-LocalConvolution.unbalancedWidthLoss S.rank c p H))
    (f F : ZMod N → ℝ) (x : ZMod N) (hF : ∀ r, F r ≤ f (x + r))
    {u u₀ c₀ K : ℝ} (hu : 0 < u) (hc₀ : 0 < c₀) (hK : 0 ≤ K) (hlower : c₀ * u ≤ u₀)
    (hparent : ∀ C, admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier f z ≤ K * u) :
    ∀ C, admissibleBohrShape S 1 (LocalConvolution.unbalancedRankExtra c p H)
      (S.radius * Real.exp (-LocalConvolution.unbalancedWidthLoss S.rank c p H)) C →
      ∀ z, cellAverage C.carrier F z / u₀ ≤ K / c₀ := by
  intro C hC z
  exact normalized_local_cell_cap C.carrier f F x hF hu hc₀ hK hlower
    (hparent C (uniform_unbalanced_shape_in_parent hsub hrank hwidth hC)) z

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_parent_unbalanced_contraction
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H : ℝ}
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H))
    (F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) ≤ u) (hmeang : (𝔼 r ∈ L.carrier, g r) ≤ v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun r => f r / u) ∨ h = (fun r => g r / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S 1 (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedWidthLoss S.rank c p H)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      let rho := 1 - c / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ) := by
  have hu : 0 < u := (mul_pos hc₀ hU).trans_le hlowerf
  have hv : 0 < v := (mul_pos hc₀ hV).trans_le hlowerg
  have hcellsf := Peeling.normalized_local_caps_from_parent hSB hrank hwidth
    F f x hdomf hU hc₀ hK hlowerf hparentF
  have hcellsg := Peeling.normalized_local_caps_from_parent hSB hrank hwidth
    G g y hdomg hV hc₀ hK hlowerg hparentG
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction⟩ :=
    exists_uniform_unbalanced_matched_contraction L S hL hSpos hSwidth hSreg hSrank hSL hkappa
      f g hf hg hfsupport hgsupport hu hv hmeanf hmeang hM hc hc1 hp hH hMcap hcapf hcapg
      herror q hq heven hqp h hchoice hlarge hseparation
      (fun C hC => ⟨hcellsf C hC, hcellsg C hC⟩)
  exact ⟨C, Peeling.uniform_unbalanced_shape_in_parent hSB hrank hwidth hshape,
    hshape, hCpos, hCwidth, hcontraction⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_parent_unbalanced_independent_refinement
    (B L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth c p H W A E : ℝ}
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra c p H ≤ B.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E))
    (F G f g : ZMod N → ℝ) (x y : ZMod N)
    (hdomf : ∀ r, f r ≤ F (x + r)) (hdomg : ∀ r, g r ≤ G (y + r))
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (hfsupport : ∀ r, r ∉ L.carrier → f r = 0)
    (hgsupport : ∀ r, r ∉ L.carrier → g r = 0)
    {U V u v M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerf : c₀ * U ≤ u) (hlowerg : c₀ * V ≤ v)
    (hmeanf : (𝔼 r ∈ L.carrier, f r) ≤ u) (hmeang : (𝔼 r ∈ L.carrier, g r) ≤ v)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hMcap : M ≤ Real.exp p) (hcapf : ∀ r, f r / u ≤ M) (hcapg : ∀ r, g r / v ≤ M)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ c / 32)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (h : ZMod N → ℝ) (hchoice : h = (fun r => f r / u) ∨ h = (fun r => g r / v))
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier h h) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B scale extra minimumWidth C ∧
      Peeling.admissibleBohrShape S
        (CellRefinement.independentReturnScale S.rank W (Real.exp (-E))) (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      (let rho := 1 - c / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
      3 / 4 ≤ rho ∧ rho < 1 ∧
        (𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
          (matchedFirstCell C.carrier f z * matchedSecondCell C.carrier g z) ^ (1 / 4 : ℝ)) ≤
          rho * (u * v) ^ (1 / 4 : ℝ)) ∧
      ∀ a : ZMod N → ℝ, (∀ r, |a r| ≤ W) →
        |(𝔼 z ∈ matchedCellSpace L.carrier S.carrier,
            CellRefinement.bilinearIntegral (C.carrier.image (fun t => z.1 + t))
              (C.carrier.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g) -
          CellRefinement.matchedIntegral L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  have hu : 0 < u := (mul_pos hc₀ hU).trans_le hlowerf
  have hv : 0 < v := (mul_pos hc₀ hV).trans_le hlowerg
  let zeta := CellRefinement.independentReturnScale S.rank W (Real.exp (-E))
  have hzeta1 : zeta ≤ 1 :=
    (CellRefinement.independentReturnScale_spec S.rank hW (Real.exp_pos (-E))).2.1
  have hsub : (S.ndilate zeta).carrier ⊆ (B.ndilate scale).carrier := by
    have h := CyclicBohr.Set.carrier_ndilate_mono (B := S) hzeta1
    rw [CyclicBohr.Set.ndilate_one] at h
    exact h.trans hSB
  have hconvert (C : CyclicBohr.Set N)
      (hC : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C) :
      Peeling.admissibleBohrShape B scale extra minimumWidth C :=
    Peeling.admissibleBohrShape_transfer hsub hrank hwidth hC
  have hcells (C : CyclicBohr.Set N)
      (hC : Peeling.admissibleBohrShape S zeta (unbalancedRankExtra c p H)
        (S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H A E)) C) :
      (∀ r, cellAverage C.carrier f r / u ≤ K / c₀) ∧
        (∀ r, cellAverage C.carrier g r / v ≤ K / c₀) := by
    exact ⟨fun r => normalized_local_cell_cap C.carrier F f x hdomf hU hc₀ hK hlowerf
        (hparentF C (hconvert C hC)) r,
      fun r => normalized_local_cell_cap C.carrier G g y hdomg hV hc₀ hK hlowerg
        (hparentG C (hconvert C hC)) r⟩
  obtain ⟨C, hshape, hCpos, hCwidth, hcontraction, hintegral⟩ :=
    exists_unbalanced_independent_refinement L S hL hSpos hSwidth hSreg hSrank hfreq hlocalWidth
      hSL hkappa f g hf hg hfsupport hgsupport hu hv hmeanf hmeang hM hc hc1 hp hH
      hMcap hcapf hcapg herror q hq heven hqp h hchoice hlarge hseparation hW hWcap hA hE hcells
  exact ⟨C, hconvert C hshape, hshape, hCpos, hCwidth, hcontraction, hintegral⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

noncomputable def refinementMatchingWidthLoss (rank : ℕ) (p H Q E J T delta : ℝ) : ℝ :=
  matchingWidthLoss rank p (outerMatchingScaleLoss rank Q E T) delta (localMomentGain delta) +
    unbalancedReturnWidthLoss rank (localMomentGain delta) p H Q J

variable {N : ℕ} [NeZero N]

theorem exists_refinement_matching_geometry
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (hBwidth : B.radius ≤ 2) (hBrank : 1 ≤ B.rank)
    {W Q E M p H J T R delta : ℝ} {scale : ℝ≥0}
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hM : 0 ≤ M) (hMcap : M ≤ Real.exp p) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hJ : 0 ≤ J) (hT : 0 ≤ T) (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hBwide : Real.exp (-R) ≤ B.radius) (hscale : Real.exp (-T) ≤ (scale : ℝ)) :
    let c := localMomentGain delta
    let kappa := outerMatchingScale B.rank W (Real.exp (-E)) scale
    let tau := coordinatedMatchingScale B.rank M delta c kappa
    let D := matchingWidthLoss B.rank p (outerMatchingScaleLoss B.rank Q E T) delta c
    let w := B.radius * Real.exp (-refinementMatchingWidthLoss B.rank p H Q E J T delta)
    0 ≤ R + D ∧ ∃ L S : CyclicBohr.Set N,
      L.frequencies = B.frequencies ∧ S.frequencies = L.frequencies ∧
      L.IsRankRegular ∧ S.IsRankRegular ∧ 0 < L.radius ∧ 0 < S.radius ∧
      S.radius ≤ L.radius ∧ S.radius ≤ 1 ∧ 1 ≤ S.rank ∧
      Peeling.admissibleBohrShape B scale (unbalancedRankExtra c p H) w L ∧
      S.carrier ⊆ (B.ndilate scale).carrier ∧
      S.rank + unbalancedRankExtra c p H ≤ B.rank + unbalancedRankExtra c p H ∧
      w ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q J) ∧
      Real.exp (-(R + D)) ≤ S.radius ∧
      S.carrier ⊆ (L.ndilate tau).carrier ∧
      S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier ∧
      tau + tau ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0) ∧
      M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((tau + tau : ℝ≥0) : ℝ)) ≤ c / 32 ∧
      ∀ a f g : ZMod N → ℝ, (∀ x, |a x| ≤ W) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
        |bilinearIntegral B.carrier B.carrier a f g -
          parentTruncatedIntegral B.carrier B.carrier L.carrier S.carrier a f g| ≤ Real.exp (-E) := by
  intro c kappa tau D w
  have hc : 0 < c := localMomentGain_pos delta
  have hc1 : c ≤ 1 := (localMomentGain_le_half delta).trans (by norm_num)
  have hp0 : 0 ≤ p := by linarith
  have hK := outerMatchingScaleLoss_nonneg B.rank hQ hE hT
  have hD : 0 ≤ D := matchingWidthLoss_nonneg B.rank hp0 hK hdelta hc hc1
  refine ⟨add_nonneg hR hD, ?_⟩
  obtain ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos,
      hLwidth, hSwidth, hLlower, hSlower, hLB, hSL, hmoment, hsmall, herror, hcompare⟩ :=
    exists_parent_controlled_matching B hBpos hB hW hWcap hQ hE hM hMcap hp0 hT
      hdelta hc hc1 hscale
  have hLrank : L.rank = B.rank := congrArg Finset.card hLfreq
  have hSrank : S.rank = B.rank := congrArg Finset.card (hSfreq.trans hLfreq)
  have hSLbase : S.carrier ⊆ L.carrier := by
    apply CyclicBohr.Set.carrier_mono
    · rw [hSfreq]
    · exact hSwidth
  have hU : 0 ≤ unbalancedReturnWidthLoss B.rank c p H Q J := by
    have h := unbalancedWidthLoss_nonneg B.rank hc hc1 hp0 hH
    unfold unbalancedReturnWidthLoss
    positivity
  have hDlarge : outerMatchingScaleLoss B.rank Q E T + 6 ≤ D := by
    have hEd := (localMomentErrorBudget_spec hdelta).1
    have hEc := (unbalancedErrorBudget_spec hc hc1).1
    have hrank : (0 : ℝ) ≤ B.rank := Nat.cast_nonneg B.rank
    change _ ≤ matchingWidthLoss B.rank p (outerMatchingScaleLoss B.rank Q E T) delta c
    unfold matchingWidthLoss coordinatedMatchingScaleLoss
    linarith
  have hLminimum : w ≤ L.radius := by
    apply le_trans _ hLlower
    apply mul_le_mul_of_nonneg_left _ B.radius_nonneg
    apply Real.exp_le_exp.mpr
    change -(D + unbalancedReturnWidthLoss B.rank c p H Q J) ≤
      -(outerMatchingScaleLoss B.rank Q E T + 6)
    linarith
  have hsuccessorWidth : w ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank c p H Q J) := by
    rw [hSrank]
    calc
      _ = (B.radius * Real.exp (-D)) * Real.exp (-unbalancedReturnWidthLoss B.rank c p H Q J) := by
        change B.radius * Real.exp (-(D + unbalancedReturnWidthLoss B.rank c p H Q J)) = _
        rw [neg_add, Real.exp_add, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hSlower (Real.exp_nonneg _)
  have hSwide : Real.exp (-(R + D)) ≤ S.radius := by
    calc
      _ = Real.exp (-R) * Real.exp (-D) := by rw [neg_add, Real.exp_add]
      _ ≤ B.radius * Real.exp (-D) := mul_le_mul_of_nonneg_right hBwide (Real.exp_nonneg _)
      _ ≤ _ := hSlower
  refine ⟨L, S, hLfreq, hSfreq, hLreg, hSreg, hLpos, hSpos, hSwidth,
    hSwidth.trans (by linarith), ?_, ⟨hLreg, hLB, ?_, hLminimum⟩,
    hSLbase.trans hLB, ?_, hsuccessorWidth, hSwide, hSL, hmoment, hsmall, herror, hcompare⟩
  · simpa only [hSrank] using hBrank
  · rw [hLrank]
    omega
  · rw [hSrank]

end Erdos3.CellRefinement

end

end OAI

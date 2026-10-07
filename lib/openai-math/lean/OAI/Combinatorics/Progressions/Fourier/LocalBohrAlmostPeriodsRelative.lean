import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
import OAI.Combinatorics.Progressions.Estimates.CyclicRelativeChang
import OAI.Combinatorics.Progressions.Estimates.LocalBoostedAlmostPeriods

namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def characterBasis (Delta : Finset (AddChar (ZMod N) ℂ))
    (r : ℝ≥0) : Set N :=
  ofFrequencies (Delta.map AddChar.zmodAddEquiv.symm.toEmbedding) r r.coe_nonneg

@[simp] theorem rank_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).rank = Delta.card := by
  simp [characterBasis]

@[simp] theorem radius_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).radius = r := rfl

theorem norm_one_sub_le_of_mem_characterBasis
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Delta) :
    ‖1 - psi x‖ ≤ r := by
  have hmem : AddChar.zmodAddEquiv.symm psi ∈
      Delta.map AddChar.zmodAddEquiv.symm.toEmbedding :=
    Finset.mem_map.mpr ⟨psi, hpsi, rfl⟩
  have h := mem_iff.mp hx _ hmem
  simpa only [characterBasis, radius_ofFrequencies, character,
    AddEquiv.apply_symm_apply] using h

theorem norm_one_sub_le_of_mem_characterBasis_addSpan
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ}
    (hpsi : psi ∈ Delta.addSpan) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r := by
  obtain ⟨epsilon, hepsilon, hsum⟩ := Finset.mem_addSpan.mp hpsi
  rw [← hsum, AddChar.sum_apply]
  calc
    ‖1 - ∏ gamma ∈ Delta, (epsilon gamma • gamma) x‖ ≤
        ∑ gamma ∈ Delta, ‖1 - (epsilon gamma • gamma) x‖ :=
      norm_one_sub_prod_le_sum Delta _ (fun gamma _ => by simp)
    _ ≤ ∑ _gamma ∈ Delta, (r : ℝ) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      have h := norm_one_sub_le_of_mem_characterBasis hx hgamma
      rcases hepsilon gamma with hneg | hzero | hone
      · rw [hneg, neg_one_zsmul, AddChar.neg_apply, AddChar.map_neg_eq_conj]
        have heq : ‖1 - (starRingEnd ℂ) (gamma x)‖ = ‖1 - gamma x‖ := by
          simpa using (RCLike.norm_conj (1 - gamma x))
        rwa [heq]
      · simp [hzero]
      · simpa [hone] using h
    _ = (Delta.card : ℝ) * r := by simp

noncomputable def adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) : Set N :=
  (B.ndilate sigma).meet (characterBasis Delta r)

theorem rank_adjoinCharacters_le (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).rank ≤ B.rank + Delta.card := by
  simpa only [adjoinCharacters, rank_ndilate, rank_characterBasis] using
    rank_meet_le (B.ndilate sigma) (characterBasis Delta r)

@[simp] theorem radius_adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).radius = min ((sigma : ℝ) * B.radius) r := by
  simp only [adjoinCharacters, radius_meet, radius_ndilate, radius_characterBasis]

theorem adjoinCharacters_subset_ndilate (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).carrier ⊆ (B.ndilate sigma).carrier :=
  carrier_meet_subset_left _ _

theorem norm_one_sub_le_of_relative_cover
    (B : Set N) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s)
    {x : ZMod N} (hx : x ∈ adjoinCharacters B Delta sigma r)
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Q) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
      800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨z, hz, s, hs, rfl⟩ := hcover psi hpsi
  have hxB := adjoinCharacters_subset_ndilate B Delta sigma r hx
  have hxDelta : x ∈ characterBasis Delta r :=
    carrier_meet_subset_right (B.ndilate sigma) (characterBasis Delta r) hx
  have hzbound := norm_one_sub_le_of_mem_characterBasis_addSpan hxDelta hz
  have hsbound := Erdos3.norm_one_sub_le_of_mem_largeSpectrum_half hBreg hsigma hs hxB
  rw [AddChar.add_apply]
  exact (norm_one_sub_mul_of_norm_le_one (by simp)).trans (add_le_add hzbound hsbound)

theorem exists_regular_bohr_of_relative_cover
    (B : Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s) :
    ∃ R : Set N, R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
      min ((sigma : ℝ) * B.radius) r / 2 ≤ R.radius ∧
      R.radius ≤ min ((sigma : ℝ) * B.radius) r ∧
      R.carrier ⊆ (B.ndilate sigma).carrier ∧
      ∀ x ∈ R.carrier, ∀ psi ∈ Q,
        ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
          800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  let D := adjoinCharacters B Delta sigma r
  have hDpos : 0 < D.radius := by
    rw [radius_adjoinCharacters]
    exact lt_min (mul_pos (by exact_mod_cast hsigma0) hBpos) (by exact_mod_cast hr0)
  obtain ⟨R, hfreq, hRreg, hlo, hhi, hsub, _⟩ :=
    exists_controlled_regular_subdilate D hDpos 1 (by norm_num) le_rfl
  have hRD : R.carrier ⊆ D.carrier := by simpa only [ndilate_one] using hsub
  have hrank : R.rank = D.rank := congrArg Finset.card hfreq
  refine ⟨R, hRreg, hrank.le.trans (rank_adjoinCharacters_le B Delta sigma r), ?_, ?_,
    hRD.trans (adjoinCharacters_subset_ndilate B Delta sigma r), ?_⟩
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hlo
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hhi
  · intro x hx psi hpsi
    exact norm_one_sub_le_of_relative_cover B hBreg hsigma hcover (hRD hx) hpsi

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.RelativeChangSanders

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem localChangBaseScale_pos (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    0 < localChangBaseScale B X eta := by
  unfold localChangBaseScale
  positivity

theorem exists_regular_relative_spectrum_controller
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) (sigma r : ℝ≥0)
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    ∃ rho : ℝ≥0, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ), ∃ R : CyclicBohr.Set N,
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
        min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius / 2)) r / 2 ≤
          R.radius ∧
        R.radius ≤ min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius)) r ∧
        R.carrier ⊆ (C.ndilate sigma).carrier ∧
        ∀ x ∈ R.carrier, ∀ psi ∈ Chang.largeSpectrum X eta,
          ‖1 - psi x‖ ≤ localChangDimension B X eta * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨rho, C, Delta, hrho0, hrho1, hC, hCreg, hcard, hDelta, hcover⟩ :=
    exists_relativeLargeSpectrum_cover B hBpos hBreg X hX hXB eta heta
  have hCrank : C.rank = B.rank := by simp [hC]
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have ha : (0 : ℝ) < localChangBaseScale B X eta := by
    exact_mod_cast localChangBaseScale_pos B X eta
  have hCradius : C.radius = (rho : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius) := by
    simp only [hC, CyclicBohr.Set.radius_ndilate, NNReal.coe_mul, mul_assoc]
  have hCpos : 0 < C.radius := by
    rw [hCradius]
    exact mul_pos (by linarith) (mul_pos ha hBpos)
  have hClo : (localChangBaseScale B X eta : ℝ) * B.radius / 2 ≤ C.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hChi : C.radius ≤ (localChangBaseScale B X eta : ℝ) * B.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hsigmaC : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0) := by
    simpa only [hCrank] using hsigma
  obtain ⟨R, hRreg, hRrank, hRlo, hRhi, hRsub, hRphase⟩ :=
    CyclicBohr.Set.exists_regular_bohr_of_relative_cover
      C hCpos hCreg hsigma0 hr0 hsigmaC hcover
  refine ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta, hRreg,
    ?_, ?_, ?_, hRsub, ?_⟩
  · simpa only [hCrank] using hRrank
  · apply le_trans _ hRlo
    exact div_le_div_of_nonneg_right
      (min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hClo sigma.coe_nonneg))
      (by norm_num)
  · apply hRhi.trans
    exact min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hChi sigma.coe_nonneg)
  · intro x hx psi hpsi
    have hphase := hRphase x hx psi hpsi
    rw [hCrank] at hphase
    exact hphase.trans (add_le_add
      (mul_le_mul_of_nonneg_right hcard r.coe_nonneg) le_rfl)

end Erdos3.RelativeChangSanders

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem finiteFourierCoeff_finiteIndicator (A : Finset G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteIndicator A) psi =
      (∑ a ∈ A, star (psi a)) / (Fintype.card G : ℂ) := by
  simp [finiteFourierCoeff, Fintype.expect_eq_sum_div_card, finiteIndicator, ite_mul]

theorem finiteFourierCoeff_averagingKernel {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) :
    finiteFourierCoeff (averagingKernel A) psi = setFourierMultiplier A psi := by
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (A.card : ℂ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have heq : finiteFourierCoeff (averagingKernel A) psi =
      ((Fintype.card G : ℂ) / A.card) * finiteFourierCoeff (finiteIndicator A) psi := by
    unfold finiteFourierCoeff averagingKernel
    simp only [mul_assoc, Finset.mul_expect]
  rw [heq, finiteFourierCoeff_finiteIndicator, setFourierMultiplier,
    Finset.expect_eq_sum_div_card]
  field_simp

theorem sum_sq_setFourierMultiplier {A : Finset G} (hA : A.Nonempty) :
    (∑ psi : AddChar G ℂ, ‖setFourierMultiplier A psi‖ ^ 2) =
      (Fintype.card G : ℝ) / A.card := by
  simp_rw [← finiteFourierCoeff_averagingKernel hA]
  rw [finiteFourier_parseval, mean_averagingKernel_norm_sq hA]

theorem fourierL1_triple_average_sq_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ^ 2 ≤
      (M.card : ℝ) / L.card := by
  let s : ℝ := ∑ psi : AddChar G ℂ,
    ‖setFourierMultiplier L psi‖ * ‖finiteFourierCoeff (finiteIndicator M) psi‖
  have hbound : fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤ s := by
    unfold fourierL1
    apply Finset.sum_le_sum
    intro psi _
    rw [finiteFourierCoeff_finiteSetAverage, finiteFourierCoeff_finiteSetAverage]
    simp only [norm_mul]
    have hAone := norm_setFourierMultiplier_le_one hA psi
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hAone) (norm_nonneg _)
  have hnonneg : 0 ≤ fourierL1
      (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hCS : s ^ 2 ≤
      (∑ psi : AddChar G ℂ, ‖setFourierMultiplier L psi‖ ^ 2) *
        ∑ psi : AddChar G ℂ, ‖finiteFourierCoeff (finiteIndicator M) psi‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  rw [sum_sq_setFourierMultiplier hL, finiteFourier_parseval, mean_indicator_norm_sq] at hCS
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcancel : ((Fintype.card G : ℝ) / L.card) * (M.card / (Fintype.card G : ℝ)) =
      (M.card : ℝ) / L.card := by field_simp
  exact (pow_le_pow_left₀ hnonneg hbound 2).trans (hCS.trans_eq hcancel)

theorem fourierL1_triple_average_le {A L : Finset G}
    (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset G) :
    fourierL1 (finiteSetAverage L (finiteSetAverage A (finiteIndicator M))) ≤
      Real.sqrt ((M.card : ℝ) / L.card) :=
  Real.le_sqrt_of_sq_le (fourierL1_triple_average_sq_le hA hL M)

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem finiteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) :
    finiteSetAverage A (fun x => (u x : ℂ)) = fun x => (setAverageTranslate A u x : ℂ) := by
  funext x
  rw [finiteSetAverage, Finset.expect_eq_sum_div_card, setAverageTranslate]
  push_cast
  rfl

omit [NeZero N] in
theorem iteratedFiniteSetAverage_ofReal (A : Finset (ZMod N)) (u : ZMod N → ℝ) (q : ℕ) :
    iteratedFiniteSetAverage A (fun x => (u x : ℂ)) q =
      fun x => (iteratedSetAverage A u q x : ℂ) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [iteratedFiniteSetAverage, ih, finiteSetAverage_ofReal]
      rfl

omit [NeZero N] in
theorem finiteIndicator_eq_ofReal_realSetIndicator (M : Finset (ZMod N)) :
    finiteIndicator M = fun x => (realSetIndicator M x : ℂ) := by
  funext x
  by_cases hx : x ∈ M <;> simp [finiteIndicator, realSetIndicator, hx]

omit [NeZero N] in
theorem triple_average_ofReal (A L M : Finset (ZMod N)) :
    finiteSetAverage L (finiteSetAverage A (finiteIndicator M)) =
      fun x => (setAverageTranslate L (setAverageTranslate A (realSetIndicator M)) x : ℂ) := by
  rw [finiteIndicator_eq_ofReal_realSetIndicator, finiteSetAverage_ofReal, finiteSetAverage_ofReal]

theorem triple_translate_le_of_iterated_approx
    {A L X : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (hX : X.Nonempty)
    (M : Finset (ZMod N)) (q : ℕ) {delta eta theta : ℝ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : ZMod N) :
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    (∀ y, |iteratedSetAverage X u q y - u y| ≤ delta) →
    (∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) →
    |u (x - t) - u x| ≤
      2 * delta + (theta + 2 * eta ^ q) * Real.sqrt ((M.card : ℝ) / L.card) := by
  intro u happrox hphase
  let f := finiteSetAverage L (finiteSetAverage A (finiteIndicator M))
  have hf : f = fun y => (u y : ℂ) := triple_average_ofReal A L M
  have happrox' : ∀ y, ‖iteratedFiniteSetAverage X f q y - f y‖ ≤ delta := by
    intro y
    rw [hf, iteratedFiniteSetAverage_ofReal]
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using happrox y
  have h := translate_le_of_iteratedFiniteSetAverage_approx hX q f heta htheta t x happrox' hphase
  have hreal : |u (x - t) - u x| ≤ 2 * delta + (theta + 2 * eta ^ q) * fourierL1 f := by
    simpa only [hf, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  exact hreal.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (fourierL1_triple_average_le hA hL M)
      (add_nonneg htheta (mul_nonneg (by norm_num) (pow_nonneg heta q)))))

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3

open scoped BigOperators NNReal Pointwise

variable {N : ℕ} [NeZero N]

namespace RelativeChangSanders

theorem localChangBaseScale_le_one
    (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    localChangBaseScale B X eta ≤ 1 := by
  have hd : (1 : ℝ≥0) ≤ (2 * max B.rank 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * max B.rank 1 by omega)
  have hk : (1 : ℝ≥0) ≤ (2 * localChangCap B X eta + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * localChangCap B X eta + 1 by omega)
  unfold localChangBaseScale
  rw [← one_div, div_le_one (by positivity)]
  nlinarith

end RelativeChangSanders

namespace CyclicCrootSisask

open RelativeChangSanders

theorem exists_local_bohr_triple_almostPeriods
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A S L : Finset (ZMod N)} (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (hSB : S - S ⊆ B.carrier) (M : Finset (ZMod N))
    (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta)
    (sigma r : ℝ≥0) (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (X : Finset (ZMod N)) (R : CyclicBohr.Set N),
      0 ∈ X ∧ X ⊆ S - S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ X.card) ∧
      R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + localChangDimension B X (1 / 2) ∧
      min ((sigma : ℝ) * ((localChangBaseScale B X (1 / 2) : ℝ) * B.radius / 2)) r / 2 ≤
        R.radius ∧
      R.carrier ⊆ B.carrier ∧
      ∀ t ∈ R.carrier, ∀ x,
        |u (x + t) - u x| ≤ 2 * delta +
          (localChangDimension B X (1 / 2) * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma + 2 * (1 / 2 : ℝ) ^ q) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  intro m k u
  obtain ⟨T, X, z, hTS, hz, hXeq, hzero, hXS, hcount, happrox⟩ :=
    exists_local_boosted_triple_almostPeriods hA hS hL M q hq hdelta
  have hX : X.Nonempty := ⟨0, hzero⟩
  obtain ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta,
      hRreg, hRrank, hRwidth, hRupper, hRsub, hphase⟩ :=
    exists_regular_relative_spectrum_controller B hBpos hBreg X hX (hXS.trans hSB)
      (1 / 2) (by norm_num) sigma r hsigma0 hr0 hsigma
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have ha1 := localChangBaseScale_le_one B X (1 / 2)
  have hscale : sigma * (rho * localChangBaseScale B X (1 / 2)) ≤ 1 := by
    calc
      sigma * (rho * localChangBaseScale B X (1 / 2)) ≤ 1 * (1 * 1) :=
        mul_le_mul hsigma1 (mul_le_mul hrho1 ha1 (by positivity) (by norm_num))
          (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hCB : (C.ndilate sigma).carrier ⊆ B.carrier := by
    rw [hC, CyclicBohr.Set.ndilate_ndilate]
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := B) hscale
  have hcountX : (((A.card : ℝ) ^ k / 2 * S.card) /
      ((A + S).card : ℝ) ^ k ≤ X.card) := by simpa [hXeq] using hcount
  have hdim0 : 0 ≤ localChangDimension B X (1 / 2) :=
    (Nat.cast_nonneg Delta.card).trans hcard
  refine ⟨X, R, hzero, hXS, hcountX, hRreg, ?_, hRwidth, hRsub.trans hCB, ?_⟩
  · have hRrankR : (R.rank : ℝ) ≤ B.rank + Delta.card := by exact_mod_cast hRrank
    exact hRrankR.trans (add_le_add le_rfl hcard)
  · intro t ht x
    have htheta : 0 ≤ localChangDimension B X (1 / 2) * (r : ℝ) +
        800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by positivity
    have h := triple_translate_le_of_iterated_approx hA hL hX M q
      (eta := (1 / 2 : ℝ)) (by norm_num) htheta t (x + t) happrox
      (fun psi hpsi => hphase t ht psi hpsi)
    simpa only [add_sub_cancel_right, abs_sub_comm] using h

end CyclicCrootSisask
end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators NNReal Pointwise
open RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem exists_local_bohr_triple_almostPeriods_relative
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A S L : Finset (ZMod N)} (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (hSB : S ⊆ B.carrier) (M : Finset (ZMod N))
    (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta)
    (sigma r : ℝ≥0) (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T : Finset (ZMod N)) (R : CyclicBohr.Set N),
      T.Nonempty ∧ T ⊆ S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + localChangDimension B T (1 / 2) ∧
      min ((sigma : ℝ) * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2 ≤
        R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧
      ∀ t ∈ R.carrier, ∀ x,
        |u (x + t) - u x| ≤ 2 * delta +
          (localChangDimension B T (1 / 2) * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma + 2 * (1 / 2 : ℝ) ^ q) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  intro m k u
  obtain ⟨T, X, z, hTS, hz, hXeq, hzero, hXS, hcount, happrox⟩ :=
    exists_local_boosted_triple_almostPeriods hA hS hL M q hq hdelta
  have hX : X.Nonempty := ⟨0, hzero⟩
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta,
      hRreg, hRrank, hRwidth, hRupper, hRsub, hphase⟩ :=
    exists_regular_relative_spectrum_controller B hBpos hBreg T hT (hTS.trans hSB)
      (1 / 2) (by norm_num) sigma r hsigma0 hr0 hsigma
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have ha1 := localChangBaseScale_le_one B T (1 / 2)
  have hscale : sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 := by
    calc
      sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 * (1 * 1) :=
        mul_le_mul hsigma1 (mul_le_mul hrho1 ha1 (by positivity) (by norm_num))
          (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hCB : (C.ndilate sigma).carrier ⊆ B.carrier := by
    rw [hC, CyclicBohr.Set.ndilate_ndilate]
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := B) hscale
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) :=
    (Nat.cast_nonneg Delta.card).trans hcard
  refine ⟨T, R, hT, hTS, hcount, hRreg, ?_, hRwidth,
    hRupper.trans (min_le_right _ _), hRsub.trans hCB, ?_⟩
  · have hRrankR : (R.rank : ℝ) ≤ B.rank + Delta.card := by exact_mod_cast hRrank
    exact hRrankR.trans (add_le_add le_rfl hcard)
  · intro t ht x
    have htheta : 0 ≤ localChangDimension B T (1 / 2) * (r : ℝ) +
        800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by positivity
    have h := triple_translate_le_of_iterated_approx hA hL hX M q
      (eta := (1 / 2 : ℝ)) (by norm_num) htheta t (x + t) happrox
      (fun psi hpsi => hphase t ht psi (by
        rw [hXeq] at hpsi
        exact (Chang.mem_largeSpectrum_map_subRight_iff T z (1 / 2) psi).1 hpsi))
    simpa only [add_sub_cancel_right, abs_sub_comm] using h

end Erdos3.CyclicCrootSisask

end

end OAI

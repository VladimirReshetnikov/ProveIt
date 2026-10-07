import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw
import OAI.Combinatorics.Progressions.Polynomial.PrimePowerPolynomialUnchargedDensity

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem primePower_integer_polynomial_shifted_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : ∀ j, J j → ZMod (p ^ A)) :
    let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
    let Y := fun (x : V → ZMod (p ^ A)) j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
    |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 ∧
    (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z ≤
      1 + 2 / (p : ℝ) ^ 2 := by
  dsimp only
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) j i =>
    eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i)
  have hdecay (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (_hχ : χ ≠ 1) :
      ‖finiteImageCharacteristic law Y χ‖ ≤
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent s C) := by
    have hlocal := primePower_polynomial_image_characteristic_decay hs p A 0 0 hp C hC
      (fun j i => map (Int.castRingHom (ZMod (p ^ A))) (F j i))
      (fun j i => (totalDegree_map_le _ _).trans (hF j i))
      (by
        intro B hB hBA j row hunit
        rw [primePowerHomogeneousRankProbability_integerPolynomial]
        exact hrank B hB hBA j row hunit)
      r χ
    simpa only [law, Y, eval_map, Nat.zero_add, pow_zero, Nat.cast_one, Real.one_rpow,
      one_mul] using hlocal
  have hann (x : ∀ j, J j → ZMod (p ^ A)) : (p ^ A) • x = 0 := by
    ext j i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have h := finiteImage_uncharged_prime_density_rpow (taggedIntegerResidue J (p ^ A))
    (taggedIntegerResidue_surjective J (p ^ A)) hp hann law Y hP hdecay z
  have hd : |(Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z - 1| ≤
      2 / (p : ℝ) ^ 2 := by
    simpa only [← Nat.card_eq_fintype_card] using h
  exact ⟨hd, by linarith [(abs_le.mp hd).2]⟩

theorem localPrimePowerIntegerPolynomialOutput_uncharged_density
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ), 0 < B → B ≤ A → ∀ (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      integerPolynomialRankProbability p B j.val (F j) row ≤ (p : ℝ) ^ (-C * B))
    (r : V → ZMod (p ^ A)) (z : Sigma J → ZMod (p ^ A)) :
    |rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z - 1| ≤
        2 / (p : ℝ) ^ 2 ∧
    rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p ^ A)))
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z ≤
        1 + 2 / (p : ℝ) ^ 2 := by
  let law := FiniteProbabilityWeights.uniform (V → ZMod (p ^ A))
  let Y := fun (x : V → ZMod (p ^ A)) (j : Sigma J) =>
    (localPrimePowerIntegerPolynomialOutput p A 0 F r x j : ZMod (p ^ A))
  let curry := (taggedPolynomialOutputCurry J (p ^ A)).toEquiv
  have hY : (fun x => curry (Y x)) = fun x j i =>
      eval₂ (Int.castRingHom (ZMod (p ^ A))) (fun v => r v + x v) (F j i) := by
    funext x j i
    change (localPrimePowerIntegerPolynomialOutput p A 0 F r x ⟨j, i⟩ : ZMod (p ^ A)) = _
    rw [localPrimePowerIntegerPolynomialOutput_reduce]
    simp only [pow_zero, one_mul]
  have hdensity : rationalOutputDensity law
      (localPrimePowerIntegerPolynomialOutput p A 0 F r) (p ^ A) z =
      (Fintype.card (∀ j, J j → ZMod (p ^ A)) : ℝ) * finiteImageMass law
        (fun x j i => eval₂ (Int.castRingHom (ZMod (p ^ A)))
          (fun v => r v + x v) (F j i)) (curry z) := by
    change (Fintype.card (Sigma J → ZMod (p ^ A)) : ℝ) * finiteImageMass law Y z = _
    rw [Fintype.card_congr curry, ← finiteImageMass_outputEquiv law Y curry z, hY]
  rw [hdensity]
  exact primePower_integer_polynomial_shifted_uncharged_density hs p A hp C hC hP
    F hF hrank r (curry z)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem exists_goodPrimeDeletionCutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff : ℕ, 0 < cutoff ∧ 2 / (cutoff : ℝ) ≤ 1 / 2 ∧ 4 / (cutoff : ℝ) ≤ δ := by
  obtain ⟨cutoff, hcutoff⟩ := exists_nat_ge (max 4 (4 / δ))
  have hfour : (4 : ℝ) ≤ cutoff := (le_max_left _ _).trans hcutoff
  have hpos : (0 : ℝ) < cutoff := by linarith
  refine ⟨cutoff, Nat.cast_pos.mp hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hpos).mpr
    linarith
  · apply (div_le_iff₀ hpos).mpr
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hcutoff)
    linarith

theorem indexed_good_prime_product_tail {L : Type*}
    (p : L → ℕ) (hp : Function.Injective p) (S : Finset L) (f : L → ℝ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    (hlarge : ∀ l ∈ S, cutoff < p l) (hnonneg : ∀ l ∈ S, 0 ≤ f l)
    (herror : ∀ l ∈ S, |f l - 1| ≤ 2 / (p l : ℝ) ^ 2) :
    |(∏ l ∈ S, f l) - 1| ≤ 4 / (cutoff : ℝ) := by
  have h := finite_positive_product_tail (S.image p) (Function.extend p f (fun _ => 1))
    hcutoff (by norm_num : (0 : ℝ) ≤ 2)
    (by rintro q hq; obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq; exact hlarge l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using hnonneg l hl)
    (by
      rintro q hq
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hq
      simpa only [hp.extend_apply] using herror l hl) hsmall
  simpa only [Finset.prod_image hp.injOn, hp.extend_apply, show (2 : ℝ) * 2 = 4 by norm_num] using h

theorem crt_integer_polynomial_inactive_good_prime_deletion
    {L V I Z : Type*} [Fintype L] [Fintype V] [Fintype I] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p A bad e : L → ℕ) [∀ l, NeZero (p l)]
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : ((Fintype.card (Sigma J) + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s C)
    (F : I → ∀ j, J j → MvPolynomial V ℤ)
    (hF : ∀ i j a, (F i j a).totalDegree ≤ j.val + 1)
    (hrank : ∀ i l B, bad l < B → B ≤ A l → ∀ j
      (row : J j → ZMod (p l ^ B)), (∃ a, IsUnit (row a)) →
      integerPolynomialRankProbability (p l) B j.val (F i j) row ≤ (p l : ℝ) ^ (-C * B))
    (r : I → ∀ l, V → ZMod (p l ^ A l))
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (retained : Finset L)
    (hretained : ∀ l, l ∉ retained → cutoff < p l ∧ bad l = 0 ∧ e l = 0)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma J → ZMod (∏ l, p l ^ A l)) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    let full := rationalInactiveForecast inactive
      (fun _ => crtPrimePowerPolynomialLaw (V := V) p A) gridPoint
      (fun i => crtPrimePowerIntegerPolynomialOutput p A e
        (primePower_crt_coprime p A hp hinj) (F i) (r i))
      (∏ l, p l ^ A l) gridVolume z β
    let truncated := gridVolume * inactive.fiberMean gridPoint z (fun i =>
      ∏ l ∈ retained,
        rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
          (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
          (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
            (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j)))
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  dsimp only
  rw [crt_integer_polynomial_rational_inactive_density_product]
  let factor (i : I) (l : L) :=
    rationalOutputDensity (FiniteProbabilityWeights.uniform (V → ZMod (p l ^ A l)))
      (localPrimePowerIntegerPolynomialOutput (p l) (A l) (e l) (F i) (r i l)) (p l ^ A l)
      (fun j => ZMod.castHom (Finset.dvd_prod_of_mem (fun l => p l ^ A l)
        (Finset.mem_univ l)) (ZMod (p l ^ A l)) (β j))
  have hnonneg (i : I) (l : L) : 0 ≤ factor i l := rationalOutputDensity_nonneg _ _ _ _
  apply inactive.fiberMean_prod_bounds_of_omitted_prod_sub_one_le gridPoint z
    gridVolume δ hvolume hδ retained factor hnonneg
  intro i
  apply (indexed_good_prime_product_tail p hinj (Finset.univ \ retained) (factor i)
    cutoff hcutoff hsmall ?_ (fun l _ => hnonneg i l) ?_).trans haccuracy
  · intro l hl
    exact (hretained l (Finset.mem_sdiff.mp hl).2).1
  · intro l hl
    obtain ⟨_, hbad, he⟩ := hretained l (Finset.mem_sdiff.mp hl).2
    dsimp only [factor]
    rw [he]
    apply (localPrimePowerIntegerPolynomialOutput_uncharged_density hs (p l) (A l)
      (hp l) C hC hP (F i) (hF i) ?_ (r i l) _).1
    intro B hB hBA j row hunit
    exact hrank i l B (by simpa only [hbad] using hB) hBA j row hunit

end Erdos3

end

end OAI

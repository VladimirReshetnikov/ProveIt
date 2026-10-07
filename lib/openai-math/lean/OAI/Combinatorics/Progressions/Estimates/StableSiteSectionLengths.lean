import OAI.Combinatorics.Progressions.Polynomial.StableSiteLowDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_uniform_sections {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ S : Finset {i // i ∉ K}, S.card ≤ j → ∀ x,
      productConditionalMean ν S (density (fun z => (h z).re)) x ≤
        level * productConditionalMean ν S (density (fun z => (g z).re)) x + level * τ ∧
      v - τ ≤ productConditionalMean ν S (density (fun z => (g z).re)) x ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          3 * Real.exp (L + T) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          3 * Real.exp (L + T) := by
  dsimp only
  have hga : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have hha : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hh z hz).1]
    exact (hh z hz).2
  have hmeans := stable_site_reference_mean_bounds hstable hupper hM hpair hcop u hga hha
    hlevel.le hτ.le hδ hinc hη hητ hηlevel herror
  obtain ⟨hgb, hhb⟩ := stable_site_normalized_marginals hstable hupper hM hpair hcop u hg hha
    hlevel hτ (by linarith) (by nlinarith) hη (by linarith) (by nlinarith) herror
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  obtain ⟨hgs, hhs, hgcap, hhcap, hlogcap⟩ := site_normalization_caps hv hτ hlevel hL hT hlower hτinv
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have hcapP : Real.exp (L + T) ≤ Real.exp P := Real.exp_le_exp.mpr (by linarith)
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hbudget := approxMoment_small_of_exponential (Fintype.card {i // i ∉ K}) (j + r) moment
    (Real.exp (L + T)) P hP (Real.exp_pos _).le houtside hcapP hrP hqP hηsmall
  have hclow := ProductMarginalsClose.mono _ hclose (le_max_left _ _)
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  intro S hS x
  have hSj : S.card ≤ j + r := by omega
  have hm := hmeans S hSj x
  refine ⟨hm.1, hm.2, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact residuePrimeDensity_scaled_section_low_degree lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
      hhs (Real.exp_pos _).le hhcap hmoment heven S hSj (by omega) x hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hclow hhb
  · intro k hk
    exact residuePrimeDensity_scaled_section_low_degree lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
      hgs (Real.exp_pos _).le hgcap hmoment heven S hSj (by omega) x hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hclow hgb
  · exact residuePrimeDensity_scaled_section_norm lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
      hhs hhcap S x hη0 hη.le _ (fun A hA => (mem_lowDegreeCoordinateSets _ b A).mp hA)
      (ProductMarginalsClose.mono _ hclose (by omega)) hgram
  · exact residuePrimeDensity_scaled_section_norm lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
      hgs hgcap S x hη0 hη.le _ (fun A hA => (mem_lowDegreeCoordinateSets _ b A).mp hA)
      (ProductMarginalsClose.mono _ hclose (by omega)) hgram

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_uniform_sections_of_lengths {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (modLog dimLog errorLog : ℝ) (hmodLog : 0 ≤ modLog) (herror : Real.exp (-errorLog) ≤ η)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog) (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hlength : ∀ k, Real.exp (modLog * (max ((j + r) * (moment + 1)) (2 * b + j) : ℕ) +
      errorLog + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ S : Finset {i // i ∉ K}, S.card ≤ j → ∀ x,
      productConditionalMean ν S (density (fun z => (h z).re)) x ≤
        level * productConditionalMean ν S (density (fun z => (g z).re)) x + level * τ ∧
      v - τ ≤ productConditionalMean ν S (density (fun z => (g z).re)) x ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          (16 * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (4 * level * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (h z).re)) y)) ≤
          3 * Real.exp (L + T) ∧
      Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets {i // i ∉ K} b)
        (fun y => (2 * (v + τ))⁻¹ * productSectionAverage ν S S x (density (fun z => (g z).re)) y)) ≤
          3 * Real.exp (L + T) := by
  have hQ : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i : {i // i ∉ K}, (M.lcm (∏ k ∈ K, q k)).Coprime (q i.val) :=
    fun i => selectedCombined_coprime_outside q hpair M K hcop i.val i.property
  have hpair' : Pairwise (fun i k : {i // i ∉ K} => (q i.val).Coprime (q k.val)) :=
    fun i k hik => hpair (fun heq => hik (Subtype.ext heq))
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hmods := fun i : {i // i ∉ K} => hmoduli i.val i.property
  have hbase := residuePrimeDensity_close_of_lengths lo N (M.lcm (∏ i ∈ K, q i))
    (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair'
    (max ((j + r) * (moment + 1)) (2 * b + j)) modLog dimLog errorLog η
    hmodLog hη.le herror hmods hdim hlength
  have hrank : j + r ≤ max ((j + r) * (moment + 1)) (2 * b + j) := by
    have hmul : j + r ≤ (j + r) * (moment + 1) := by
      calc
        j + r = (j + r) * 1 := (Nat.mul_one _).symm
        _ ≤ (j + r) * (moment + 1) := Nat.mul_le_mul_left _ (by omega)
    exact hmul.trans (le_max_left _ _)
  have herr (S : Finset {i // i ∉ K}) (hS : S.card ≤ j + r) :=
    (primeCoordinate_error_le_exp (fun i : {i // i ∉ K} => q i.val)
      (fun k => residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val))
      (max ((j + r) * (moment + 1)) (2 * b + j)) modLog dimLog errorLog hmodLog hmods hdim hlength
      S (hS.trans hrank)).trans herror
  exact stable_site_uniform_sections hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc
    hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall
    herr hbase hgram

end Erdos3

end

end OAI

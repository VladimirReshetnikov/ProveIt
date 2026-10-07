import OAI.Combinatorics.Progressions.Probability.DensityNormalizationScales
import OAI.Combinatorics.Progressions.Probability.StableSiteDensityBounds

namespace OAI

section

namespace Erdos3

theorem approxMomentEnvelope_pow_le_exp (N r q : ℕ) (M P : ℝ)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M) (hN : (N : ℝ) ≤ Real.exp P) (hM : M ≤ Real.exp P)
    (hr : (r : ℝ) ≤ P) (hq : (q : ℝ) ≤ P + 2) :
    approxMomentEnvelope N r M ^ q ≤ Real.exp ((P + 3) ^ 3) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hone : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hadd (x : ℝ) (hx : x ≤ Real.exp P) : 2 + x ≤ Real.exp (P + 2) := by
    calc
      _ ≤ 3 * Real.exp P := by linarith
      _ ≤ Real.exp 2 * Real.exp P := mul_le_mul_of_nonneg_right hthree (Real.exp_pos P).le
      _ = _ := by rw [mul_comm, ← Real.exp_add]
  have henv : approxMomentEnvelope N r M ≤ Real.exp ((P + 3) ^ 2) := by
    calc
      _ ≤ Real.exp 1 ^ (r + 1) * Real.exp (P + 2) ^ r * Real.exp (P + 2) := by
        unfold approxMomentEnvelope
        gcongr
        · exact hadd N hN
        · exact hadd M hM
      _ = Real.exp (((r : ℝ) + 1) * (P + 3)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp ((P + 3) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right (show (r : ℝ) + 1 ≤ P + 3 by linarith)
          (show 0 ≤ P + 3 by linarith)]
  calc
    _ ≤ Real.exp ((P + 3) ^ 2) ^ q :=
      pow_le_pow_left₀ ((zero_le_one.trans (approxMomentEnvelope_one_le N r hM0))) henv q
    _ = Real.exp ((q : ℝ) * (P + 3) ^ 2) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((P + 3) ^ 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (show (q : ℝ) ≤ P + 3 by linarith) (sq_nonneg (P + 3))]

theorem approxMoment_small_of_exponential (N r q : ℕ) (M P : ℝ)
    (hP : 0 ≤ P) (hM0 : 0 ≤ M) (hN : (N : ℝ) ≤ Real.exp P) (hM : M ≤ Real.exp P)
    (hr : (r : ℝ) ≤ P) (hq : (q : ℝ) ≤ P + 2) {η : ℝ}
    (hη : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3))) :
    η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (N : ℝ)) ^ r * (2 + M)) ^ q)⁻¹ := by
  have hpos : 0 < approxMomentEnvelope N r M ^ q :=
    pow_pos (zero_lt_one.trans_le (approxMomentEnvelope_one_le N r hM0)) q
  have hbound := approxMomentEnvelope_pow_le_exp N r q M P hP hM0 hN hM hr hq
  have hinv : Real.exp (-((P + 3) ^ 3)) ≤ (approxMomentEnvelope N r M ^ q)⁻¹ := by
    simpa only [one_div, Real.exp_neg] using one_div_le_one_div_of_le hpos hbound
  exact hη.trans (mul_le_mul_of_nonneg_left hinv (by norm_num))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stable_site_low_degree_of_lengths {ι σ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {r moment : ℕ} {level ε δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q r level ε δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ) (hε : ε ≤ level * τ)
    (hη : η < 1) (hητ : η ≤ τ) (hηlevel : η ≤ level * τ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : (r : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment)
    (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (B C D : ℝ) (hB : 0 ≤ B) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp B) (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ j, Real.exp (B * (r * (moment + 1) : ℕ) + D + C + 1) ≤
      (residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val) : ℝ)) :
    let v := (residuePrimeCoordinateMean g lo N M a q K base).re
    let density := fun f scale => normalizedResiduePrimeDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f scale
    let μ := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    ∀ k : ℕ, k ≤ r →
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (density (fun z => (g z).re) (2 * (v + τ)))) ≤ (16 * (P + 2)) ^ (2 * k) ∧
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (density (fun z => (h z).re) (4 * level * (v + τ)))) ≤ (16 * (P + 2)) ^ (2 * k) := by
  dsimp only
  have hQ : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i : {i // i ∉ K}, (M.lcm (∏ j ∈ K, q j)).Coprime (q i.val) :=
    fun i => selectedCombined_coprime_outside q hpair M K hcop i.val i.property
  have hpair' : Pairwise (fun i j : {i // i ∉ K} => (q i.val).Coprime (q j.val)) :=
    fun i j hij => hpair (fun heq => hij (Subtype.ext heq))
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hmods := fun i : {i // i ∉ K} => hmoduli i.val i.property
  have hbase := residuePrimeDensity_close_of_lengths lo N (M.lcm (∏ i ∈ K, q i))
    (fun j => (u.val j).val) hne (fun i : {i // i ∉ K} => q i.val) hQ hQcop hpair'
    (r * (moment + 1)) B C D η hB hη.le herror hmods hdim hlength
  have hrank : r ≤ r * (moment + 1) := by
    calc
      r = r * 1 := (Nat.mul_one r).symm
      _ ≤ r * (moment + 1) := Nat.mul_le_mul_left r (by omega)
  have herr (S : Finset {i // i ∉ K}) (hS : S.card ≤ r) :=
    (primeCoordinate_error_le_exp (fun i : {i // i ∉ K} => q i.val)
      (fun j => residueIndexLength (lo j) (lo j + N j) (M.lcm (∏ i ∈ K, q i)) ((u.val j).val))
      (r * (moment + 1)) B C D hB hmods hdim hlength S (hS.trans hrank)).trans herror
  have hha : ∀ z ∈ translatedIntegerBox lo N, |(h z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hh z hz).1]
    exact (hh z hz).2
  obtain ⟨hgb, hhb⟩ := stable_site_normalized_marginals hstable hupper hM hpair hcop u hg hha
    hlevel hτ hδ hε hη hητ hηlevel herr
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  obtain ⟨hgs, hhs, hgcap, hhcap, hlogcap⟩ := site_normalization_caps hv hτ hlevel hL hT hlower hτinv
  have hP : 0 ≤ P := (Nat.cast_nonneg r).trans hrP
  have hcapP : Real.exp (L + T) ≤ Real.exp P := Real.exp_le_exp.mpr (by linarith)
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hbudget := approxMoment_small_of_exponential (Fintype.card {i // i ∉ K}) r moment
    (Real.exp (L + T)) P hP (Real.exp_pos _).le houtside hcapP hrP hqP hηsmall
  have hη0 : 0 ≤ η := (Real.exp_pos (-D)).le.trans herror
  intro k hk
  constructor
  · exact normalizedResiduePrimeDensity_low_degree lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
      _ hgs (Real.exp_pos _).le hgcap hk hmoment heven hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hbase hgb
  · exact normalizedResiduePrimeDensity_low_degree lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
      _ hhs (Real.exp_pos _).le hhcap hk hmoment heven hη0 hrP (hlogcap.trans hlog)
      hPq hqP hbudget hbase hhb

end Erdos3

end

end OAI

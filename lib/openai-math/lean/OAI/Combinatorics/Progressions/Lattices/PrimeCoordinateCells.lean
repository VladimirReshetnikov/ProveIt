/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
import OAI.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds
import OAI.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => prime i ∣ M)

@[simp] theorem mem_periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) (i : ι) :
    i ∈ periodPrimeCoordinates prime M ↔ prime i ∣ M := by
  classical
  simp [periodPrimeCoordinates]

theorem periodPrimeCoordinates_card_pow_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) : 2 ^ (periodPrimeCoordinates prime M).card ≤ M := by
  classical
  let A := periodPrimeCoordinates prime M
  have hsub : A.image prime ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime i, (mem_periodPrimeCoordinates prime M i).mp hi, hM.ne'⟩
  have hcard : A.card ≤ M.primeFactors.card := by
    rw [← Finset.card_image_of_injective A hinj]
    exact Finset.card_le_card hsub
  calc
    2 ^ A.card ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

theorem periodPrimeCoordinates_card_log_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) :
    (periodPrimeCoordinates prime M).card * Real.log 2 ≤ Real.log M := by
  have hpow : (2 : ℝ) ^ (periodPrimeCoordinates prime M).card ≤ M := by
    exact_mod_cast periodPrimeCoordinates_card_pow_le prime hprime hinj hM
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow

theorem periodPrimeCoordinates_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) {B : ℝ} (hMB : (M : ℝ) ≤ Real.exp B) :
    ((periodPrimeCoordinates prime M).card : ℝ) ≤ 2 * B := by
  have h := (periodPrimeCoordinates_card_log_le prime hprime hinj hM).trans
    ((Real.log_le_iff_le_exp (by exact_mod_cast hM)).mpr hMB)
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    linarith
  have hc : (0 : ℝ) ≤ (periodPrimeCoordinates prime M).card := Nat.cast_nonneg _
  nlinarith

theorem periodPrimeCoordinates_pending_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (M : ℕ) (J : Finset ι)
    (hJ : Disjoint J (periodPrimeCoordinates prime M)) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) M := by
  classical
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.Coprime.pow_left
  apply (hprime i).coprime_iff_not_dvd.mpr
  intro hd
  exact Finset.disjoint_left.mp hJ hi ((mem_periodPrimeCoordinates prime M i).mpr hd)

theorem periodPrimeCoordinates_pending_mul_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (M d : ℕ) (J : Finset ι)
    (hJ : Disjoint J (periodPrimeCoordinates prime M))
    (hd : Nat.Coprime (∏ i ∈ J, prime i ^ power i) d) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) (M * d) :=
  (periodPrimeCoordinates_pending_coprime prime power hprime M J hJ).mul_right hd

theorem disjoint_prime_power_products_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (A B : Finset ι) (hAB : Disjoint A B) :
    Nat.Coprime (∏ i ∈ A, prime i ^ power i) (∏ j ∈ B, prime j ^ power j) := by
  classical
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  apply Nat.coprime_prod_right_iff.mpr
  intro j hj
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  have hij := hinj heq
  exact Finset.disjoint_left.mp hAB hi (hij.symm ▸ hj)

theorem periodPrimeCoordinates_unfixed_coprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (K J : Finset ι)
    (hJ : Disjoint J (K ∪ periodPrimeCoordinates prime M)) :
    Nat.Coprime (∏ i ∈ J, prime i ^ power i) ((∏ i ∈ K, prime i ^ power i) * M) := by
  have hJK : Disjoint J K := hJ.mono_right Finset.subset_union_left
  have hJM : Disjoint J (periodPrimeCoordinates prime M) := hJ.mono_right Finset.subset_union_right
  exact (disjoint_prime_power_products_coprime prime power hprime hinj J K hJK).mul_right
    (periodPrimeCoordinates_pending_coprime prime power hprime M J hJM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedPrimePowers_pairwise_coprime {ι : Type*}
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  exact hij (hinj heq)

theorem modEq_selected_prod_iff {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (a b : ℤ) :
    a ≡ b [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] ↔ ∀ i ∈ I, a ≡ b [ZMOD (q i : ℤ)] := by
  induction I using Finset.induction_on with
  | empty => simp [Int.ModEq]
  | @insert i I hi ih =>
    have hc : (q i).Coprime (∏ j ∈ I, q j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply hcop
      intro heq
      subst j
      exact hi hj
    have hci : Int.natAbs (q i : ℤ) |>.Coprime (Int.natAbs ((∏ j ∈ I, q j : ℕ) : ℤ)) := by
      simpa only [Int.natAbs_natCast] using hc
    rw [Finset.prod_insert hi, Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hci, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem periodPrimeCoordinates_modulus_dvd_product {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (m : ℕ)
    (hm : m ∣ ∏ i, prime i ^ power i) :
    m ∣ ∏ i ∈ periodPrimeCoordinates prime m, prime i ^ power i := by
  let I := periodPrimeCoordinates prime m
  have hc := (periodPrimeCoordinates_pending_coprime prime power hprime m Iᶜ
    (Finset.disjoint_left.mpr (fun _ hi hI => (Finset.mem_compl.mp hi) hI))).symm
  apply hc.dvd_of_dvd_mul_right
  rw [Finset.prod_mul_prod_compl]
  exact hm

theorem periodPrimeCoordinates_card_le_of_le_pow {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {m b : ℕ} (hm : 0 < m) (hmb : m ≤ 2 ^ b) :
    (periodPrimeCoordinates prime m).card ≤ b := by
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((periodPrimeCoordinates_card_pow_le prime hprime hinj hm).trans hmb)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem initialResiduePrimeMask_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (hM : 0 < M) (p : ℝ) (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hqp : ∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p)
    (mandatory : Finset ι) (hmandatory : (mandatory.card : ℝ) ≤ p) :
    let K := mandatory ∪ periodPrimeCoordinates prime M
    (K.card : ℝ) ≤ 3 * p ∧
      ((M.lcm (∏ i ∈ K, prime i ^ power i) : ℕ) : ℝ) ≤ Real.exp (p + 3 * p ^ 2) := by
  dsimp only
  let K := mandatory ∪ periodPrimeCoordinates prime M
  have hperiod := periodPrimeCoordinates_card_le prime hprime hinj hM hMp
  have hcardNat := Finset.card_union_le mandatory (periodPrimeCoordinates prime M)
  have hcard : (K.card : ℝ) ≤ 3 * p := by
    have hcardReal : (K.card : ℝ) ≤ mandatory.card + (periodPrimeCoordinates prime M).card := by
      exact_mod_cast hcardNat
    linarith
  refine ⟨hcard, ?_⟩
  have hprod : ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) ≤ Real.exp (3 * p ^ 2) := by
    rw [Nat.cast_prod]
    calc
      (∏ i ∈ K, ((prime i ^ power i : ℕ) : ℝ)) ≤ ∏ _i ∈ K, Real.exp p :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hqp i)
      _ = Real.exp ((K.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
      _ ≤ Real.exp (3 * p ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hcard hp]
  have hprodpos : 0 < ∏ i ∈ K, prime i ^ power i :=
    Finset.prod_pos (fun i _ => pow_pos (hprime i).pos _)
  have hlcm : ((M.lcm (∏ i ∈ K, prime i ^ power i) : ℕ) : ℝ) ≤
      (M : ℝ) * ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hM hprodpos) (Nat.lcm_dvd_mul M _)
  calc
    _ ≤ (M : ℝ) * ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) := hlcm
    _ ≤ Real.exp p * Real.exp (3 * p ^ 2) := mul_le_mul hMp hprod (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + 3 * p ^ 2) := (Real.exp_add _ _).symm

theorem initialResidueCombined_coprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (K : Finset ι) (hcovered : periodPrimeCoordinates prime M ⊆ K)
    (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, prime i ^ power i)).Coprime (prime j ^ power j) := by
  have hM : M.Coprime (prime j ^ power j) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime j).coprime_iff_not_dvd.mpr
    intro hd
    exact hj (hcovered ((mem_periodPrimeCoordinates prime M j).mpr hd))
  have hK : (∏ i ∈ K, prime i ^ power i).Coprime (prime j ^ power j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    apply selectedPrimePowers_pairwise_coprime prime power hprime hinj
    intro heq
    exact hj (heq ▸ hi)
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul M _) (Nat.coprime_mul_iff_left.mpr ⟨hM, hK⟩)

end Erdos3

end

section

namespace Erdos3

noncomputable def affineComparisonPrimeThreshold (ξ P : ℝ) : ℝ :=
  (P + 2) ^ (4 + CyclicCrootSisask.spectralIterations ξ 18)

noncomputable def affineComparisonContraction (ξ P : ℝ) : ℝ :=
  (affineComparisonPrimeThreshold ξ P)⁻¹

theorem affineComparisonContraction_bounds {ξ P : ℝ} (hξ : 0 < ξ) (hP : 0 ≤ P) :
    0 < affineComparisonContraction ξ P ∧ affineComparisonContraction ξ P ≤ 1 / 2 ∧
    affineComparisonContraction ξ P * (8 * (1 + 2) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16 := by
  have ht : 2 ≤ P + 2 := by linarith
  have hthreshold : 2 ≤ affineComparisonPrimeThreshold ξ P := by
    unfold affineComparisonPrimeThreshold
    calc
      2 ≤ P + 2 := ht
      _ = (P + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hp : 0 < affineComparisonPrimeThreshold ξ P := by linarith
  refine ⟨inv_pos.mpr hp, ?_, ?_⟩
  · simpa only [affineComparisonContraction, one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hthreshold
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hc : (147456 : ℝ) ≤ Real.exp 18 := by
      calc
        147456 ≤ (2 : ℝ) ^ 18 := by norm_num
        _ ≤ (Real.exp 1) ^ 18 := pow_le_pow_left₀ (by norm_num) htwo 18
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    exact low_level_after_power_cutoff (d := 4) hξ ht (by norm_num) hc
      (by ring_nf; exact le_rfl) le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P)

theorem mem_affineMandatoryPrimes {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (i : ι) :
    i ∈ affineMandatoryPrimes prime ξ P ↔ (prime i : ℝ) ≤ affineComparisonPrimeThreshold ξ P := by
  simp only [affineMandatoryPrimes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem affineMandatoryPrimes_outside_inverse {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) {ξ P : ℝ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineMandatoryPrimes prime ξ P ⊆ K) (i : ι) (hi : i ∉ K) :
    (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  have ht : 0 < affineComparisonPrimeThreshold ξ P := by unfold affineComparisonPrimeThreshold; positivity
  have hp : affineComparisonPrimeThreshold ξ P ≤ (prime i : ℝ) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hi (hK ((mem_affineMandatoryPrimes prime ξ P i).mpr h))
  simpa only [affineComparisonContraction, one_div] using one_div_le_one_div_of_le ht hp

theorem affineMandatoryPrimes_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (ξ P : ℝ) (hP : 0 ≤ P) :
    ((affineMandatoryPrimes prime ξ P).card : ℝ) ≤ affineComparisonPrimeThreshold ξ P + 2 := by
  let n := ⌈affineComparisonPrimeThreshold ξ P⌉₊
  have hsub : (affineMandatoryPrimes prime ξ P).image prime ⊆ Finset.range (n + 1) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hle : (prime i : ℝ) ≤ (n : ℝ) :=
      ((mem_affineMandatoryPrimes prime ξ P i).mp hi).trans (Nat.le_ceil _)
    have hn : prime i ≤ n := by exact_mod_cast hle
    exact Finset.mem_range.mpr (by omega)
  have hc : (affineMandatoryPrimes prime ξ P).card ≤ n + 1 := by
    calc
      _ = ((affineMandatoryPrimes prime ξ P).image prime).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card hsub
      _ = _ := Finset.card_range _
  have ht : 0 ≤ affineComparisonPrimeThreshold ξ P := by unfold affineComparisonPrimeThreshold; positivity
  have hn := Nat.ceil_lt_add_one ht
  have hc' : ((affineMandatoryPrimes prime ξ P).card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hc
  change (n : ℝ) < affineComparisonPrimeThreshold ξ P + 1 at hn
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineInitialPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) : Finset ι :=
  (affineMandatoryPrimes prime ξ P ∪ periodPrimeCoordinates prime sourceM) ∪
    periodPrimeCoordinates prime siteM

theorem affineInitialPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM : ℕ) :
    affineMandatoryPrimes prime ξ P ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime sourceM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM ∧
    periodPrimeCoordinates prime siteM ⊆ affineInitialPrimeMask prime ξ P sourceM siteM := by
  exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩

theorem affineInitialPrimeMask_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {ξ P sourceLog siteLog : ℝ} {sourceM siteM : ℕ}
    (hP : 0 ≤ P) (hsourceM : 0 < sourceM) (hsiteM : 0 < siteM)
    (hsource : (sourceM : ℝ) ≤ Real.exp sourceLog) (hsite : (siteM : ℝ) ≤ Real.exp siteLog) :
    ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) ≤
      affineComparisonPrimeThreshold ξ P + 2 + 2 * sourceLog + 2 * siteLog := by
  have hmandatory := affineMandatoryPrimes_card_le prime hinj ξ P hP
  have hs := periodPrimeCoordinates_card_le prime hprime hinj hsourceM hsource
  have ht := periodPrimeCoordinates_card_le prime hprime hinj hsiteM hsite
  have hcard : (affineInitialPrimeMask prime ξ P sourceM siteM).card ≤
      (affineMandatoryPrimes prime ξ P).card + (periodPrimeCoordinates prime sourceM).card +
        (periodPrimeCoordinates prime siteM).card := by
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcard' : ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) ≤
      ((affineMandatoryPrimes prime ξ P).card : ℝ) + ((periodPrimeCoordinates prime sourceM).card : ℝ) +
        ((periodPrimeCoordinates prime siteM).card : ℝ) := by exact_mod_cast hcard
  linarith

theorem affineInitialPrimeMask_outside_coprime {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    {ξ P : ℝ} {sourceM siteM : ℕ} (K : Finset ι)
    (hK : affineInitialPrimeMask prime ξ P sourceM siteM ⊆ K)
    (i : ι) (hi : i ∉ K) :
    sourceM.Coprime (prime i ^ power i) ∧ siteM.Coprime (prime i ^ power i) := by
  have hcontains := affineInitialPrimeMask_contains prime ξ P sourceM siteM
  have hcop (M : ℕ) (hM : periodPrimeCoordinates prime M ⊆ K) : M.Coprime (prime i ^ power i) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime i).coprime_iff_not_dvd.mpr
    intro hd
    exact hi (hM ((mem_periodPrimeCoordinates prime M i).mpr hd))
  exact ⟨hcop sourceM (hcontains.2.1.trans hK), hcop siteM (hcontains.2.2.trans hK)⟩

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def affineSamplerPrimeMask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) : Finset ι :=
  affineInitialPrimeMask prime ξ P sourceM siteM ∪ periodPrimeCoordinates prime D

theorem affineSamplerPrimeMask_contains {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (ξ P : ℝ) (sourceM siteM D : ℕ) :
    affineInitialPrimeMask prime ξ P sourceM siteM ⊆
      affineSamplerPrimeMask prime ξ P sourceM siteM D ∧
    periodPrimeCoordinates prime D ⊆ affineSamplerPrimeMask prime ξ P sourceM siteM D :=
  ⟨Finset.subset_union_left, Finset.subset_union_right⟩

theorem affineSamplerPrimeMask_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {ξ P sourceLog siteLog parameterLog : ℝ} {sourceM siteM D : ℕ}
    (hP : 0 ≤ P) (hsourceM : 0 < sourceM) (hsiteM : 0 < siteM) (hD : 0 < D)
    (hsource : (sourceM : ℝ) ≤ Real.exp sourceLog) (hsite : (siteM : ℝ) ≤ Real.exp siteLog)
    (hparameter : (D : ℝ) ≤ Real.exp parameterLog) :
    ((affineSamplerPrimeMask prime ξ P sourceM siteM D).card : ℝ) ≤
      affineComparisonPrimeThreshold ξ P + 2 + 2 * sourceLog + 2 * siteLog + 2 * parameterLog := by
  have hbase := affineInitialPrimeMask_card_le (ξ := ξ) prime hprime hinj hP hsourceM hsiteM hsource hsite
  have hp := periodPrimeCoordinates_card_le prime hprime hinj hD hparameter
  have hcard : ((affineSamplerPrimeMask prime ξ P sourceM siteM D).card : ℝ) ≤
      ((affineInitialPrimeMask prime ξ P sourceM siteM).card : ℝ) +
        ((periodPrimeCoordinates prime D).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (affineInitialPrimeMask prime ξ P sourceM siteM) (periodPrimeCoordinates prime D)
  linarith

theorem affineSamplerPrimeMask_outside {ι : Type*} [Fintype ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    {ξ P : ℝ} {sourceM siteM D : ℕ} (hP : 0 ≤ P) (K : Finset ι)
    (hK : affineSamplerPrimeMask prime ξ P sourceM siteM D ⊆ K)
    (i : ι) (hi : i ∉ K) :
    sourceM.Coprime (prime i ^ power i) ∧ siteM.Coprime (prime i ^ power i) ∧
    D.Coprime (prime i ^ power i) ∧ (prime i : ℝ)⁻¹ ≤ affineComparisonContraction ξ P := by
  have hcontains := affineSamplerPrimeMask_contains prime ξ P sourceM siteM D
  have hbase := affineInitialPrimeMask_outside_coprime prime power hprime K (hcontains.1.trans hK) i hi
  have hD : D.Coprime (prime i ^ power i) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime i).coprime_iff_not_dvd.mpr
    intro hd
    exact hi (hK (hcontains.2 ((mem_periodPrimeCoordinates prime D i).mpr hd)))
  have hmandatory := (affineInitialPrimeMask_contains prime ξ P sourceM siteM).1.trans (hcontains.1.trans hK)
  exact ⟨hbase.1, hbase.2, hD, affineMandatoryPrimes_outside_inverse prime hP K hmandatory i hi⟩

end Erdos3

end

section

namespace Erdos3

noncomputable def affineReferencePower (epsilon : ℝ) : ℕ :=
  4 + CyclicCrootSisask.spectralIterations (epsilon / (2 + epsilon)) 18

noncomputable def affineReferenceInput (epsilon U : ℝ) : ℝ :=
  (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon +
    affinePrimitiveLogBudget U + 3 * U + 10

theorem affineReferenceInput_bounds (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    2 ≤ affineReferenceInput epsilon U ∧ U ≤ affineReferenceInput epsilon U ∧
      affinePrimitiveLogBudget U ≤ affineReferenceInput epsilon U := by
  have hpow : 0 ≤ (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon :=
    pow_nonneg (by unfold affinePrimitiveLogBudget; positivity) _
  unfold affineReferenceInput affinePrimitiveLogBudget at *
  constructor
  · linarith
  constructor <;> linarith

theorem affineReferenceInput_le_envelope (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    affineReferenceInput epsilon U ≤ (20 * (U + 3)) ^ (affineReferencePower epsilon + 1) := by
  let B := 20 * (U + 3)
  have hB : 2 ≤ B := by dsimp only [B]; linarith
  have hk : 1 ≤ affineReferencePower epsilon := by unfold affineReferencePower; omega
  have hp := pow_le_pow_left₀ (by unfold affinePrimitiveLogBudget; positivity :
      0 ≤ affinePrimitiveLogBudget U + 2)
    (by dsimp only [B]; unfold affinePrimitiveLogBudget; linarith : affinePrimitiveLogBudget U + 2 ≤ B)
    (affineReferencePower epsilon)
  have hBpow : B ≤ B ^ affineReferencePower epsilon := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ B) hk
  have htail : affinePrimitiveLogBudget U + 3 * U + 10 ≤ B := by
    dsimp only [B]; unfold affinePrimitiveLogBudget; linarith
  have hn : 0 ≤ B ^ affineReferencePower epsilon := pow_nonneg (by linarith) _
  change _ ≤ B ^ (affineReferencePower epsilon + 1)
  rw [pow_succ]
  unfold affineReferenceInput
  nlinarith

theorem affineReferenceInput_mask_and_depth {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (D : ℕ) (hD : 0 < D) {epsilon L T C U : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U)
    (hepsInv : epsilon⁻¹ ≤ Real.exp U) (hDU : (D : ℝ) ≤ Real.exp U) :
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon))
      (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ affineReferenceInput epsilon U ∧
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affineReferenceInput epsilon U ∧
    T + 4 ≤ affineReferenceInput epsilon U := by
  have hprim := affineComparisonPrimitive_bounds hepsilon hepsilon1 hU hL hT hC hLU hTU hCU hepsInv
  have hs := (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1
  have hm := affineSamplerPrimeMask_card_le (ξ := epsilon / (2 + epsilon)) prime hprime hinj hs
    (by norm_num : 0 < (1 : ℕ)) (by norm_num : 0 < (1 : ℕ)) hD
    (by simp : ((1 : ℕ) : ℝ) ≤ Real.exp 0) (by simp : ((1 : ℕ) : ℝ) ≤ Real.exp 0) hDU
  have hthreshold : affineComparisonPrimeThreshold (epsilon / (2 + epsilon))
      (affineComparisonScale epsilon L T C) ≤
      (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon := by
    exact pow_le_pow_left₀ (by linarith) (by linarith [hprim.2.1]) _
  have hbudget := affineReferenceInput_bounds epsilon hU
  refine ⟨?_, hprim.1.trans hbudget.2.2, ?_⟩
  · unfold affineReferenceInput
    norm_num at hm
    linarith [affinePrimitiveLogBudget_nonneg hU]
  · have hpow : 0 ≤ (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon :=
      pow_nonneg (by unfold affinePrimitiveLogBudget; positivity) _
    unfold affineReferenceInput affinePrimitiveLogBudget at *
    linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    Finset (σ → ℤ) := by
  classical
  exact (translatedIntegerBox lo N).filter (fun z => ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i)

@[simp] theorem mem_primeCoordinateCell {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I x ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i := by
  classical
  simp only [primeCoordinateCell, Finset.mem_filter]

theorem primeCoordinateCell_anchor {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (u : σ → ℤ) (hu : u ∈ primeCoordinateCell lo N q I x) :
    primeCoordinateCell lo N q I x = primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) := by
  ext z
  simp only [mem_primeCoordinateCell] at hu ⊢
  constructor
  · rintro ⟨hz, heq⟩
    exact ⟨hz, fun i hi => (heq i hi).trans (hu.2 i hi).symm⟩
  · rintro ⟨hz, heq⟩
    exact ⟨hz, fun i hi => (heq i hi).trans (hu.2 i hi)⟩

theorem mem_primeCoordinateCell_anchor {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ j, z j ≡ u j [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] := by
  rw [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, heq⟩
    refine ⟨hz, ?_⟩
    intro j
    apply (modEq_selected_prod_iff q hcop I (z j) (u j)).mpr
    intro i hi
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mp (congrFun (heq i hi) j)
  · rintro ⟨hz, hmod⟩
    refine ⟨hz, ?_⟩
    intro i hi
    funext j
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mpr
      ((modEq_selected_prod_iff q hcop I (z j) (u j)).mp (hmod j) i hi)

noncomputable def primeCoordinateCellEquiv {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u : σ → ℤ) :
    primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ≃
      IntegerResidueBox lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u where
  toFun z := fun j => ⟨z.val j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ((mem_translatedIntegerBox lo N z.val).mp ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).1 j),
    ((mem_primeCoordinateCell_anchor lo N q hcop I u z.val).mp z.property).2 j⟩⟩
  invFun z := ⟨fun j => (z j).val, (mem_primeCoordinateCell_anchor lo N q hcop I u _).mpr
    ⟨(mem_translatedIntegerBox lo N _).mpr (fun j => Finset.mem_Ico.mp (Finset.mem_filter.mp (z j).property).1),
      fun j => (Finset.mem_filter.mp (z j).property).2⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by funext j; apply Subtype.ext; rfl

theorem primeCoordinateCell_mean {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u : σ → ℤ)
    (f : (σ → ℤ) → ℂ) :
    (𝔼 z : primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))), f z.val) =
      physicalResidueMean f lo N (∏ i ∈ I, q i) u := by
  exact Fintype.expect_equiv (primeCoordinateCellEquiv lo N q hcop I u) _ _ (fun _ => rfl)

end Erdos3

end

end OAI

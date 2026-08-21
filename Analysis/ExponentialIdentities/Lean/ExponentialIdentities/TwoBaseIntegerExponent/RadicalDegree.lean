import ExponentialIdentities.TwoBaseIntegerExponent.RationalPowerIndex
import Mathlib.RingTheory.Norm.Basic

namespace LeanProofs.TwoBaseIntegerExponent

open Set Polynomial IntermediateField

noncomputable section

/-- A positive real algebraic radical whose first rational power is its `d`-th power
has exact degree `d`. -/
theorem irreducible_X_pow_sub_C_of_least_rational_power
    {E : ℝ} (hE : 0 < E) {d : ℕ} (hd : 0 < d) {q : ℚ}
    (hq : E ^ d = (q : ℝ))
    (hleast : ∀ n : ℕ, E ^ n ∈ Set.range ((↑) : ℚ → ℝ) → 0 < n → d ≤ n) :
    Irreducible (X ^ d - C q) ∧
      minpoly ℚ E = X ^ d - C q ∧
      (minpoly ℚ E).natDegree = d := by
  let p : ℚ[X] := X ^ d - C q
  have hpMonic : p.Monic := by
    dsimp only [p]
    exact monic_X_pow_sub_C q hd.ne'
  have hpEval : Polynomial.aeval E p = 0 := by
    dsimp only [p]
    simp [hq]
  have hEint : IsIntegral ℚ E := ⟨p, hpMonic, hpEval⟩
  let K := ℚ⟮E⟯
  let α : K := AdjoinSimple.gen ℚ E
  letI : FiniteDimensional ℚ K := adjoin.finiteDimensional hEint
  let r : ℕ := Module.finrank ℚ K
  have hrEq : r = (minpoly ℚ E).natDegree := by
    dsimp only [r, K]
    exact adjoin.finrank hEint
  have hrPos : 0 < r := by
    dsimp only [r]
    exact Module.finrank_pos
  have hαpow : α ^ d = algebraMap ℚ K q := by
    apply Subtype.ext
    change E ^ d = (q : ℝ)
    exact hq
  have hnormQ : (Algebra.norm ℚ α) ^ d = q ^ r := by
    calc
      (Algebra.norm ℚ α) ^ d = Algebra.norm ℚ (α ^ d) := by rw [map_pow]
      _ = Algebra.norm ℚ (algebraMap ℚ K q) := by rw [hαpow]
      _ = q ^ r := by simp only [Algebra.norm_algebraMap, r]
  have hnormR : |((Algebra.norm ℚ α : ℚ) : ℝ)| = E ^ r := by
    apply (pow_left_inj₀ (abs_nonneg _) (pow_nonneg hE.le _) hd.ne').mp
    rw [← abs_pow]
    have hcast := congrArg (fun z : ℚ ↦ (z : ℝ)) hnormQ
    push_cast at hcast
    rw [hcast, ← hq, ← pow_mul, abs_of_pos (pow_pos hE _), mul_comm, pow_mul]
  have hrRat : E ^ r ∈ Set.range ((↑) : ℚ → ℝ) := by
    refine ⟨|Algebra.norm ℚ α|, ?_⟩
    push_cast
    exact hnormR
  have hdr : d ≤ r := hleast r hrRat hrPos
  have hminDvd : minpoly ℚ E ∣ p := minpoly.dvd ℚ E hpEval
  have hrLe : r ≤ d := by
    rw [hrEq]
    exact (natDegree_le_of_dvd hminDvd hpMonic.ne_zero).trans_eq (by simp [p])
  have hr : r = d := Nat.le_antisymm hrLe hdr
  have hdeg : (minpoly ℚ E).natDegree = d := hrEq.symm.trans hr
  have hpEq : minpoly ℚ E = p := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hEint) hpMonic hminDvd
    simp [hdeg, p]
  have hpIrr : Irreducible p := hpEq ▸ minpoly.irreducible hEint
  refine ⟨?_, ?_, hdeg⟩
  · simpa only [p] using hpIrr
  · simpa only [p] using hpEq

/-- The least rational-power index of an odd core is the exact degree of its normalized
radical polynomial over `ℚ`. -/
theorem oddCoreRpow_exact_radical_degree
    {w d a c : ℕ} (hw : 0 < w) (hd : 0 < d)
    (hleast : ∀ j : ℤ, oddCoreRpow w ^ j ∈ Set.range ((↑) : ℚ → ℝ) →
      0 < j → (d : ℤ) ≤ j)
    (hnorm : oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a) :
    Irreducible
        (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ∧
      minpoly ℚ (oddCoreRpow w) =
        X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a) ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d := by
  apply irreducible_X_pow_sub_C_of_least_rational_power
      (oddCoreRpow_pos hw) hd
  · rw [hnorm]
    push_cast
    rfl
  · intro n hnRat hn
    have hnRatZ : oddCoreRpow w ^ (n : ℤ) ∈ Set.range ((↑) : ℚ → ℝ) := by
      simpa using hnRat
    have hdnZ := hleast (n : ℤ) hnRatZ (by exact_mod_cast hn)
    exact_mod_cast hdnZ

/-- Failure with a fixed common odd core yields a normalized radical whose binomial is
irreducible and whose algebraic degree is exactly the primitive rational-power index. -/
theorem exists_exact_radical_degree_of_fixed_common_oddCore
    {w : ℕ} (hodd : Odd w) (hw : 1 < w)
    (hrep : ∀ m : ℕ, TwoBaseNaturalCandidate m →
      ∃ i j : ℕ, m = 2 ^ i * w ^ j)
    (hfail : ∃ m : ℕ, TwoBaseNaturalCandidate m ∧
      ¬ ∃ n : ℕ, m = 2 ^ n) :
    ∃ d a c : ℕ,
      0 < d ∧ 0 < c ∧ (a = 0 ∨ ¬ 3 ∣ c) ∧
      oddCoreRpow w ^ d = (c : ℝ) / (3 : ℝ) ^ a ∧
      Irreducible
        (X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a)) ∧
      minpoly ℚ (oddCoreRpow w) =
        X ^ d - C ((c : ℚ) / (3 : ℚ) ^ a) ∧
      (minpoly ℚ (oddCoreRpow w)).natDegree = d := by
  obtain ⟨d, a, c, hd, hc, ha, _hindex, hleast, hnorm, _hchar, _hβleast⟩ :=
    exists_exact_solution_monoid_of_fixed_common_oddCore hodd hw hrep hfail
  obtain ⟨hirr, hmin, hdeg⟩ :=
    oddCoreRpow_exact_radical_degree (by omega) hd hleast hnorm
  exact ⟨d, a, c, hd, hc, ha, hnorm, hirr, hmin, hdeg⟩

end

end LeanProofs.TwoBaseIntegerExponent

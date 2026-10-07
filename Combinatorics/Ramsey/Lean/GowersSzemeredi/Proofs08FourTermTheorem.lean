import GowersSzemeredi.Proofs18QuadraticDoubleExponential

/-! The quantitative four-term theorem in its exact catalogue form. The
large-density case avoids trying to absorb constants into powers at delta=1. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- More than three quarters of a prime cyclic group contains four terms
with common difference -1, by the union bound on four sets of bad starts. -/
theorem hasModAP_four_of_three_quarters {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (hdense : 3 * N < 4 * A.card) : HasModAP A 4 := by
  classical
  let S : Finset (ZMod N) := Finset.univ \ A
  let F : Fin 4 → Finset (ZMod N) := fun i => S.image (fun x => x + ((i : Nat) : ZMod N))
  let bad := Finset.univ.biUnion F
  have hScard : S.card = N - A.card := by simp [S, Finset.card_sdiff, ZMod.card]
  have hbad : bad.card ≤ 4 * (N - A.card) := by
    calc
      _ ≤ ∑ i : Fin 4, (F i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin 4, S.card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)
      _ = _ := by simp [hScard]
  have hAcard : A.card ≤ N := by simpa [ZMod.card] using Finset.card_le_univ A
  have hbadlt : bad.card < (Finset.univ : Finset (ZMod N)).card := by
    simp only [Finset.card_univ, ZMod.card]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadlt
  have hpoint (i : Fin 4) : a - ((i : Nat) : ZMod N) ∈ A := by
    by_contra hx
    apply ha
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨a - ((i : Nat) : ZMod N), by simp [S, hx], ?_⟩
    simp
  refine ⟨a, -1, bne_iff_ne.mpr (neg_ne_zero.mpr one_ne_zero), ?_⟩
  intro i hi
  simpa only [mul_neg, mul_one, sub_eq_add_neg] using hpoint ⟨i, hi⟩

/-- The fixed prefactor and the factor two in the explicit density bound
can be absorbed into one fixed power as long as delta is at most 3/4. -/
theorem quadratic_double_exp_power_absorption :
    ∃ C : Real, 0 < C ∧ ∀ delta : Real, 0 < delta → delta ≤ 3 / 4 →
      (quadraticIterationLogBudgetConstant + 1) * (2 / delta) ^ (3070857064 : Nat) ≤
        (1 / delta) ^ C := by
  let p : Nat := 3070857064
  let K := quadraticIterationLogBudgetConstant + 1
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (K * (2 : Real) ^ p)
    (by norm_num : (1 : Real) < 4 / 3)
  refine ⟨((m + p : Nat) : Real), by dsimp [p]; positivity, ?_⟩
  intro delta hδ hδsmall
  have hbase : (4 / 3 : Real) ≤ 1 / delta := (le_div_iff₀ hδ).mpr (by linarith)
  have hpower : K * (2 : Real) ^ p ≤ (1 / delta) ^ m := hm.le.trans
    (pow_le_pow_left₀ (by norm_num) hbase m)
  rw [Real.rpow_natCast]
  change K * (2 / delta) ^ p ≤ (1 / delta) ^ (m + p)
  calc
    _ = (K * (2 : Real) ^ p) * (1 / delta) ^ p := by
      have hdiv : 2 / delta = 2 * (1 / delta) := by ring
      rw [hdiv, mul_pow, ← mul_assoc]
    _ ≤ (1 / delta) ^ m * (1 / delta) ^ p :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = _ := (pow_add _ _ _).symm

/-- **Theorem 8.2.** Complete quadratic density iteration yields the
double-exponential four-term bound with one fixed positive exponent. -/
theorem theorem_8_2_holds : theorem_8_2 := by
  obtain ⟨C, hC, habsorb⟩ := quadratic_double_exp_power_absorption
  refine ⟨C, hC, ?_⟩
  intro N _ _ A delta hδ hcard hN
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcardle : (A.card : Real) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa [ZMod.card] using Finset.card_le_univ A)
  have hδone : delta ≤ 1 := by nlinarith only [hcard, hcardle, hNpos]
  by_cases hdense : 3 / 4 < delta
  · apply hasModAP_four_of_three_quarters A
    have hreal : (3 : Real) * N < 4 * A.card := by nlinarith only [hdense, hcard, hNpos]
    exact_mod_cast hreal
  · apply quadratic_cyclic_szemeredi_double_exp delta hδ hδone N _ A hcard.symm.le
    exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
      (habsorb delta hδ (le_of_not_gt hdense)))).trans hN

end LeanProofs.GowersSzemeredi

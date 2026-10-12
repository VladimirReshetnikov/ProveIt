import GowersSzemeredi.Proofs08FourTermTheorem

/-! The four-term theorem over every nonzero modulus, with a lower bound
on the density rather than equality. The quadratic iteration already has
this scope; the dense branch needs only that the group has order at least two. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- More than three quarters of any cyclic group of order at least two contains four terms
with common difference -1, by the union bound on four sets of bad starts. -/
theorem hasModAP_four_of_three_quarters_all_moduli {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (A : Finset (ZMod N)) (hdense : 3 * N < 4 * A.card) : HasModAP A 4 := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
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

/-- The quantitative four-term theorem with neither primality nor exact density. -/
def theorem_8_2_all_moduli : Prop :=
  ∃ C : Real, 0 < C ∧ ∀ (N : Nat) [NeZero N]
      (A : Finset (ZMod N)) (delta : Real),
    0 < delta → delta * N ≤ A.card →
    Real.exp (Real.exp ((1 / delta) ^ C)) ≤ N → HasModAP A 4

/-- The same fixed exponent as in the prime-modulus proof works over all moduli. -/
theorem theorem_8_2_all_moduli_holds : theorem_8_2_all_moduli := by
  obtain ⟨C, hC, habsorb⟩ := quadratic_double_exp_power_absorption
  refine ⟨C, hC, ?_⟩
  intro N _ A delta hδ hcard hN
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcardle : (A.card : Real) ≤ N := by
    exact_mod_cast (show A.card ≤ N by simpa [ZMod.card] using Finset.card_le_univ A)
  have hδone : delta ≤ 1 := by nlinarith only [hcard, hcardle, hNpos]
  have hNtwo : 2 ≤ N := by
    have hlt : (1 : Real) < N :=
      (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).trans_le hN
    have : 1 < N := by exact_mod_cast hlt
    omega
  by_cases hdense : 3 / 4 < delta
  · apply hasModAP_four_of_three_quarters_all_moduli hNtwo A
    have hreal : (3 : Real) * N < 4 * A.card := by
      nlinarith only [hdense, hcard, hNpos]
    exact_mod_cast hreal
  · apply quadratic_cyclic_szemeredi_double_exp delta hδ hδone N _ A hcard
    exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
      (habsorb delta hδ (le_of_not_gt hdense)))).trans hN

end LeanProofs.GowersSzemeredi

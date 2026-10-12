import GowersSzemeredi.Proofs15DegenerateArrangements

/-! The printed degeneracy bound over every prime. At characteristic two,
the stated coefficient already dominates the whole parameter space. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def lemma_15_4_all_primes : Prop :=
  ∀ (N k d : Nat) [NeZero N], Nat.Prime N → 1 ≤ k → 1 ≤ d →
    (degenerateGeneralArrangementCount (N := N) (k := k) d : Real) ≤
      (3 : Real) ^ (2 * d * 2 ^ k) * k *
        (N : Real) ^ ((2 * d + 1) * k + 2 * d - 2)

private theorem degeneracy_bound_at_two (k d : Nat) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (degenerateGeneralArrangementCount (N := 2) (k := k) d : Real) ≤
      (3 : Real) ^ (2 * d * 2 ^ k) * k *
        (2 : Real) ^ ((2 * d + 1) * k + 2 * d - 2) := by
  classical
  let t : Nat := k + 2 * d * k + 2 * d
  have hcard : Fintype.card (GeneralArrangement 2 k d) = 2 ^ t := by
    simp only [GeneralArrangement, Point, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    dsimp only [t]
    rw [← pow_mul, Nat.mul_comm k (2 * d), ← pow_add, ← pow_add]
    congr 1
    omega
  have hupperNat : degenerateGeneralArrangementCount (N := 2) (k := k) d ≤ 2 ^ t := by
    unfold degenerateGeneralArrangementCount countWhere
    calc
      _ ≤ Fintype.card (GeneralArrangement 2 k d) := Finset.card_le_univ _
      _ = _ := hcard
  have hupper : (degenerateGeneralArrangementCount (N := 2) (k := k) d : Real) ≤
      (2 : Real) ^ t := by exact_mod_cast hupperNat
  have hpower : 1 ≤ (2 : Nat) ^ k := Nat.one_le_pow k 2 (by decide)
  have hE : 2 ≤ 2 * d * 2 ^ k := by
    calc
      2 = 2 * 1 := by omega
      _ ≤ (2 * d) * 2 ^ k := Nat.mul_le_mul (by omega) hpower
  have hC : (4 : Real) ≤ (3 : Real) ^ (2 * d * 2 ^ k) * k := by
    have hkReal : (1 : Real) ≤ k := by exact_mod_cast hk
    calc
      4 ≤ (3 : Real) ^ 2 := by norm_num
      _ ≤ (3 : Real) ^ (2 * d * 2 ^ k) := pow_le_pow_right₀ (by norm_num) hE
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hkReal
  have hsplit : ((2 * d + 1) * k + 2 * d - 2) + 2 = t := by
    dsimp only [t]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ (2 : Real) ^ t := hupper
    _ = 4 * (2 : Real) ^ ((2 * d + 1) * k + 2 * d - 2) := by
      rw [← hsplit, pow_add]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

/-- Oddness is unnecessary for the final counting inequality, despite being
necessary in the signed-Walsh ingredient used in the odd-prime proof. -/
theorem lemma_15_4_all_primes_holds : lemma_15_4_all_primes := by
  intro N k d _ hprime hk hd
  rcases hprime.eq_two_or_odd' with htwo | hodd
  · subst N
    exact degeneracy_bound_at_two k d hk hd
  · exact lemma_15_4_holds N k d hprime hodd hk hd

end LeanProofs.GowersSzemeredi

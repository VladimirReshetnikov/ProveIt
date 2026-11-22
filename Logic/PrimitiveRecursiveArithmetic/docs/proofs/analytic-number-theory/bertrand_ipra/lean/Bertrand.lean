import BertrandLegendre
import BertrandReconstruction

/-! Public theorems. All proofs below refer only to the local development and Std. -/
namespace Bertrand

theorem central_factorization : CentralFactorization :=
  central_of_reconstruction factor_numeral

theorem no_large_gap : NoLargeGap := no_gap_of_factorization central_factorization primorial_bound

theorem strong {n : Nat} (hn : 4 ≤ n) : Good n (witness n) := strong_of_large no_large_gap hn

theorem strict {n : Nat} (hn : 2 ≤ n) :
    n < witness n ∧ witness n < 2*n ∧ Prime (witness n) := weak_of_large no_large_gap hn

theorem closed_right {n : Nat} (hn : 1 ≤ n) :
    n < witness n ∧ witness n ≤ 2*n ∧ Prime (witness n) := closed_right_of_large no_large_gap hn

theorem least {n q : Nat} (hn : 1 ≤ n) (hlo : n < q) (hhi : q < witness n) : ¬ Prime q := by
  by_cases h : 4 ≤ n
  · exact witness_minimal no_large_gap h hlo hhi
  · have hsmall : n=1 ∨ n=2 ∨ n=3 := by omega
    rcases hsmall with rfl | rfl | rfl
    · have v : witness 1 = 2 := by decide
      omega
    · have v : witness 2 = 3 := by decide
      omega
    · have v : witness 3 = 5 := by decide
      have e : q=4 := by omega
      subst q
      intro pr
      exact (pr.2 2 (by decide) (by decide)) ⟨2,rfl⟩

/-- Zero-based enumeration: at 0 this is the first prime, 2. -/
def nthPrime : Nat → Nat
  | 0 => 2
  | k+1 => witness (nthPrime k)

theorem nthPrime_prime (k : Nat) : Prime (nthPrime k) := by
  induction k with
  | zero => exact (primeB_spec 2).mp (by decide)
  | succ k ih => exact (strict ih.1).2.2

theorem consecutive (k : Nat) :
    nthPrime k < nthPrime (k+1) ∧ nthPrime (k+1) < 2*nthPrime k ∧
    ∀ q, nthPrime k < q → q < nthPrime (k+1) → ¬ Prime q := by
  have h := (nthPrime_prime k).1
  have w := strict h
  exact ⟨w.1, w.2.1, fun _ lo hi => least (by omega) lo hi⟩

theorem nthPrime_lower (k : Nat) : k+2 ≤ nthPrime k := by
  induction k with
  | zero => decide
  | succ k ih => have h := (consecutive k).1; omega

/-- Every prime occurs in this enumeration, with an explicit bound on its index. -/
theorem nthPrime_exhaustive {p : Nat} (hp : Prime p) : ∃ k, k ≤ p-2 ∧ nthPrime k = p := by
  have scan (t : Nat) : (∃ k, k ≤ t ∧ nthPrime k = p) ∨ nthPrime t < p := by
    induction t with
    | zero =>
      by_cases h : p = 2
      · exact Or.inl ⟨0, by decide, h.symm⟩
      · exact Or.inr (show 2 < p by have := hp.1; omega)
    | succ t ih =>
      rcases ih with ⟨k, hk, he⟩ | hl
      · exact Or.inl ⟨k, by omega, he⟩
      · by_cases h : nthPrime (t+1) = p
        · exact Or.inl ⟨t+1, Nat.le_refl _, h⟩
        · by_cases hu : nthPrime (t+1) < p
          · exact Or.inr hu
          · exact False.elim ((consecutive t).2.2 p hl (by omega) hp)
  rcases scan (p-2) with hit | lt
  · exact hit
  · have := nthPrime_lower (p-2)
    omega

end Bertrand

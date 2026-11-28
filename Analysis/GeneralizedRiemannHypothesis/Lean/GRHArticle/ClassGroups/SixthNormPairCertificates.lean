import GRHArticle.ClassGroups.SixthNormCollisionBound

/-!
# Verified instances of the sixth-power pair obstruction

This replays all pairs with both primes at most 2113 and includes a
separate pair for which the largest witness in the full search is needed.
-/

namespace GRHArticle.ClassGroups

private def earlySixthPrimes : List ℕ :=
  [2069,2081,2083,2087,2089,2099,2111,2113]

private theorem earlySixthPrime_mem {r : ℕ} (hlo : 2065 ≤ r) (hhi : r ≤ 2113)
    (hp : r.Prime) : r ∈ earlySixthPrimes := by
  interval_cases r <;> revert hp <;> decide +kernel

private def checkEarlyRow (p : ℕ) : Bool :=
  earlySixthPrimes.all (fun q ↦ if p < q then checkSixthNormPair p q else true)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2069 : checkEarlyRow 2069 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2081 : checkEarlyRow 2081 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2083 : checkEarlyRow 2083 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2087 : checkEarlyRow 2087 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2089 : checkEarlyRow 2089 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2099 : checkEarlyRow 2099 = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem early_2111 : checkEarlyRow 2111 = true := by decide +kernel

private theorem early_2113 : checkEarlyRow 2113 = true := by decide +kernel

private theorem checkEarlyRows : earlySixthPrimes.all checkEarlyRow = true := by
  simp only [earlySixthPrimes, List.all_cons, List.all_nil, early_2069, early_2081, early_2083,
    early_2087, early_2089, early_2099, early_2111, early_2113, Bool.and_self]

/-- The full pairwise statement through 2113, covering all 28 eligible
prime pairs in this range. -/
theorem checkSixthNormPair_of_le_2113 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hqU : q ≤ 2113)
    (hcut : censusDiscriminantCutoff < 4*p^6) : checkSixthNormPair p q = true := by
  have hqcut : censusDiscriminantCutoff < 4*q^6 :=
    hcut.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq.le _))
  have hmem (r : ℕ) (hr : r.Prime) (hB : r ≤ 2113)
      (hc : censusDiscriminantCutoff < 4*r^6) : r ∈ earlySixthPrimes := by
    have h₁ : 2065 ≤ r := by
      by_contra! h
      have hk : 4*2064^6 ≤ censusDiscriminantCutoff := by decide +kernel
      exact (not_lt_of_ge ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by omega : r ≤ 2064) 6)).trans hk)) hc
    exact earlySixthPrime_mem h₁ hB hr
  have hrow := List.all_eq_true.mp checkEarlyRows p (hmem p hp (hpq.le.trans hqU) hcut)
  have h := List.all_eq_true.mp hrow q (hmem q hq hqU hqcut)
  simpa only [if_pos hpq] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Full replay of the pair containing the recorded witness at 151. -/
theorem checkSixthNormPair_2381_3323 : checkSixthNormPair 2381 3323 = true := by decide +kernel

/-- Read back the candidate requiring the last prime in the recorded sieve. -/
theorem sixthNormPair_candidate_151 :
    sixthNormCandidate 2381 3323 32266241748 = 714255603922907803620 ∧
      HasSixthSquareWitness 714255603922907803620 :=
  ⟨by decide +kernel, hasSixthSquareWitness_of_check (by decide +kernel)⟩

private theorem shortSixthNorm_coefficient_eq_one {x p a b : ℕ}
    (hx : censusDiscriminantCutoff < x) (hp : p ≤ 2113) (hb : 0 < b)
    (h : SixthPowerNormEquation x p a b) : b = 1 := by
  by_contra! hne
  have hnum : 4*2113^6 < 2^2*censusDiscriminantCutoff := by decide +kernel
  have hp' := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp 6)
  have hb' : 2^2*censusDiscriminantCutoff ≤ b^2*x :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 2 ≤ b) 2) hx.le
  rw [mul_comm (b^2) x] at hb'
  unfold SixthPowerNormEquation at h
  omega

/-- In the fully checked range, there cannot be two distinct eligible
norm primes when all small square witnesses for the discriminant are absent. -/
theorem no_two_sixthNormPrimes_le_2113 {x p q a c b d : ℕ}
    (hx : censusDiscriminantCutoff < x) (hno : NoSixthDiscriminantSquareWitness x)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hqU : q ≤ 2113)
    (hb : 0 < b) (hd : 0 < d)
    (ha : SixthPowerNormEquation x p a b) (hc : SixthPowerNormEquation x q c d) :
    False := by
  rw [shortSixthNorm_coefficient_eq_one hx (hpq.le.trans hqU) hb ha] at ha
  rw [shortSixthNorm_coefficient_eq_one hx hqU hd hc] at hc
  have hcut : censusDiscriminantCutoff < 4*p^6 := by
    unfold SixthPowerNormEquation at ha
    simp only [one_pow, mul_one] at ha
    omega
  obtain ⟨u,hdiv,hlo,hhi,hM⟩ :=
    exists_sixthNormCandidate_of_collision (by omega) hpq (by decide : 0 < 1) ha hc
  have huCut : censusDiscriminantCutoff < sixthNormCandidate p q u := by simpa [hM] using hx
  have hW := hasSixthSquareWitness_of_pairCheck hpq hdiv hlo hhi huCut
    (checkSixthNormPair_of_le_2113 hp hq hpq hqU hcut)
  rw [hM] at hW
  obtain ⟨r,hr,hrlo,hrhi,j,hj,hj2⟩ := discriminantSquareWitness_of_sixthWitness hW
  exact hno r hr hrlo hrhi j hj hj2

end GRHArticle.ClassGroups

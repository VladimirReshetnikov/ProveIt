import IPRADerivations.AnalyticNumberTheory.Riemann.EnergyInequality

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`PowerDivisorBounds.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Integer witness conversion for convolution along perfect powers.
No real powers or infinite series enter any estimate. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PowerDivisorBounds
open scoped BigOperators

/-- Each complete block of denominators [2^j+1,2^{j+1}] costs at most X. -/
private theorem block_bound (u : ℕ → ℕ) (X e : ℕ)
    (hu : ∀ i, (i+1)*u i ≤ X) :
    ∑ i ∈ Finset.range (2^e), u i ≤ (e+1)*X := by
  induction e with
  | zero => simpa using hu 0
  | succ e ih =>
    let b := 2^e
    have hb : 0 < b := Nat.two_pow_pos _
    have tail : b * (∑ i ∈ Finset.range b, u (b+i)) ≤ b*X := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ _i ∈ Finset.range b, X := Finset.sum_le_sum fun i _ =>
          (Nat.mul_le_mul_right _ (show b ≤ b+i+1 by omega)).trans (hu (b+i))
        _ = b*X := by simp
    have small := Nat.le_of_mul_le_mul_left tail hb
    have split : 2^(e+1) = b+b := by simp [b, pow_succ, Nat.mul_two]
    rw [split, Finset.sum_range_add]
    dsimp [b] at small ⊢
    rw [Nat.succ_mul]
    exact Nat.add_le_add ih small

theorem harmonic_budget (u : ℕ → ℕ) (X N : ℕ)
    (hu : ∀ i < N, (i+1)*u i ≤ X) :
    ∑ i ∈ Finset.range N, u i ≤ (N.log2+2)*X := by
  let v := fun i => if i < N then u i else 0
  have hv (i : ℕ) : (i+1)*v i ≤ X := by
    by_cases h : i < N
    · simpa [v,h] using hu i h
    · simp [v,h]
  calc
    _ = ∑ i ∈ Finset.range N, v i := Finset.sum_congr rfl fun i h => by
      simp [v,Finset.mem_range.mp h]
    _ ≤ ∑ i ∈ Finset.range (2^(N.log2+1)), v i :=
      Finset.sum_le_sum_of_subset (Finset.range_mono Nat.lt_log2_self.le)
    _ ≤ _ := block_bound v X (N.log2+1) hv

private theorem one_add_le_two_pow (a : ℕ) : a+1 ≤ 2^a := by
  induction a with
  | zero => decide
  | succ a ih => rw [pow_succ]; omega

/-- Absorb an integer logarithm at the explicit cost of one power of N. -/
theorem log_absorb (N k : ℕ) (hn : 0 < N) (hk : 0 < k) :
    (N.log2+2)^k ≤ (2*k)^k*N := by
  let l := N.log2
  have hdiv := Nat.div_add_mod l k
  have hmod := Nat.mod_lt l hk
  have hbase : l+2 ≤ (2*k)*2^(l/k) := calc
    _ ≤ 2*(k*(l/k+1)) := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2*(k*2^(l/k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (one_add_le_two_pow _))
    _ = _ := by ac_rfl
  calc
    _ ≤ ((2*k)*2^(l/k))^k := Nat.pow_le_pow_left hbase _
    _ = (2*k)^k*2^(k*(l/k)) := by rw [mul_pow,← pow_mul, Nat.mul_comm (l/k) k]
    _ ≤ (2*k)^k * 2^l := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.log2_self_le (by omega))

private theorem abs_sum (t : ℕ → ℤ) (N : ℕ) :
    (∑ i ∈ Finset.range N, t i).natAbs ≤ ∑ i ∈ Finset.range N, (t i).natAbs := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (Int.natAbs_add_le ..).trans (Nat.add_le_add_right ih _)

/-- If the d-th signed contribution is a prefix at an argument ≤ N/d²
with the input exponent at 2r, this is the output witness at r. -/
theorem power_divisor_transfer (r c N : ℕ) (hr : 0 < r)
    (t : ℕ → ℤ) (m : ℕ → ℕ)
    (harg : ∀ i < N, (i+1)^2*m i ≤ N)
    (hterm : ∀ i < N, (t i).natAbs^(4*r) ≤ c*(m i)^(2*r+1)) :
    (∑ i ∈ Finset.range N, t i).natAbs^(2*r) ≤
      ((c+1)*(8*r)^(2*r))*N^(r+1) := by
  by_cases hN : N = 0
  · subst N; simp [Nat.ne_of_gt hr]
  have hn : 0 < N := by omega
  let u := fun i => (t i).natAbs
  let X := (Finset.range N).sup (fun i => (i+1)*u i)
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup (Finset.range N)
    ⟨0, Finset.mem_range.mpr hn⟩ (fun i => (i+1)*u i)
  have hX : X = (j+1)*u j := heq
  have hjn := Finset.mem_range.mp hj
  have hp : X^(4*r) ≤ c*N^(2*r+1) := by
    rw [hX, mul_pow]
    calc
      _ ≤ (j+1)^(4*r)*(c*(m j)^(2*r+1)) := Nat.mul_le_mul_left _ (hterm j hjn)
      _ ≤ (j+1)^(2*(2*r+1))*(c*(m j)^(2*r+1)) := Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (by omega))
      _ = c*((j+1)^2*m j)^(2*r+1) := by rw [pow_mul, mul_pow]; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (harg j hjn) _)
  have total := (abs_sum t N).trans
    (harmonic_budget u X N fun i hi => Finset.le_sup (f := fun j => (j+1)*u j) (Finset.mem_range.mpr hi))
  have rough := Nat.pow_le_pow_left total (4*r)
  rw [mul_pow] at rough
  have budget := Nat.mul_le_mul (log_absorb N (4*r) hn (by omega)) hp
  have b : 2*(4*r) = 8*r := by omega
  rw [b] at budget
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  calc
    _ = (∑ i ∈ Finset.range N, t i).natAbs^(4*r) := by rw [← pow_mul]; congr 1; omega
    _ ≤ ((8*r)^(4*r)*N) * (c*N^(2*r+1)) := rough.trans budget
    _ = c * ((8*r)^(2*r) * N^(r+1))^2 := by
      rw [mul_pow ((8*r)^(2*r)) (N^(r+1)) 2, ← pow_mul, ← pow_mul, show (2*r)*2 = 4*r by omega,
        show (r+1)*2 = (2*r+1)+1 by omega, pow_succ N (2*r+1)]
      ac_rfl
    _ ≤ (c+1)^2 * ((8*r)^(2*r) * N^(r+1))^2 :=
      Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le c, Nat.zero_le (c*c)])
    _ = _ := by rw [← mul_pow]; ac_rfl

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PowerDivisorBounds

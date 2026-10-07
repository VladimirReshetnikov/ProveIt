import GowersSzemeredi.Proofs05ModularApproximation

/-! Transfer a sufficiently small Dirichlet witness to polynomial recurrence
in every degree at least two. The sample size is distinct from the order
`t^(k-1)` used in rational approximation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem polynomial_recurrence_of_dirichlet_witness {N R k t q : Nat} [NeZero N]
    (a r : ZMod N) (b : Int) (hk : 2 ≤ k) (hR : 1 ≤ R) (ht : 0 < t)
    (hq : 0 < q) (hr : r ≠ 0)
    (happrox : |(-(a * r).valMinAbs : Real) / N - (b : Real) / q| ≤
      ((q : Real) * (t : Real) ^ (k - 1))⁻¹)
    (hsmall : (centeredAbs r : Real) * q < (t : Real) / R) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ t ∧
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) < (N : Real) / R := by
  have ht0 : (0 : Real) < t := by exact_mod_cast ht
  have hR1 : (1 : Real) ≤ R := by exact_mod_cast hR
  have hR0 : (0 : Real) < R := by linarith
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hs : 0 < centeredAbs r := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hr ((ZMod.valMinAbs_eq_zero r).mp (Int.natAbs_eq_zero.mp hz))
  let p := centeredAbs r * q
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (by dsimp [p]; positivity)
  have hpR : (p : Real) < (t : Real) / R := by simpa only [p, Nat.cast_mul] using hsmall
  have hpT : (p : Real) < t := hpR.trans_le
    ((div_le_iff₀ hR0).mpr (by nlinarith))
  have hpNat : p ≤ t := by exact_mod_cast hpT.le
  have hratio : (p : Real) / t < 1 / R := by
    apply (div_lt_div_iff₀ ht0 hR0).mpr
    simpa only [one_mul] using (lt_div_iff₀ hR0).mp hpR
  have hratioOne : (p : Real) / t ≤ 1 := (div_le_one ht0).mpr hpT.le
  have hpPow : ((p : Real) / t) ^ (k - 1) ≤ (p : Real) / t := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by positivity) hratioOne (by omega : 1 ≤ k - 1)
  have hcenter := modular_monomial_of_rational_approximation (k := k) a r b
    (by omega) hq (show 0 < (t : Real) ^ (k - 1) by positivity) happrox
  refine ⟨p, hp, hpNat, ?_⟩
  calc
    _ ≤ ((N : Real) / (t : Real) ^ (k - 1)) * (p : Real) ^ (k - 1) := hcenter
    _ = (N : Real) * ((p : Real) / t) ^ (k - 1) := by rw [div_pow]; ring
    _ ≤ (N : Real) * ((p : Real) / t) := mul_le_mul_of_nonneg_left hpPow hN.le
    _ < (N : Real) * (1 / R) := mul_lt_mul_of_pos_left hratio hN
    _ = (N : Real) / R := by ring

end LeanProofs.GowersSzemeredi

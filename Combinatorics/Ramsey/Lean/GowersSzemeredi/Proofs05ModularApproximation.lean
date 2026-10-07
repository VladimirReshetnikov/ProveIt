import GowersSzemeredi.Section05

/-! Transfer a rational approximation of a Fourier frequency back to a
small modular monomial. This isolates the integer representative and sign
argument from all analytic Weyl estimates and numerical thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem recurrence_centeredAbs_intCast_le {N : Nat} [NeZero N] (i : Int) :
    centeredAbs (i : ZMod N) ≤ i.natAbs := by
  have hnat (n : Nat) : centeredAbs (n : ZMod N) ≤ n := by
    rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
    exact (Nat.min_le_left _ _).trans (Nat.mod_le n N)
  cases i with
  | ofNat n => simpa using hnat n
  | negSucc n =>
      have heq : ((Int.negSucc n : Int) : ZMod N) = -((n + 1 : Nat) : ZMod N) := by
        push_cast
        ring
      rw [heq, centeredAbs, ZMod.natAbs_valMinAbs_neg]
      exact hnat (n + 1)

theorem modular_monomial_of_rational_approximation {N k q : Nat} [NeZero N]
    (a r : ZMod N) (b : Int) (hk : 1 ≤ k) (hq : 0 < q) {T : Real} (hT : 0 < T)
    (happrox : |(-(a * r).valMinAbs : Real) / N - (b : Real) / q| ≤ ((q : Real) * T)⁻¹) :
    let p := centeredAbs r * q
    (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤
      ((N : Real) / T) * (p : Real) ^ (k - 1) := by
  let p := centeredAbs r * q
  let c := (a * r).valMinAbs
  let e0 : Int := -c * q - b * N
  let E : Int := e0 * (p : Int) ^ (k - 1)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hqr : (0 : Real) < q := by exact_mod_cast hq
  have hfraction : (-(a * r).valMinAbs : Real) / N - (b : Real) / q =
      (e0 : Real) / ((N : Real) * q) := by
    dsimp [e0, c]
    push_cast
    field_simp
  have he0 : |(e0 : Real)| ≤ (N : Real) / T := by
    rw [hfraction, abs_div, abs_of_pos (mul_pos hN hqr)] at happrox
    have h := (div_le_iff₀ (mul_pos hN hqr)).mp happrox
    have heq : ((q : Real) * T)⁻¹ * ((N : Real) * q) = (N : Real) / T := by
      field_simp
    exact h.trans_eq heq
  have hE : (E.natAbs : Real) ≤ ((N : Real) / T) * (p : Real) ^ (k - 1) := by
    have heq : (E.natAbs : Real) = |(e0 : Real)| * (p : Real) ^ (k - 1) := by
      have hcast : (E.natAbs : Real) = |(E : Real)| := by
        calc
          _ = ((E.natAbs : Int) : Real) := (Int.cast_natCast E.natAbs).symm
          _ = ((|E| : Int) : Real) := congrArg (fun z : Int => (z : Real))
            (show (E.natAbs : Int) = |E| by rw [Int.abs_eq_natAbs])
          _ = _ := by rw [Int.cast_abs]
      rw [hcast]
      dsimp [E]
      push_cast
      rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : Real) ≤ p)]
    rw [heq]
    exact mul_le_mul_of_nonneg_right he0 (by positivity)
  have hcCast : (c : ZMod N) = a * r := ZMod.coe_valMinAbs _
  have hECast : (E : ZMod N) =
      (-(a * r) * (q : ZMod N)) * (p : ZMod N) ^ (k - 1) := by
    dsimp [E, e0]
    push_cast
    rw [hcCast]
    simp
  have hpCast : (p : ZMod N) = (centeredAbs r : ZMod N) * q := by
    simp only [p, Nat.cast_mul]
  have hpPow : (p : ZMod N) ^ k = (p : ZMod N) ^ (k - 1) * p := by
    calc
      _ = (p : ZMod N) ^ ((k - 1) + 1) := congrArg _ (by omega : k = (k - 1) + 1)
      _ = _ := pow_succ _ _
  have hsign : (centeredAbs r : ZMod N) = r ∨ (centeredAbs r : ZMod N) = -r := by
    have h := ZMod.natCast_natAbs_valMinAbs r
    unfold centeredAbs
    split at h
    · exact Or.inl h
    · exact Or.inr h
  have htarget : ((p : ZMod N) ^ k) * a = (E : ZMod N) ∨
      ((p : ZMod N) ^ k) * a = -(E : ZMod N) := by
    rcases hsign with hs | hs
    · right
      rw [hpPow, hECast, hpCast, hs]
      ring
    · left
      rw [hpPow, hECast, hpCast, hs]
      ring
  have hcenter : centeredAbs (((p : ZMod N) ^ k) * a) ≤ E.natAbs := by
    rcases htarget with h | h
    · rw [h]
      exact recurrence_centeredAbs_intCast_le E
    · rw [h, centeredAbs, ZMod.natAbs_valMinAbs_neg]
      exact recurrence_centeredAbs_intCast_le E
  exact (show (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs by
    exact_mod_cast hcenter).trans hE

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Section05
import GowersSzemeredi.Proofs00Basics

/-! Transfer a rational approximation of a Fourier frequency back to a
small modular monomial. This isolates the integer representative and sign
argument from all analytic Weyl estimates and numerical thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

alias recurrence_centeredAbs_intCast_le := lemma55_centeredAbs_intCast_le

theorem modular_monomial_of_rational_approximation {N k q : Nat} [NeZero N]
    (a r : ZMod N) (b : Int) (hk : 1 ≤ k) (hq : 0 < q) {T : Real} (hT : 0 < T)
    (happrox : |(-(a * r).valMinAbs : Real) / N - (b : Real) / q| ≤ ((q : Real) * T)⁻¹) :
    let p := centeredAbs r * q
    (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤
      ((N : Real) / T) * (p : Real) ^ (k - 1) := by
  intro p
  let e0 : Int := -(a * r).valMinAbs * q - b * N
  let E : Int := e0 * (p : Int) ^ (k - 1)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hqr : (0 : Real) < q := by exact_mod_cast hq
  -- the approximation error is `e0 / (N q)`, so `|e0| ≤ N / T`
  have he0 : |(e0 : Real)| ≤ (N : Real) / T := by
    have h : (-(a * r).valMinAbs : Real) / N - (b : Real) / q = (e0 : Real) / (N * q) := by
      push_cast [e0]
      field_simp
    rw [h, abs_div, abs_of_pos (mul_pos hN hqr), div_le_iff₀ (mul_pos hN hqr)] at happrox
    exact happrox.trans_eq (by field_simp)
  -- in `ZMod N`, `p ^ k a = ∓E` according to the sign of the centered lift of `r`
  have hE : (E : ZMod N) = -(a * r) * q * (p : ZMod N) ^ (k - 1) := by
    simp [E, e0, ZMod.coe_valMinAbs]
  have hP : (p : ZMod N) ^ k = (p : ZMod N) ^ (k - 1) * ((centeredAbs r : ZMod N) * q) := by
    rw [← Nat.cast_mul]
    exact (pow_sub_one_mul (by omega) _).symm
  have hcenter : centeredAbs (((p : ZMod N) ^ k) * a) ≤ E.natAbs := by
    rcases natCast_centeredAbs_eq_or_neg r with hs | hs <;> rw [hP, hs]
    · rw [show (p : ZMod N) ^ (k - 1) * (r * q) * a = -(E : ZMod N) by rw [hE]; ring,
        centeredAbs, ZMod.natAbs_valMinAbs_neg]
      exact recurrence_centeredAbs_intCast_le E
    · rw [show (p : ZMod N) ^ (k - 1) * (-r * q) * a = (E : ZMod N) by rw [hE]; ring]
      exact recurrence_centeredAbs_intCast_le E
  calc (centeredAbs (((p : ZMod N) ^ k) * a) : Real) ≤ E.natAbs := by exact_mod_cast hcenter
    _ = |(e0 : Real)| * (p : Real) ^ (k - 1) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        push_cast [E]
        rw [abs_mul, abs_pow, Nat.abs_cast]
    _ ≤ _ := by gcongr

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs13FejerQuantitative

/-! Choose the even kernel from rho and eta. The modulus threshold is
uniform over all actual densities beta above a prescribed positive delta.
The elementary signal estimate gives an explicit 2^(-1150) mass constant. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_purification_uniform
    (delta rho eta : Real) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ N₀ : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ (U : Finset (Pair N)) (phi : Pair N → ZMod N) (beta : Real), delta ≤ beta →
      (U.card : Real) = beta * (N : Real) ^ 2 →
      rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi →
      ∃ S ⊆ U,
        ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 * beta ^ 15 * (N : Real) ^ 32 ≤
          (respectedArrangementCount 8 S phi : Real) ∧
        (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  have hp : 0 < rho * eta := mul_pos hrho heta
  have hp1 : rho * eta ≤ 1 := by nlinarith only [hrho1, heta1, hrho, heta]
  let A : Real := (2 : Real) ^ 34 / (rho * eta)
  have hA : 1 ≤ A := by
    apply (le_div_iff₀ hp).mpr
    simpa using hp1.trans (by norm_num : (1 : Real) ≤ 2 ^ 34)
  let M : Nat := Nat.ceil A
  have hM : 0 < M := Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hA)
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have hMlo : A ≤ (M : Real) := Nat.le_ceil A
  have hMhi : (M : Real) ≤ (2 : Real) ^ 35 / (rho * eta) := by
    calc
      (M : Real) ≤ A + 1 := (Nat.ceil_lt_add_one (zero_le_one.trans hA)).le
      _ ≤ 2 * A := by linarith only [hA]
      _ = _ := by dsimp [A]; ring
  have hkernel : (2 : Real) ^ 34 ≤ rho * eta * (M : Real) := by
    have ht := (div_le_iff₀ hp).mp hMlo
    nlinarith only [ht]
  let T : Real := (2 : Real) ^ 131 * (M : Real) ^ 63 / (rho * eta * delta ^ 15)
  refine ⟨max (2 * M) (Nat.ceil T), ?_⟩
  intro N _ _ hN U phi beta hdb hcard habundance
  have hbeta : 0 < beta := hdelta.trans_le hdb
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMN : 2 * M ≤ N := (le_max_left _ _).trans hN
  have hT : T ≤ (N : Real) :=
    (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right (2 * M) (Nat.ceil T)).trans hN)
  have hmodulus : (2 : Real) ^ 131 * (M : Real) ^ 63 ≤ rho * eta * beta ^ 15 * (N : Real) := by
    have ht := (div_le_iff₀ (by positivity : (0 : Real) < rho * eta * delta ^ 15)).mp hT
    have hd := pow_le_pow_left₀ hdelta.le hdb 15
    have hd' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hp.le) hn.le
    nlinarith only [ht, hd']
  obtain ⟨S, hS, hmass, hratio⟩ := section13_fejer_purification_even hM hMN U phi beta rho eta
    hbeta hrho heta hcard habundance hkernel hmodulus
  have hinv : rho * eta / (2 : Real) ^ 35 ≤ (M : Real)⁻¹ := by
    have ht := (inv_le_inv₀ (by positivity : (0 : Real) < (2 : Real) ^ 35 / (rho * eta)) hm).mpr hMhi
    simpa only [inv_div] using ht
  have hpow := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ rho * eta / (2 : Real) ^ 35) hinv 31
  have hcoef : ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 ≤
      ((2 : Real) ^ 65)⁻¹ * rho * ((M : Real) ^ 31)⁻¹ := by
    have ht := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : Real) ≤ ((2 : Real) ^ 65)⁻¹ * rho)
    calc
      _ = ((2 : Real) ^ 65)⁻¹ * rho * (rho * eta / (2 : Real) ^ 35) ^ 31 := by
        rw [show (1150 : Nat) = 65 + 35 * 31 from rfl, pow_add, pow_mul]
        ring
      _ ≤ ((2 : Real) ^ 65)⁻¹ * rho * ((M : Real)⁻¹) ^ 31 := ht
      _ = _ := by rw [inv_pow]
  refine ⟨S, hS, ?_, hratio⟩
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
    (by positivity)).trans hmass

end LeanProofs.GowersSzemeredi

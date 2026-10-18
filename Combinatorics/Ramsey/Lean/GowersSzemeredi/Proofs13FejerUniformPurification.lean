import GowersSzemeredi.Proofs13FejerQuantitative

/-! Choose the even kernel from rho and eta. The modulus threshold is
uniform over all actual densities beta above a prescribed positive delta.
The elementary signal estimate gives an explicit 2^(-1150) mass constant.

`section13_fejer_purification_uniform` is in
`Proofs13FejerUniformPurificationSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def fejerPurificationThreshold (delta rho eta : Real) : Nat :=
  let M := Nat.ceil ((2 : Real) ^ 34 / (rho * eta))
  max (2 * M) (Nat.ceil ((2 : Real) ^ 131 * (M : Real) ^ 63 / (rho * eta * delta ^ 15)))

theorem section13_fejer_purification_explicit
    (delta rho eta : Real) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerPurificationThreshold delta rho eta ≤ N →
      ∀ (U : Finset (Pair N)) (phi : Pair N → ZMod N) (beta : Real), delta ≤ beta →
      (U.card : Real) = beta * (N : Real) ^ 2 →
      rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi →
      ∃ S ⊆ U,
        ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 * beta ^ 15 * (N : Real) ^ 32 ≤
          (respectedArrangementCount 8 S phi : Real) ∧
        (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  have hp : 0 < rho * eta := mul_pos hrho heta
  let M : Nat := Nat.ceil ((2 : Real) ^ 34 / (rho * eta))
  have hM : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hhi : ((M : Real) - 1) * (rho * eta) < 2 ^ 34 :=
    (lt_div_iff₀ hp).mp (sub_lt_iff_lt_add.mpr (Nat.ceil_lt_add_one (by positivity)))
  have hMhi : rho * eta * M ≤ 2 ^ 35 := by linarith [mul_le_one₀ hrho1 heta.le heta1]
  intro N _ _ hN U phi beta hdb hcard habundance
  have hbeta := hdelta.trans_le hdb
  have hT : (2 : Real) ^ 131 * (M : Real) ^ 63 / (rho * eta * delta ^ 15) ≤ N :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  rw [div_le_iff₀ (by positivity)] at hT
  have hd := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdelta.le hdb 15)
    (by positivity : (0 : Real) ≤ rho * eta * N)
  obtain ⟨S, hS, hmass, hratio⟩ := section13_fejer_purification_even hM
    ((le_max_left _ _).trans hN) U phi beta rho eta hbeta hrho heta hcard habundance
    ((div_le_iff₀' hp).mp (Nat.le_ceil _)) (by linarith only [hT, hd])
  refine ⟨S, hS, le_trans ?_ hmass, hratio⟩
  gcongr ?_ * _ * _
  rw [le_mul_inv_iff₀ (by positivity), show (1150 : Nat) = 65 + 35 * 31 from rfl, pow_add,
    pow_mul]
  linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMhi 31)
    (by positivity : (0 : Real) ≤ (2 ^ 65 * (2 ^ 35) ^ 31)⁻¹ * rho)]

end LeanProofs.GowersSzemeredi

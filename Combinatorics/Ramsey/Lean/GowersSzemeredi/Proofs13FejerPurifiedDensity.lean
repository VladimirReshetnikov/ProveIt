import GowersSzemeredi.Proofs13FejerUniformPurification

/-! Recover density after purification from the sharp arrangement upper
count. Integer powers give a convenient explicit density bound without
introducing a fifteenth root.

`section13_fejer_density_uniform` is in `Proofs13FejerPurifiedDensitySide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_density_from_mass {N : Nat} [NeZero N]
    (S : Finset (Pair N)) (phi : Pair N → ZMod N)
    (beta rho eta : Real) (hbeta : 0 ≤ beta)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hmass : ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 * beta ^ 15 * (N : Real) ^ 32 ≤
      (respectedArrangementCount 8 S phi : Real)) :
    ((2 : Real) ^ 77)⁻¹ * rho ^ 3 * eta ^ 3 * beta * (N : Real) ^ 2 ≤ (S.card : Real) := by
  let t : Real := ((2 : Real) ^ 77)⁻¹ * rho ^ 3 * eta ^ 3 * beta
  have hc : (((2 : Real) ^ 77)⁻¹) ^ 15 ≤ ((2 : Real) ^ 1150)⁻¹ := by
    rw [inv_pow, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hr : rho ^ 45 ≤ rho ^ 32 := pow_le_pow_of_le_one hrho hrho1 (by decide)
  have he : eta ^ 45 ≤ eta ^ 31 := pow_le_pow_of_le_one heta heta1 (by decide)
  have ht : t ^ 15 ≤ ((2 : Real) ^ 1150)⁻¹ * rho ^ 32 * eta ^ 31 * beta ^ 15 := by
    simp only [t, mul_pow, ← pow_mul]
    gcongr
  have hres : respectedArrangementCount 8 S phi ≤ arrangementCount 8 S := by
    have hp := fejerArrangementEdges_partition_card S (fun R => R.IsRespected phi)
    rw [fejerArrangementEdges_good_card] at hp
    omega
  have hup : (respectedArrangementCount 8 S phi : Real) ≤
      (S.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hres.trans (context_arrangementCount_le_card_pow S)
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine le_of_pow_le_pow_left₀ (n := 15) (by norm_num) (Nat.cast_nonneg _)
    (le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < (N : Real) ^ 2))
  calc (t * (N : Real) ^ 2) ^ 15 * (N : Real) ^ 2 = t ^ 15 * (N : Real) ^ 32 := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right ht (by positivity)).trans (hmass.trans hup)

theorem section13_fejer_density_explicit
    (delta rho eta : Real) (hdelta : 0 < delta)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerPurificationThreshold delta rho eta ≤ N →
      ∀ (U : Finset (Pair N)) (phi : Pair N → ZMod N) (beta : Real), delta ≤ beta →
      (U.card : Real) = beta * (N : Real) ^ 2 →
      rho * beta ^ 15 * (N : Real) ^ 32 ≤ respectedArrangementCount 8 U phi →
      ∃ S ⊆ U,
        ((2 : Real) ^ 77)⁻¹ * rho ^ 3 * eta ^ 3 * beta * (N : Real) ^ 2 ≤ (S.card : Real) ∧
        (1 - eta) * (arrangementCount 8 S : Real) ≤ (respectedArrangementCount 8 S phi : Real) := by
  intro N _ _ hN U phi beta hdb hcard habundance
  obtain ⟨S, hS, hmass, hratio⟩ := section13_fejer_purification_explicit delta rho eta hdelta hrho hrho1 heta heta1 N hN U phi beta hdb hcard habundance
  refine ⟨S, hS, section13_fejer_density_from_mass S phi beta rho eta
    (hdelta.trans_le hdb).le hrho.le hrho1 heta.le heta1 hmass, ?_⟩
  have hg : (0 : Real) ≤ respectedArrangementCount 8 S phi := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr heta1)
  have herror : 0 ≤ eta ^ 2 * (respectedArrangementCount 8 S phi : Real) := mul_nonneg (sq_nonneg _) hg
  nlinarith only [hmul, herror]

end LeanProofs.GowersSzemeredi

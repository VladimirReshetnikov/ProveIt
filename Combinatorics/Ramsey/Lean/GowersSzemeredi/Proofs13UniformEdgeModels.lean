import GowersSzemeredi.Proofs13EdgeDensity

/-! Uniform Bohr models for all strong heights. Actual edge densities vary;
monotonicity permits a common lower density parameter without pretending
that the edge cardinalities equal their lower bound.

`lemma_13_6_from_initial_stages` and `section13_uniform_height_bohr_model` are
in `Proofs13UniformEdgeModelsSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The corrected Bohr radius increases with the density, including the
rounded spectrum parameter and its denominator. -/
theorem section10Zeta_mono {a b : Real} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    section10Zeta a ≤ section10Zeta b := by
  have hbpos : 0 < b := ha.trans_le hab
  have hkb : 0 < section10SpectrumParameter b := by
    apply Nat.ceil_pos.mpr
    unfold section10SpectrumBound
    positivity
  have hk : section10SpectrumParameter b ≤ section10SpectrumParameter a := by
    apply Nat.ceil_mono
    unfold section10SpectrumBound
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hab (by norm_num)) (by positivity)
  have hkReal : (section10SpectrumParameter b : Real) ≤ section10SpectrumParameter a :=
    by exact_mod_cast hk
  have hp : a ^ (18 * section10SpectrumParameter a) ≤
      b ^ (18 * section10SpectrumParameter b) := by
    calc
      _ ≤ b ^ (18 * section10SpectrumParameter a) := pow_le_pow_left₀ ha.le hab _
      _ ≤ _ := pow_le_pow_of_le_one hbpos.le hb (Nat.mul_le_mul_left 18 hk)
  have htwo : (2 : Real) ^ (-(155 : Real) * section10SpectrumParameter a) ≤
      (2 : Real) ^ (-(155 : Real) * section10SpectrumParameter b) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  unfold section10Zeta
  apply div_le_div₀
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (pow_nonneg hbpos.le _))
    (mul_le_mul htwo hp (pow_nonneg ha.le _) (Real.rpow_nonneg (by norm_num) _))
    (by exact_mod_cast hkb) hkReal

/-- More frequencies and a smaller radius give a smaller Bohr domain. -/
theorem bohr_domain_mono {N : Nat} [NeZero N] {K L : Finset (ZMod N)} {r s : Real}
    (hK : K ⊆ L) (hrs : r ≤ s) : bohr L r ⊆ bohr K s := by
  intro d hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k hk
  exact ((Finset.mem_filter.mp hd).2 k (hK hk)).trans
    (mul_le_mul_of_nonneg_right hrs (Nat.cast_nonneg _))

/-- Restrict a Bohr difference model to any smaller Bohr domain. -/
theorem bohr_difference_model_restrict {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (K L : Finset (ZMod N)) (r s : Real) (Y : Finset X) (psi : ZMod N → ZMod N)
    (hmodel : HasBohrDifferenceModel D phi K r Y psi)
    (hsub : bohr L s ⊆ bohr K r) : HasBohrDifferenceModel D phi L s Y psi := by
  refine ⟨IsAddFreimanHom.subset hsub hmodel.1 (Set.mapsTo_univ _ _), ?_⟩
  intro v hv w hw hdiff
  exact hmodel.2 v hv w hw (hsub hdiff)

end LeanProofs.GowersSzemeredi

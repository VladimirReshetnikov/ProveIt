import GowersSzemeredi.Proofs16CommonBohrParameters
import GowersSzemeredi.Proofs16ProperBohrProgression

/-! Uniform size bounds for the proper progression used to localize
common difference maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def bohrProgressionDensity (r : Nat) (rho : Real) : Real :=
  Real.exp (-(((r : Real)+1)*Real.log (1+rho⁻¹)+10*((r : Real)+1)^2))

def commonDifferenceProgressionDensity (kappa : Real) : Real :=
  bohrProgressionDensity (commonDifferenceRank kappa) (commonDifferenceRadius kappa)

def commonDifferenceProgressionRetention (kappa : Real) : Real :=
  commonDifferenceProgressionDensity kappa*commonDifferenceBohrDensity kappa

theorem bohrProgressionDensity_pos (r : Nat) (rho : Real) :
    0 < bohrProgressionDensity r rho := Real.exp_pos _

theorem commonDifferenceProgressionDensity_pos (kappa : Real) :
    0 < commonDifferenceProgressionDensity kappa := Real.exp_pos _

theorem commonDifferenceProgressionRetention_pos {kappa : Real} (hk : 0 < kappa) :
    0 < commonDifferenceProgressionRetention kappa :=
  mul_pos (commonDifferenceProgressionDensity_pos kappa) (commonDifferenceBohrDensity_pos hk)

/-- Replace the actual spectrum cardinality by any uniform rank bound
without weakening the progression's properness or neighborhood inclusion. -/
theorem exists_uniform_proper_progression_in_bohr {N r : Nat} [NeZero N]
    (Gamma : Finset (ZMod N)) {rho : Real} (hrho : 0 < rho) (hG : Gamma.card ≤ r) :
    ∃ P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      P.rank ≤ r+1 ∧ P.Proper ∧ P.carrier ⊆ bohr Gamma (rho/4) ∧
      bohrProgressionDensity r rho*N ≤ (P.carrier.card : Real) := by
  obtain ⟨hw,hwidth⟩ := logarithmic_bohr_width hrho
  obtain ⟨P,hPrank,hPproper,hPsub,hPcard⟩ := exists_proper_progression_in_bohr Gamma hrho hw hwidth
  have hGR : (Gamma.card : Real) ≤ r := by exact_mod_cast hG
  have he : bohrProgressionDensity r rho ≤
      Real.exp (-(((Gamma.card : Real)+1)*Real.log (1+rho⁻¹)+10*((Gamma.card : Real)+1)^2)) := by
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_right (show (Gamma.card : Real)+1 ≤ r+1 by linarith) hw
    have hsq : ((Gamma.card : Real)+1)^2 ≤ ((r : Real)+1)^2 := by
      nlinarith [Nat.cast_nonneg Gamma.card (α := Real), Nat.cast_nonneg r (α := Real)]
    linarith
  exact ⟨P,hPrank.trans (Nat.add_le_add_right hG 1),hPproper,hPsub,
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hPcard⟩

end LeanProofs.GowersSzemeredi

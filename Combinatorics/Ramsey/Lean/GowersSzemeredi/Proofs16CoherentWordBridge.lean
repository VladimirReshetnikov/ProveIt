import GowersSzemeredi.Proofs16CoherentWordFamily
import GowersSzemeredi.Proofs16CoherentWordMonomials
import GowersSzemeredi.Proofs16CoherentMonomialAccuracy

/-! A fully specified bridge accuracy produces all compatible words up
to the requested length at the actual retained density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentWordBridgePower (K : Nat) : Nat := 20+4*coherentWordExponent K

def coherentWordBridgeScale (K : Nat) : Real := coherentRichBridgeScale (coherentWordCoefficient K/2)

theorem coherentWordBridgeScale_pos (K : Nat) : 0 < coherentWordBridgeScale K :=
  coherentRichBridgeScale_pos (div_pos (coherentWordCoefficient_pos K) (by norm_num))

theorem CoherentBridgeSystem.word_family {N ell depth : Nat} [NeZero N] [Fact N.Prime]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} {Q : Finset (Fin 4 → ZMod N)} (K : Nat)
    (h : CoherentBridgeSystem B X theta F sigma
      (kappa^(coherentWordBridgePower K)/coherentWordBridgeScale K) depth)
    (hdepth : 3 ≤ depth) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hk : 0 < kappa) (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 2 < N) :
    HasCoherentWordFamily X B theta F sigma kappa K := by
  have hk1 := hfamily.density_le_one hmass
  have hb : 0 < coherentWordCoefficient K/2 := by have hp := coherentWordCoefficient_pos K; positivity
  have hs := coherentWordBridgeScale_pos K
  have hbeta : coherentWordDensity kappa K/2 = (coherentWordCoefficient K/2)*kappa^(coherentWordExponent K) := by
    rw [coherentWordDensity_monomial]
    ring
  have hsmall := coherent_monomial_pair_bound hb hk.le hk1 (coherentWordExponent K)
  have herror : 4*(kappa^(coherentWordBridgePower K)/coherentWordBridgeScale K) <
      ((coherentWordDensity kappa K/2)^2*coherentRobustWalkDensity kappa)^2 := by
    rw [hbeta]
    exact coherent_monomial_error_bound hb hk (coherentWordExponent K)
  have hr := h.rich_set (by positivity) hdepth hfamily hk hmass hsmall
    (by have hp := coherentWordDensity_pos hk K; positivity) herror hN
  exact hr.word_family K hk hk1

end LeanProofs.GowersSzemeredi

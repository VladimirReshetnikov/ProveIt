import IPRADerivations.Analysis.Polynomials.GridSums.RationalPolynomialGridSum
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.DiscreteIdentities.GaussianStirlingAllOrderPanelDerivative

/-!
# Readback of the literal centered Bernoulli samples

Removing the Bernoulli constant coefficient gives exactly the
original centered sampler, including its factorial and sign.
The actual finite fold therefore has the cleared power-sum readback.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGridMean

open_ipra
open BernoulliBounds (bden bden_pos bint pv toZ_zint)
open GaussianStirlingAllOrderBernoulliMesh (lower_endpoint_value)
open GaussianStirlingAllOrderCenteredBernoulli (sample numerator denominator factor sample_value sample_canonical)
open RationalFiniteSum (term canonical_equal)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficients (m : ℕ) (i : Fin (2*m+1)) : ℤ :=
  if i = 0 then 0 else factor m * bint (2*m) i

def body (m : ℕ) : PTm 2 := RationalPolynomialGridSum.body (coefficients m) (bden (2*m))

private theorem centered_numerator (m : ℕ) (i M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (pv (coefficients m) i M) (numerator m i M) := by
  have atZero := ZT.toZ_eq (lower_endpoint_value (Γ := Γ) (2*m) M)
  simp only [ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat] at atZero
  have wp : Groth.ι (Q.mk Γ (pw i (num 0))) = 1 := by
    simpa using AnalyticNumberTheory.RobinThreePos.pw_lit (Γ := Γ) i 0
  apply ZT.derive
  simp only [numerator,ZT.toZ_mul,ZT.toZ_sub,toZ_zint,atZero]
  simp only [pv,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp [coefficients,wp,_root_.mul_assoc,← Finset.mul_sum]

theorem body_at (m : ℕ) (i M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] term (body m) i M ≐ sample m i M := by
  rw [body,RationalPolynomialGridSum.body_at]
  have h := GaussianStirlingAllOrderCenteredBernoulli.denominator_positive m M hM
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ h) (sample_canonical m i M hM)
    (normalize_preserves_value _ _ h) (sample_value m i M hM) h h
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_eq (centered_numerator (Γ := Γ) m i M)]

theorem actual_original_centered_Bernoulli_grid_readback_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 1) ⟶ term (body m) (var 0) (var 1) ≐ sample m (var 0) (var 1)) :=
  closeUniv 2 (.impI (body_at m _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliGridMean

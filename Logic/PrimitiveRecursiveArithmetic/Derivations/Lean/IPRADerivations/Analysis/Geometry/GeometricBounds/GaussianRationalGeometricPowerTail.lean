import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalReciprocal
import IPRADerivations.Analysis.Polynomials.Coefficients.NamedCoefficients.GaussianCoefficientNameBounds

/-!
# A linear denominator bound for a contractive rational power

The cleared internal inequality is
`B^N(B+NC) ≤ (B+C)^N B`. It gives a rational tail bound even
when the contraction margin is a variable in the object theory.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianRationalGeometricPowerTail

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalReciprocal (power bounded_power)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def law (B C N : PTm n) : Fm PTm n :=
  le (pw B N*(B+N*C)) (B*pw (B+C) N)

ipra_subst law [pw]

private theorem base (B C : PTm n) : Γ ⊢[PRAAx] law B C zero := by
  change Γ ⊢[PRAAx] le (pw B zero*(B+zero*C)) (B*pw (B+C) zero)
  exact le_congr ((congrMul (pw_zero B) (by ipra_ring)).eqTrans (one_mul B)).eqSymm
    ((congrMul (.eqRefl B) (pw_zero (B+C))).eqTrans (mul_comm B one |>.eqTrans (one_mul B))).eqSymm
    (le_refl B)

private theorem step (B C N : PTm n) (h : Γ ⊢[PRAAx] law B C N) : Γ ⊢[PRAAx] law B C (succ N) := by
  have g : Γ ⊢[PRAAx] le (B*(B+succ N*C)) ((B+N*C)*(B+C)) :=
    le_of_eq_add (d := N*C*C) (by ipra_ring)
  have first := mul_le_mul_right (pw B N) g
  have second := mul_le_mul_right (B+C) h
  change Γ ⊢[PRAAx] le (pw B (succ N)*(B+succ N*C)) (B*pw (B+C) (succ N))
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] B*(B+succ N*C)*pw B N ≐ (pw B N*B)*(B+succ N*C)).eqTrans
      (congrMul (pw_succ B N).eqSymm (.eqRefl _)))
    ((by ipra_ring : Γ ⊢[PRAAx] B*pw (B+C) N*(B+C) ≐ B*(pw (B+C) N*(B+C))).eqTrans
      (congrMul (.eqRefl B) (pw_succ (B+C) N).eqSymm))
    (le_trans first (le_congr (by ipra_ring) (.eqRefl _) second))

theorem finite (B C N : PTm n) : Γ ⊢[PRAAx] law B C N := by
  have h : Γ ⊢[PRAAx] .all (law (Syn.shift B) (Syn.shift C) (var 0)) := by
    ipra_qfind (le_QF _ _) [subst_law]
    · exact base B C
    · exact step _ _ _ Prf.hyp0
  ipra_simpa_inst [subst_law] using h.allE N

theorem power_tail (q B C N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] bounded q B (B+C)) : Γ ⊢[PRAAx]
    bounded (power q N) B (B+N*C) := by
  have hd := le_trans hB (le_add_right B C)
  exact bounded_radius_mono _ _ _ _ _
    (GaussianPolynomialPerturbation.power_positive _ _ hd) (le_trans hB (le_add_right B (N*C)))
    (finite B C N) (bounded_power q B (B+C) N hd hq)

theorem actual_rational_geometric_power_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ bounded (var 0) (var 1) (var 1+var 2)) ⟶
      bounded (power (var 0) (var 3)) (var 1) (var 1+var 3*var 2)) :=
  closeUniv 4 (.impI (power_tail _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalGeometricPowerTail

import IPRADerivations.Analysis.Polynomials.Representation.RationalPolynomialDegreeGaussianEmbedding

/-!
# Nonvanishing of the original rational coefficient scan

The actual flag succeeds exactly when a bounded original coefficient
has nonzero rational value. Its first returned index is a witness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialNonvanishing

open_ipra
open RationalGaussianEmbedding (scalarZero scalar_recode_zero scalar_recode_equal)
open RationalPolynomialDegreeGaussianEmbedding (first flag first_bound first_nonzero first_from_witness)
open RationalArgmin (rationalEq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nonzeroCoefficients (C N : PTm n) : Fm PTm n := .ex
  (lt (var 0) (succ (Syn.shift N)) ⋏ neg (rationalEq (entry (Syn.shift C) (var 0)) scalarZero))

ipra_subst nonzeroCoefficients [Syn.subst_shift, Syn.shift_subst, neg]

private theorem flag_of_found (C N : PTm n) (h : Γ ⊢[PRAAx] lt (first C N) (succ N)) :
    Γ ⊢[PRAAx] flag C N ≐ one := AnalyticNumberTheory.Totatives.sg_lt h

theorem found_of_flag (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) :
    Γ ⊢[PRAAx] lt (first C N) (succ N) := by
  refine .orE (lt_or_eq_of_le (first_bound C N)) Prf.hyp0 ?_
  have fail := AnalyticNumberTheory.Totatives.sg_le
    (le_congr (.eqRefl _) (Prf.hyp0 : (first C N ≐ succ N) :: Γ ⊢[PRAAx] first C N ≐ succ N).eqSymm (le_refl (succ N)))
  exact .botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans fail))

theorem selected_nonzero (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) :
    Γ ⊢[PRAAx] lt (first C N) (succ N) ⋏ neg (rationalEq (entry C (first C N)) scalarZero) := by
  have within := found_of_flag C N h
  exact .andI within (.impI (.impE (first_nonzero C N within).wk
    ((scalar_recode_equal _ _ Prf.hyp0).eqTrans scalar_recode_zero)))

theorem nonzero_of_flag (C N : PTm n) (h : Γ ⊢[PRAAx] flag C N ≐ one) :
    Γ ⊢[PRAAx] nonzeroCoefficients C N := by
  refine .exI (first C N) ?_
  simpa [nonzeroCoefficients,neg] using selected_nonzero C N h

theorem flag_of_nonzero (C N : PTm n) (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) :
    Γ ⊢[PRAAx] flag C N ≐ one := by
  refine .exE h ?_
  let P := Syn.shift C
  let M := Syn.shift N
  let Δ := (lt (var 0) (succ M) ⋏ neg (rationalEq (entry P (var 0)) scalarZero)) :: Γ.map Fm.shift
  have witness : Δ ⊢[PRAAx] lt (var 0) (succ M) ⋏ neg (rationalEq (entry P (var 0)) scalarZero) := Prf.hyp0
  have hne : Δ ⊢[PRAAx] neg (RationalArithmetic.recode (entry P (var 0)) ≐ scalarZero) :=
    .impI (.impE (Prf.andE₂ witness).wk
      (RationalGaussianEmbedding.rational_equal_of_scalar_recode _ _ (Prf.hyp0.eqTrans scalar_recode_zero.eqSymm)))
  have earliest := first_from_witness P M (var 0) (.andE₁ witness) hne
  simpa [Δ,P,M,Fm.shift,Syn.shift,one] using flag_of_found P M (lt_of_le_of_lt earliest (.andE₁ witness))

theorem flag_iff_nonzero (C N : PTm n) : Γ ⊢[PRAAx] Fm.iff (flag C N ≐ one) (nonzeroCoefficients C N) :=
  .andI (.impI (nonzero_of_flag _ _ Prf.hyp0)) (.impI (flag_of_nonzero _ _ Prf.hyp0))

theorem actual_rational_nonzero_scan_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (flag (var 0) (var 1) ≐ one) (nonzeroCoefficients (var 0) (var 1))) :=
  closeUniv 2 (flag_iff_nonzero _ _)

theorem actual_rational_nonzero_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (flag (var 0) (var 1) ≐ one ⟶
      lt (first (var 0) (var 1)) (succ (var 1)) ⋏ neg (rationalEq (entry (var 0) (first (var 0) (var 1))) scalarZero)) :=
  closeUniv 2 (.impI (selected_nonzero _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPolynomialNonvanishing

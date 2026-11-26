import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminantNorm
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Uniform entry bounds for actual coefficient norms

A genuine guarded numerical QF induction accumulates bounds on the
actual component L1 norms. Budgets may be arbitrary rational codes;
the original finite norm and exact natural scaling are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientUniformNorm

open_ipra
open GaussianCoefficientL1 (prefixNorm coefficientNorm)
open GaussianRationalL1 (qL1)
open GaussianRationalSyntheticBounds (natCode add_monotone)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def entryBounds (C N E : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ rationalLE (qL1 (entry (Syn.shift C) (var 0))) (Syn.shift E))
ipra_subst entryBounds [Syn.subst_shift, Syn.shift_subst]
theorem entry_at (C N E i : PTm n) (h : Γ ⊢[PRAAx] entryBounds C N E) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry C i)) E := by
  have gate : Γ ⊢[PRAAx] lt i N ⟶ rationalLE (qL1 (entry C i)) E := by simpa [entryBounds] using h.allE i
  exact Prf.impE gate hi

def prefixLaw (C N E j : PTm n) : Fm PTm n := le j N ⟶ rationalLE (prefixNorm C j) (multiply (natCode j) E)
ipra_subst prefixLaw

theorem prefix_step (C N E j : PTm n) (h : Γ ⊢[PRAAx] entryBounds C N E)
    (ih : Γ ⊢[PRAAx] prefixLaw C N E j) : Γ ⊢[PRAAx] prefixLaw C N E (succ j) := by
  refine .impI ?_
  have previous := Prf.impE ih.wk (le_trans (le_succ_self j) (Prf.hyp0 : le (succ j) N :: Γ ⊢[PRAAx] _))
  exact RationalArgmin.rationalLE_congr (GaussianCoefficientL1.prefix_succ C j).eqSymm
    (GaussianPolynomialDeterminantNorm.natural_scale_succ j E)
      (add_monotone _ _ _ _ previous (entry_at C N E j h.wk Prf.hyp0))

theorem prefix_uniform (C N E : PTm n) (h : Γ ⊢[PRAAx] entryBounds C N E) : Γ ⊢[PRAAx]
    rationalLE (prefixNorm C N) (multiply (natCode N) E) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entryBounds (Syn.shift C) (Syn.shift N) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift N) (Syn.shift E) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixLaw]
    · exact .impI (RationalArgmin.rationalLE_congr
        ((GaussianCoefficientL1.prefix_zero _).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm).eqSymm
        (GaussianPolynomialDeterminantNorm.natural_scale_zero _).eqSymm (RationalArgmin.reflexive _))
    · exact prefix_step _ _ _ _ hs.wk Prf.hyp0
  have gate : Γ ⊢[PRAAx] prefixLaw C N E N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact Prf.impE gate (le_refl N)

theorem coefficient_uniform (C N E : PTm n) (hL : Γ ⊢[PRAAx] length C ≐ N)
    (h : Γ ⊢[PRAAx] entryBounds C N E) : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (multiply (natCode N) E) :=
  RationalArgmin.rationalLE_congr (GaussianRationalLinearProduct.norm_length C N hL).eqSymm (.eqRefl _) (prefix_uniform C N E h)

theorem actual_uniform_coefficient_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ var 1 ⟶ entryBounds (var 0) (var 1) (var 2) ⟶
      rationalLE (coefficientNorm (var 0)) (multiply (natCode (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (coefficient_uniform _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCoefficientUniformNorm

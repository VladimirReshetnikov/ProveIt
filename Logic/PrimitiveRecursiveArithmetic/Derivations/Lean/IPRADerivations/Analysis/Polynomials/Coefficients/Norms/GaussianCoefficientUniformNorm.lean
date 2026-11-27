import IPRADerivations.Analysis.Polynomials.Determinants.ErrorBounds.GaussianPolynomialDeterminantNorm
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormOrder
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers

/-!
# Uniform entry bounds for actual coefficient norms

A genuine guarded numerical QF induction accumulates bounds on the
actual component L1 norms. Budgets may be arbitrary rational codes;
the original finite norm and exact natural scaling are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientUniformNorm

open_ipra
open GaussianCoefficientL1 (prefixNorm coefficientNorm subCoefficients sub_lookup qL1_congr)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalL1Algebra (qL1_of_bounded)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRationalL1 (qL1)
open GaussianRationalSyntheticBounds (natCode add_monotone)
open RationalArithmetic (multiply)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

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

/-- A common Euclidean bound at each degree bounds the L1 norm of the
difference of two descending coefficient buffers. -/
theorem difference_uniform_of_degree_bounds (C D N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (bounds :
      let sh (v : PTm n) := Syn.shift v
      let Δ := lt (var 0) (sh (succ N)) :: Γ.map Fm.shift
      ∀ e : PTm (n+1), (Δ ⊢[PRAAx] le e (sh N)) →
        (Δ ⊢[PRAAx] distanceBounded (entry (sh C) (monus (sh N) e))
          (entry (sh D) (monus (sh N) e)) (sh A) (sh B))) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D (succ N)))
      (fraction (succ N*(two*A)) B) := by
  have rows : Γ ⊢[PRAAx] entryBounds (subCoefficients C D (succ N)) (succ N) (fraction (two*A) B) := by
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh (succ N)) :: Γ.map Fm.shift
    let e := monus (sh N) i
    have hi : Δ ⊢[PRAAx] lt i (succ (sh N)) := by
      simpa [Δ,sh,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh (succ N)))
    have hb : Δ ⊢[PRAAx] le one (sh B) := by
      simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
    have slot := Common.monus_monus_of_le ((succ_monus_succ i (sh N)).eqSymm.eqTrans hi)
    have code := (sub_lookup (sh C) (sh D) (succ (sh N)) i hi).eqTrans
      (qsub_congr (entry_congr (.eqRefl _) slot.eqSymm) (entry_congr (.eqRefl _) slot.eqSymm))
    have norm := qL1_of_bounded _ (sh A) (sh B) hb (bounds e (Common.monus_le_self _ _))
    simpa [entryBounds,Δ,sh,e,i,Syn.shift,fraction,one,two] using
      rationalLE_congr (qL1_congr code).eqSymm (.eqRefl _) norm
  have norm := coefficient_uniform _ (succ N) _ (GaussianCoefficientL1.zip_length _ _ _ _) rows
  have exactBudget := (RationalNonnegativePowers.fraction_multiply (succ N) one (two*A) B (le_refl one) hB).eqTrans
    (RationalNonnegativePowers.fraction_congr (.eqRefl _) (one_mul B))
  exact rationalLE_congr (.eqRefl _) exactBudget norm

theorem actual_uniform_coefficient_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ var 1 ⟶ entryBounds (var 0) (var 1) (var 2) ⟶
      rationalLE (coefficientNorm (var 0)) (multiply (natCode (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (coefficient_uniform _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCoefficientUniformNorm

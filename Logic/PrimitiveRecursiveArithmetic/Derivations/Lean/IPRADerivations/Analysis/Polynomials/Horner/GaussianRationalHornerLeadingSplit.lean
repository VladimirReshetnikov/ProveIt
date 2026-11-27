import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDegree
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Split the leading monomial from the original Gaussian Horner evaluator

The degree is an encoded input. Removing the first stored coefficient
leaves the exact Horner evaluator of the lower-degree suffix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalHornerLeadingSplit

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length)
open GaussianRationalHorner (evaluate horner hornerF horner_zero horner_succ qadd qmul)
open GaussianRationalPolynomialDegree (canonicalTail tail_length tail_lookup)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalSyntheticCoefficientValues (qadd_recode_right qmul_recode_left)
open GaussianRationalSyntheticDivision (first_prefix qadd_congr qmul_congr)
open GaussianReciprocalHorner (qadd_zero_right qmul_associative qmul_one_right)
open GaussianTranslatedNonconstant (recode recode_canonical)
open GaussianRationalPolynomialBuffers renaming distribute_right → multiply_added

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leadingTerm (C w j : PTm n) : PTm n := qmul (entry C zero) (power w j)

def lowerCoefficients (C j : PTm n) : PTm n := canonicalTail C one j

@[simp] theorem subst_leadingTerm {m : ℕ} (σ : Fin n → PTm m) (C w j : PTm n) :
    Syn.subst σ (leadingTerm C w j) = leadingTerm (Syn.subst σ C) (Syn.subst σ w) (Syn.subst σ j) :=
  by simp [leadingTerm]

@[simp] theorem subst_lowerCoefficients {m : ℕ} (σ : Fin n → PTm m) (C j : PTm n) :
    Syn.subst σ (lowerCoefficients C j) = lowerCoefficients (Syn.subst σ C) (Syn.subst σ j) :=
  by simp [lowerCoefficients,one]

theorem lower_length (C j : PTm n) : Γ ⊢[PRAAx] length (lowerCoefficients C j) ≐ j :=
  tail_length _ _ _

theorem lower_at (C j i : PTm n) (hi : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] entry (lowerCoefficients C j) i ≐ recode (entry C (succ i)) :=
  (tail_lookup _ _ _ _ hi).eqTrans (GaussianTranslatedNonconstant.recode_congr
    (entry_congr (.eqRefl _) (by ipra_ring)))

private theorem leading_succ (C w j : PTm n) :
    Γ ⊢[PRAAx] qmul (leadingTerm C w j) w ≐ leadingTerm C w (succ j) :=
  (qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) (power_succ _ _).eqSymm)

private def splitLaw (C w N j : PTm n) : Fm PTm n :=
  le j N ⟶ horner C w (succ j) ≐ qadd (leadingTerm C w j) (horner (lowerCoefficients C N) w j)

@[simp] private theorem subst_splitLaw {m : ℕ} (σ : Fin n → PTm m) (C w N j : PTm n) :
    (splitLaw C w N j).subst σ = splitLaw (Syn.subst σ C) (Syn.subst σ w) (Syn.subst σ N) (Syn.subst σ j) :=
  by simp [splitLaw]

private theorem split_zero (C w N : PTm n) :
    Γ ⊢[PRAAx] horner C w (succ zero) ≐ qadd (leadingTerm C w zero) (horner (lowerCoefficients C N) w zero) := by
  let a := entry C zero
  have leading : Γ ⊢[PRAAx] leadingTerm C w zero ≐ recode a :=
    (qmul_congr (.eqRefl _) (power_zero w)).eqTrans
      ((qmul_recode_left a _).eqSymm.eqTrans (qmul_one_right _ (recode_canonical a)))
  exact (first_prefix C w).eqTrans
    (((qadd_congr leading (horner_zero _ _)).eqTrans (qadd_zero_right _ (recode_canonical a))).eqSymm)

private theorem split_step (C w N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ih : Γ ⊢[PRAAx] horner C w (succ j) ≐ qadd (leadingTerm C w j) (horner (lowerCoefficients C N) w j)) :
    Γ ⊢[PRAAx] horner C w (succ (succ j)) ≐ qadd (leadingTerm C w (succ j)) (horner (lowerCoefficients C N) w (succ j)) := by
  let a := leadingTerm C w j
  let b := horner (lowerCoefficients C N) w j
  let c := entry C (succ j)
  have expandLower : Γ ⊢[PRAAx] horner (lowerCoefficients C N) w (succ j) ≐ qadd (qmul b w) c :=
    (horner_succ _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) (lower_at C N j hj)).eqTrans (qadd_recode_right _ _))
  exact (horner_succ C w (succ j)).eqTrans
    ((qadd_congr ((qmul_congr ih (.eqRefl _)).eqTrans (multiply_added a b w)) (.eqRefl _)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative (qmul a w) (qmul b w) c).eqTrans
        (qadd_congr (leading_succ C w j) expandLower.eqSymm)))

theorem prefix_split (C w N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] horner C w (succ j) ≐ qadd (leadingTerm C w j) (horner (lowerCoefficients C N) w j) := by
  let a (t : PTm n) := Syn.shift t
  have all : Γ ⊢[PRAAx] .all (splitLaw (a C) (a w) (a N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [a,subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (split_zero C w N).wk
    · simp only [a,subst_splitLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact split_step _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have current : Γ ⊢[PRAAx] splitLaw C w N j := by
    simpa only [a,subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE current hj

theorem evaluation_split (C w N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] evaluate C w ≐ qadd (leadingTerm C w N) (evaluate (lowerCoefficients C N) w) :=
  (congrAp3 hornerF hC (.eqRefl _) (.eqRefl _)).eqTrans
    ((prefix_split C w N N (le_refl _)).eqTrans
      (qadd_congr (.eqRefl _) (congrAp3 hornerF (lower_length C N).eqSymm (.eqRefl _) (.eqRefl _))))

theorem actual_Gaussian_Horner_leading_monomial_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let C := var 0
     let w := var 1
     let N := var 2
     length C ≐ succ N ⟶ evaluate C w ≐ qadd (leadingTerm C w N) (evaluate (lowerCoefficients C N) w)) :=
  closeUniv 3 (.impI (evaluation_split _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalHornerLeadingSplit

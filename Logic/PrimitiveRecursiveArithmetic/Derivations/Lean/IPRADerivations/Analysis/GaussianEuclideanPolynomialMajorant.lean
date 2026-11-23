import IPRADerivations.Analysis.GaussianRationalSumMajorant
import IPRADerivations.Analysis.GaussianCoefficientNormEntries
import IPRADerivations.Analysis.RationalSumLinearity
import IPRADerivations.Analysis.GaussianRationalSumSegments

/-!
# Euclidean coefficient majorants for the actual Horner sum at one

The original Gaussian finite sum and scalar finite sum are used throughout.
Complex factors are bounded in Euclidean norm; only the scalar coefficient
weights are added. This avoids replacing a Euclidean budget by an L1 budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanPolynomialMajorant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul horner)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open GaussianRationalSumMajorant (majorized majorized_congr)
open GaussianRationalL1 (qL1)
open GaussianCoefficientL1 (normBody prefixNorm)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianPositiveRealArithmetic (sign numerator natural_representation)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An arbitrary raw Gaussian code is majorized by its actual scalar L1 norm. -/
theorem l1_majorized (q : PTm n) : Γ ⊢[PRAAx] majorized q (qL1 q) := by
  let r := qL1 q
  let D := denominatorOf r
  let A := numerator r
  have hD : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive r
  have hs : Γ ⊢[PRAAx] sign r := GaussianRationalL1.qL1_nonnegative q
  have comparison : Γ ⊢[PRAAx] RationalArgmin.rationalLE r (fraction A D) :=
    GaussianRationalMetric.comparison_of_cleared _ _ A A D D hD hD
      (natural_representation r hs) (fraction_represents A D hD) (le_of_eq_add (d := zero) (by ipra_ring))
  exact GaussianRationalSumMajorant.from_representation q r A D hD hs
    (natural_representation r hs) (GaussianCoefficientNormEntries.l1_to_euclidean q A D hD comparison)

def entryBody : PTm 2 := Foundations.MasterCertificate.entry (var 1) (var 0)

theorem entry_at (C i : PTm n) : Γ ⊢[PRAAx]
    inst2 entryBody i C ≐ Foundations.MasterCertificate.entry C i := by
  simp only [entryBody,inst2,Foundations.MasterCertificate.subst_entry,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact .eqRefl _

def sumLaw (C j : PTm n) : Fm PTm n :=
  horner C qone j ≐ GaussianRationalFiniteSum.sum entryBody j C

@[simp] theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (C j : PTm n) :
    (sumLaw C j).subst σ = sumLaw (Syn.subst σ C) (Syn.subst σ j) := by simp [sumLaw]

/-- Genuine QF induction compares two existing sums, with no list-shape guard. -/
theorem horner_sum (C j : PTm n) : Γ ⊢[PRAAx]
    horner C qone j ≐ GaussianRationalFiniteSum.sum entryBody j C := by
  have all : Γ ⊢[PRAAx] .all (sumLaw (Syn.shift C) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (GaussianRationalHorner.horner_zero C qone).eqTrans (GaussianRationalFiniteSum.sum_zero entryBody C).eqSymm
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (GaussianRationalSumSegments.prefix_succ (Syn.shift C) (var 0)).eqTrans
        ((qadd_congr Prf.hyp0 (entry_at (Syn.shift C) (var 0)).eqSymm).eqTrans
          (GaussianRationalFiniteSum.sum_succ entryBody (var 0) (Syn.shift C)).eqSymm)
  change Γ ⊢[PRAAx] sumLaw C j
  simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

def entriesMajorized (C D c T : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift T) ⟶ majorized (Foundations.MasterCertificate.entry (Syn.shift C) (var 0))
    (RationalArithmetic.multiply (Syn.shift c) (qL1 (Foundations.MasterCertificate.entry (Syn.shift D) (var 0)))))

@[simp] theorem subst_entriesMajorized {m : ℕ} (σ : Fin n → PTm m) (C D c T : PTm n) :
    (entriesMajorized C D c T).subst σ = entriesMajorized (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ c) (Syn.subst σ T) := by
  simp [entriesMajorized,Syn.subst_shift,Syn.shift_subst]

theorem horner_majorized (C D c T : PTm n) (h : Γ ⊢[PRAAx] entriesMajorized C D c T) : Γ ⊢[PRAAx]
    majorized (horner C qone T) (RationalArithmetic.multiply c (prefixNorm D T)) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalSumMajorant.termsMajorized entryBody
      (RationalSumLinearity.scaledBody normBody) T C (pairT c D) := by
    refine .allI (.impI ?_)
    have actual : Γ.map Fm.shift ⊢[PRAAx] entriesMajorized (Syn.shift C) (Syn.shift D) (Syn.shift c) (Syn.shift T) := by
      simpa [Fm.shift,Syn.shift] using h.shift
    have rule : Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (Syn.shift T) ⟶
        majorized (Foundations.MasterCertificate.entry (Syn.shift C) (var 0))
          (RationalArithmetic.multiply (Syn.shift c) (qL1 (Foundations.MasterCertificate.entry (Syn.shift D) (var 0)))) := by
      simpa [entriesMajorized] using actual.allE (var 0)
    have row := Prf.impE rule.wk (Prf.hyp0 (Γ := Γ.map Fm.shift))
    have scaled := majorized_congr (entry_at (Syn.shift C) (var 0)).eqSymm
      (RationalSumLinearity.scaled_term normBody (var 0) (Syn.shift c) (Syn.shift D)).eqSymm
      (by simpa only [GaussianCoefficientL1.norm_body_at] using row)
    simpa only [RationalFiniteSum.term,Syn.shift,subst_pairT] using scaled
  exact majorized_congr (horner_sum C T).eqSymm (RationalSumLinearity.sum_homogeneous normBody T c D)
    (GaussianRationalSumMajorant.sum_majorized entryBody (RationalSumLinearity.scaledBody normBody) T C (pairT c D) terms)

theorem actual_horner_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (horner (var 0) qone (var 1) ≐ GaussianRationalFiniteSum.sum entryBody (var 1) (var 0)) :=
  closeUniv 2 (horner_sum _ _)
theorem euclidean_coefficient_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (entriesMajorized (var 0) (var 1) (var 2) (var 3) ⟶
      majorized (horner (var 0) qone (var 3)) (RationalArithmetic.multiply (var 2) (prefixNorm (var 1) (var 3)))) :=
  closeUniv 4 (.impI (horner_majorized _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEuclideanPolynomialMajorant

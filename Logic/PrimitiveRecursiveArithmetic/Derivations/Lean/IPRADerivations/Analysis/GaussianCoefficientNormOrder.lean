import IPRADerivations.Analysis.GaussianRationalLinearProduct

/-!
# Nonnegative coefficient norms and actual self-differences

The norm is the actual independently denominated rational sum from
GaussianCoefficientL1. Its nonnegativity and the literal zero norm of an
actual self-difference are proved by quantifier-free induction. Original
coefficient codes need not be canonical: subtraction normalizes its output.
These are order and base-case dependencies of finite-demand (AF).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientNormOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1
  (prefixNorm coefficientNorm subCoefficients prefix_zero prefix_succ qL1_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (scalar_zero_code scalar_add_zero qzero_norm)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds
  (natCode natCode_represents natCode_nonnegative add_monotone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1
  (qL1 rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem prefixNorm_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D)
    (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx] prefixNorm C N ≐ prefixNorm D M := by
  simpa only [GaussianCoefficientL1.subst_prefixNorm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (prefixNorm (var 0) (var 1) : PTm 2)
      (σ := ![C,N]) (σ' := ![D,M]) (fun i => by fin_cases i; exact hC; exact hN)

theorem coefficientNorm_congr {C D : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) :
    Γ ⊢[PRAAx] coefficientNorm C ≐ coefficientNorm D := by
  simpa only [GaussianCoefficientL1.subst_coefficientNorm,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (coefficientNorm (var 0) : PTm 1)
      (σ := ![C]) (σ' := ![D]) (fun i => by fin_cases i; exact hC)

theorem subCoefficients_congr {C C' D D' N N' : PTm n}
    (hC : Γ ⊢[PRAAx] C ≐ C') (hD : Γ ⊢[PRAAx] D ≐ D') (hN : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] subCoefficients C D N ≐ subCoefficients C' D' N' := by
  simpa only [GaussianCoefficientL1.subst_subCoefficients,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (subCoefficients (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![C,D,N]) (σ' := ![C',D',N']) (fun i => by fin_cases i; exact hC; exact hD; exact hN)

theorem zero_lower_of_nonnegative (c : PTm n)
    (hc : Γ ⊢[PRAAx] le (numeratorOf c).neg (numeratorOf c).pos) :
    Γ ⊢[PRAAx] rationalLE (natCode zero) c := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (natCode_represents zero)
    (RationalRepresentations.represents_self c) (le_refl _) (RationalArgmin.denominator_positive c)
  apply zle_of_toZ (PTm.monus (numeratorOf c).pos (numeratorOf c).neg)
  have e := natEq (eq_add_of_le hc)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination -e

theorem qL1_zero_lower (q : PTm n) : Γ ⊢[PRAAx] rationalLE (natCode zero) (qL1 q) :=
  zero_lower_of_nonnegative _ (GaussianRationalL1.qL1_nonnegative q)

/-- Nonnegativity concerns the actual normalized finite rational sum,
including the empty prefix and independently denominated coefficients. -/
theorem prefix_nonnegative (C N : PTm n) : Γ ⊢[PRAAx] rationalLE (natCode zero) (prefixNorm C N) := by
  have all : Γ ⊢[PRAAx] .all (rationalLE (natCode zero) (prefixNorm (Syn.shift C) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [RationalArgmin.subst_rationalLE,GaussianRationalSyntheticBounds.subst_natCode,
        GaussianCoefficientL1.subst_prefixNorm,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact RationalArgmin.rationalLE_congr (.eqRefl _)
        ((prefix_zero C).eqTrans scalar_zero_code.eqSymm).eqSymm (RationalArgmin.reflexive _)
    · simp only [RationalArgmin.subst_rationalLE,GaussianRationalSyntheticBounds.subst_natCode,
        GaussianCoefficientL1.subst_prefixNorm,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let I := rationalLE (natCode zero) (prefixNorm (Syn.shift C) (var 0))
      have step := add_monotone (Γ := I :: Γ.map Fm.shift)
        (natCode zero) (prefixNorm (Syn.shift C) (var 0)) (natCode zero) (qL1 (entry (Syn.shift C) (var 0)))
        Prf.hyp0 (qL1_zero_lower (entry (Syn.shift C) (var 0)))
      exact RationalArgmin.rationalLE_congr
        (scalar_add_zero _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one)))
        (prefix_succ _ _).eqSymm step
  simpa only [RationalArgmin.subst_rationalLE,GaussianRationalSyntheticBounds.subst_natCode,
    GaussianCoefficientL1.subst_prefixNorm,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem prefix_numerator_nonnegative (C N : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (prefixNorm C N)).neg (numeratorOf (prefixNorm C N)).pos :=
  GaussianRationalL1.nonnegative_of_lower _ _ (natCode_nonnegative zero) (prefix_nonnegative C N)

theorem coefficient_nonnegative (C : PTm n) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (coefficientNorm C) := prefix_nonnegative C (length C)

theorem coefficient_numerator_nonnegative (C : PTm n) : Γ ⊢[PRAAx]
    le (numeratorOf (coefficientNorm C)).neg (numeratorOf (coefficientNorm C)).pos :=
  prefix_numerator_nonnegative C (length C)

/-- Literal normalized zero is produced even for noncanonical operands. -/
theorem qsub_self (q : PTm n) : Γ ⊢[PRAAx] qsub q q ≐ qzero := by
  have h := GaussianRationalMetric.qsub_represents q q (rawGaussian q) (rawGaussian q) (rawDen q)
    (raw_den_positive q) (raw_represents (Γ := Γ) q) (raw_represents q)
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    GaussianRationalSyntheticDivision.qzero_canonical (raw_den_positive q)
    (hrv := GaussianRationalHorner.zero_represents _)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring

def selfPrefixLaw (C N k : PTm n) : Fm PTm n := le k N ⟶
  prefixNorm (subCoefficients C C N) k ≐ natCode zero

@[simp] theorem subst_selfPrefixLaw {m : ℕ} (σ : Fin n → PTm m) (C N k : PTm n) :
    (selfPrefixLaw C N k).subst σ = selfPrefixLaw (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ k) := by
  simp [selfPrefixLaw]

theorem self_prefix_step (C N k : PTm n) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] prefixNorm (subCoefficients C C N) k ≐ natCode zero) : Γ ⊢[PRAAx]
    prefixNorm (subCoefficients C C N) (succ k) ≐ natCode zero := by
  have term := (qL1_congr ((GaussianCoefficientL1.sub_lookup C C N k hk).eqTrans (qsub_self _))).eqTrans qzero_norm
  exact (prefix_succ _ _).eqTrans ((RationalAlgebra.add_congr ih term).eqTrans
    (scalar_add_zero _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one))))

/-- The actual self-difference has zero norm on every valid prefix. The
bounded guard is needed solely for the actual sequence lookup. -/
theorem self_prefix_zero (C N k : PTm n) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    prefixNorm (subCoefficients C C N) k ≐ natCode zero := by
  have all : Γ ⊢[PRAAx] .all (selfPrefixLaw (Syn.shift C) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,trivial⟩ ?_ ?_
    · simp only [subst_selfPrefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI ((prefix_zero _).eqTrans scalar_zero_code.eqSymm)
    · simp only [subst_selfPrefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact self_prefix_step _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] selfPrefixLaw C N k := by
    simpa only [subst_selfPrefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem self_difference_norm (C N : PTm n) : Γ ⊢[PRAAx]
    coefficientNorm (subCoefficients C C N) ≐ natCode zero :=
  (prefixNorm_congr (.eqRefl _) (GaussianCoefficientL1.zip_length GaussianCoefficientL1.subF C C N)).eqTrans
    (self_prefix_zero C N N (le_refl _))

theorem coefficient_norm_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (rationalLE (natCode zero) (coefficientNorm (var 0)) ⋏
      le (numeratorOf (coefficientNorm (var 0))).neg (numeratorOf (coefficientNorm (var 0))).pos) :=
  closeUniv 1 (.andI (coefficient_nonnegative _) (coefficient_numerator_nonnegative _))

theorem prefix_norm_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (natCode zero) (prefixNorm (var 0) (var 1)) ⋏
      le (numeratorOf (prefixNorm (var 0) (var 1))).neg (numeratorOf (prefixNorm (var 0) (var 1))).pos) :=
  closeUniv 2 (.andI (prefix_nonnegative _ _) (prefix_numerator_nonnegative _ _))

theorem self_difference_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coefficientNorm (subCoefficients (var 0) (var 0) (var 1)) ≐ natCode zero) :=
  closeUniv 2 (self_difference_norm _ _)

theorem actual_self_subtraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qsub (var 0) (var 0) ≐ qzero) := closeUniv 1 (qsub_self _)

end LeanProofs.IPRA.Analysis.GaussianCoefficientNormOrder

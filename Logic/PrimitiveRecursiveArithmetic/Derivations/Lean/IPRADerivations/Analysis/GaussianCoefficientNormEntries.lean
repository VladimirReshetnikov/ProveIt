import IPRADerivations.Analysis.GaussianCoefficientNormOrder
import IPRADerivations.Analysis.GaussianApproximateFactorization

/-!
# Individual entries of actual finite Gaussian coefficient norms

Quantifier-free induction proves that each actual entry's L1 norm is bounded
by the computed finite sum, without assuming entry bounds. Independent
rational denominators are retained when this L1 estimate is converted to
an original Euclidean radius. Actual coefficient subtraction lookup then
transfers a whole coefficient-norm budget to each original coefficient
pair, including the coefficients returned by approximate factorization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientNormEntries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientL1
  (prefixNorm coefficientNorm prefix_succ subCoefficients sub_lookup qL1_congr)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNormOrder
  (prefix_nonnegative qL1_zero_lower)
open LeanProofs.IPRA.Analysis.GaussianRationalLinearProduct
  (scalar_add_zero scalar_zero_add)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode add_monotone)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (qL1)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded qsub)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Appending a nonnegative actual entry increases the computed prefix. -/
theorem prefix_step_monotone (C N : PTm n) : Γ ⊢[PRAAx] rationalLE (prefixNorm C N) (prefixNorm C (succ N)) := by
  have h := add_monotone (Γ := Γ) _ _ _ _ (RationalArgmin.reflexive (prefixNorm C N)) (qL1_zero_lower (entry C N))
  exact RationalArgmin.rationalLE_congr (scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))
    (prefix_succ C N).eqSymm h

/-- The newly appended summand is bounded by the whole new prefix. -/
theorem last_entry_bound (C N : PTm n) : Γ ⊢[PRAAx] rationalLE (qL1 (entry C N)) (prefixNorm C (succ N)) := by
  have h := add_monotone (Γ := Γ) _ _ _ _ (prefix_nonnegative C N) (RationalArgmin.reflexive (qL1 (entry C N)))
  exact RationalArgmin.rationalLE_congr (scalar_zero_add _ (GaussianRationalL1.qL1_guard _)) (prefix_succ C N).eqSymm h

def prefixEntryLaw (C i N : PTm n) : Fm PTm n := lt i N ⟶ rationalLE (qL1 (entry C i)) (prefixNorm C N)
@[simp] theorem subst_prefixEntryLaw {m : ℕ} (σ : Fin n → PTm m) (C i N : PTm n) :
    (prefixEntryLaw C i N).subst σ = prefixEntryLaw (Syn.subst σ C) (Syn.subst σ i) (Syn.subst σ N) := by
  simp only [prefixEntryLaw,Fm.subst_imp,subst_lt,RationalArgmin.subst_rationalLE,
    GaussianRationalL1.subst_qL1,subst_entry,GaussianCoefficientL1.subst_prefixNorm]

theorem prefix_entry_step (C i N : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ N))
    (ih : Γ ⊢[PRAAx] prefixEntryLaw C i N) : Γ ⊢[PRAAx] rationalLE (qL1 (entry C i)) (prefixNorm C (succ N)) := by
  have range : Γ ⊢[PRAAx] le i N := (succ_monus_succ _ _).eqSymm.eqTrans hi
  refine .orE (lt_or_eq_of_le range) ?_ ?_
  · exact RationalArgmin.transitive (.impE ih.wk Prf.hyp0) (prefix_step_monotone C N)
  · exact RationalArgmin.rationalLE_congr (qL1_congr (entry_congr (.eqRefl C) Prf.hyp0)).eqSymm
      (.eqRefl _) (last_entry_bound C N)

/-- Every internally indexed summand is bounded by the actual prefix sum.
The induction formula is quantifier-free; no bounded entry contract is an
input to the result. -/
theorem prefix_entry_bound (C N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry C i)) (prefixNorm C N) := by
  have all : Γ ⊢[PRAAx] .all (prefixEntryLaw (Syn.shift C) (Syn.shift i) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixEntryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact lt_irrefl zero _ (lt_of_le_of_lt (zero_le i) Prf.hyp0)
    · simp only [subst_prefixEntryLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_entry_step (Syn.shift C) (Syn.shift i) (var 0) Prf.hyp0 Prf.hyp1)
  have h : Γ ⊢[PRAAx] prefixEntryLaw C i N := by
    simpa only [subst_prefixEntryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE h hi

theorem coefficient_entry_bound (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry C i)) (coefficientNorm C) := prefix_entry_bound C (length C) i hi

/-- Squaring the actual normalized nonnegative fraction gives precisely the
actual Euclidean tolerance code, with no common-denominator hypothesis. -/
theorem rational_radius_square (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    multiply (normalize (ZT.ofNat A) B) (normalize (ZT.ofNat A) B) ≐ GaussianRationalMetric.squaredTolerance A B := by
  have rep := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat A) B hB
  have product := RationalRepresentations.represents_multiply _ _ _ _ _ _ rep rep
  have positive := GaussianRationalHorner.positive_product _ _ hB hB
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ positive) product
    (GaussianRationalMetric.squared_tolerance_represents A B hB) positive positive
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

/-- A genuine rational L1 bound gives the Euclidean bound at the same
radius A/B. A may be zero and the original components keep independent
denominators and arbitrary signed-pair encodings. -/
theorem l1_to_euclidean (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hL1 : Γ ⊢[PRAAx] rationalLE (qL1 q) (normalize (ZT.ofNat A) B)) : Γ ⊢[PRAAx] bounded q A B :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (rational_radius_square A B hB)
    (RationalArgmin.transitive (GaussianRationalL1.normSq_le_qL1_square q)
      (GaussianRationalL1.square_monotone _ _ (GaussianRationalL1.qL1_nonnegative q) hL1))

theorem bounded_coefficient_entry (C i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hsum : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (normalize (ZT.ofNat A) B))
    (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx] bounded (entry C i) A B :=
  l1_to_euclidean _ _ _ hB (RationalArgmin.transitive (coefficient_entry_bound C i hi) hsum)

/-- The actual subtraction-list lookup transfers a total error budget to
an original coefficient pair, without canonical input/storage guards. -/
theorem bounded_coefficient_difference (C D N i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hsum : Γ ⊢[PRAAx] rationalLE (coefficientNorm (subCoefficients C D N)) (normalize (ZT.ofNat A) B))
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] distanceBounded (entry C i) (entry D i) A B :=
  GaussianRationalReciprocal.bound_congr (sub_lookup C D N i hi) (.eqRefl _) (.eqRefl _)
    (bounded_coefficient_entry _ _ _ _ hB hsum
      (lt_congr (.eqRefl _) (GaussianCoefficientL1.zip_length _ _ _ _).eqSymm hi))

/-- Every actual coefficient error of approximate factorization has the
original Euclidean radius eta. The total error premise is derived by the
complete factorization theorem, rather than supplied here. -/
theorem approximate_factorization_entries (step : PR 3) (C N p q i : PTm n)
    (hRD : Γ ⊢[PRAAx] GaussianFactorParameters.monicRD step)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ GaussianRationalSyntheticDivision.qone)
    (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le one p)
    (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (entry C i) (entry (GaussianApproximateFactorization.productPolynomial step C N p q) i) p q :=
  bounded_coefficient_difference _ _ _ _ _ _ (le_trans hp hpq)
    (Prf.andE₂ (GaussianApproximateFactorization.approximate_factorization step C N p q hRD hC hm hN hp hpq))
    ((succ_monus_succ _ _).eqTrans hi)

/-- The same bound concerns the literal polynomial field of the actual
returned PR4 code, not an unrelated abstract product polynomial. -/
theorem returned_factorization_entries (step : PR 3) (C N p q i : PTm n)
    (hRD : Γ ⊢[PRAAx] GaussianFactorParameters.monicRD step)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] entry C zero ≐ GaussianRationalSyntheticDivision.qone)
    (hN : Γ ⊢[PRAAx] le one N) (hp : Γ ⊢[PRAAx] le one p)
    (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (entry C i) (entry (sndT (GaussianApproximateFactorization.run step C N p q)) i) p q :=
  bounded_coefficient_difference _ _ _ _ _ _ (le_trans hp hpq)
    (Prf.andE₂ (Prf.andE₂ (GaussianApproximateFactorization.program_correct step C N p q hRD hC hm hN hp hpq)))
    ((succ_monus_succ _ _).eqTrans hi)

/-! Actual coefficient-query program and closed statements. -/
def output (C N i : PTm n) : PTm n := pairT (entry C i) (pairT (qL1 (entry C i)) (prefixNorm C N))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N i : PTm n) :
    Syn.subst σ (output C N i) = output (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) := by
  simp only [output,subst_pairT,subst_entry,GaussianRationalL1.subst_qL1,GaussianCoefficientL1.subst_prefixNorm]
theorem output_at (C N i : PTm n) : Γ ⊢[PRAAx] ap3 outputF C N i ≐ output C N i := by
  simpa only [outputF,ap3,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,i]

theorem prefix_entry_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ rationalLE (qL1 (entry (var 0) (var 2))) (prefixNorm (var 0) (var 1))) :=
  closeUniv 3 (.impI (prefix_entry_bound _ _ _ Prf.hyp0))

theorem coefficient_entry_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶ rationalLE (qL1 (entry (var 0) (var 1))) (coefficientNorm (var 0))) :=
  closeUniv 2 (.impI (coefficient_entry_bound _ _ Prf.hyp0))

theorem l1_to_euclidean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ rationalLE (qL1 (var 0)) (normalize (ZT.ofNat (var 1)) (var 2)) ⟶
      bounded (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (l1_to_euclidean _ _ _ Prf.hyp1 Prf.hyp0)))

theorem coefficient_difference_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶
      rationalLE (coefficientNorm (subCoefficients (var 0) (var 1) (var 2))) (normalize (ZT.ofNat (var 4)) (var 5)) ⟶
      lt (var 3) (var 2) ⟶ distanceBounded (entry (var 0) (var 3)) (entry (var 1) (var 3)) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (bounded_coefficient_difference _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem approximate_factorization_entries_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianFactorParameters.monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶
      entry (var 0) zero ≐ GaussianRationalSyntheticDivision.qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ le (var 4) (var 1) ⟶
        distanceBounded (entry (var 0) (var 4))
          (entry (GaussianApproximateFactorization.productPolynomial step (var 0) (var 1) (var 2) (var 3)) (var 4)) (var 2) (var 3)) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact approximate_factorization_entries _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem returned_factorization_entries_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianFactorParameters.monicRD step ⟶ length (var 0) ≐ succ (var 1) ⟶
      entry (var 0) zero ≐ GaussianRationalSyntheticDivision.qone ⟶
      le one (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶ le (var 4) (var 1) ⟶
        distanceBounded (entry (var 0) (var 4))
          (entry (sndT (GaussianApproximateFactorization.run step (var 0) (var 1) (var 2) (var 3))) (var 4)) (var 2) (var 3)) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))
  exact returned_factorization_entries _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem coefficient_query_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 outputF (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) :=
  closeUniv 3 (output_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCoefficientNormEntries

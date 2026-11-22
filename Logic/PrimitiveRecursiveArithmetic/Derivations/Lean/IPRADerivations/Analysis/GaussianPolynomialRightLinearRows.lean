import IPRADerivations.Analysis.GaussianPolynomialLinearFactorCoefficients

/-!
# Every original convolution row for a right linear factor

The actual convolution ignores all left rows strictly beyond the output
row. Genuine numerical induction proves that its accumulated coefficient
has stabilized there. For a degree-one right factor, the unchanged
original convolution therefore has exactly the two expected neighboring
cells at every interior row. This removes the low-degree guard that
prevents applying the existing low Cauchy rule to the original Euler
head's linear factors at arbitrary internal degrees.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialRightLinearRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalPolynomialProduct (coefficient contribution contributionBody data product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem counter_congr (P Q M k : PTm n) {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    coefficient P Q M s k ≐ coefficient P Q M t k :=
  GaussianRationalFiniteSum.sum_index_congr contributionBody h (.eqRefl (data P Q M k))

def trailingLaw (P Q M k r : PTm n) : Fm PTm n :=
  coefficient P Q M (succ k+r) k ≐ coefficient P Q M (succ k) k
@[simp] theorem subst_trailingLaw {l : ℕ} (σ : Fin n → PTm l) (P Q M k r : PTm n) :
    (trailingLaw P Q M k r).subst σ =
      trailingLaw (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ M) (Syn.subst σ k) (Syn.subst σ r) := by
  simp [trailingLaw]

theorem trailing_zero (P Q M k : PTm n) : Γ ⊢[PRAAx] trailingLaw P Q M k zero :=
  counter_congr P Q M k (by ipra_ring)

theorem trailing_step (P Q M k r : PTm n) (ih : Γ ⊢[PRAAx] trailingLaw P Q M k r) :
    Γ ⊢[PRAAx] trailingLaw P Q M k (succ r) := by
  have outside : Γ ⊢[PRAAx] lt k (succ k+r) :=
    le_add_right (succ k) r
  exact (counter_congr P Q M k (show Γ ⊢[PRAAx] succ k+succ r ≐ succ (succ k+r) by ipra_ring)).eqTrans
    ((GaussianRationalPolynomialProduct.coefficient_succ P Q M (succ k+r) k).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianRationalPolynomialProduct.contribution_outside P Q M k _ outside)).eqTrans
        ((GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalPolynomialProduct.coefficient_canonical _ _ _ _ _)).eqTrans ih)))

theorem trailing_rows (P Q M k r : PTm n) : Γ ⊢[PRAAx] trailingLaw P Q M k r := by
  have all : Γ ⊢[PRAAx] .all (trailingLaw (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_trailingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact trailing_zero P Q M k
    · simp only [subst_trailingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact trailing_step _ _ _ _ _ Prf.hyp0
  simpa only [subst_trailingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem coefficient_stabilized (P Q M t k : PTm n) (ht : Γ ⊢[PRAAx] le (succ k) t) : Γ ⊢[PRAAx]
    coefficient P Q M t k ≐ coefficient P Q M (succ k) k :=
  (counter_congr P Q M k (eq_add_of_le ht)).eqTrans (trailing_rows P Q M k (monus t (succ k)))

theorem original_interior_row (P Q N r : PTm n) (hr : Γ ⊢[PRAAx] le (succ r) N) : Γ ⊢[PRAAx]
    entry (product P Q N one) (succ r) ≐
      qadd (qmul (entry P r) (entry Q one)) (qmul (entry P (succ r)) (entry Q zero)) := by
  have range : Γ ⊢[PRAAx] le (succ r) (N+one) := le_trans hr (le_add_right N one)
  have stable := coefficient_stabilized (Γ := Γ) P Q one (succ N) (succ r) ((succ_monus_succ _ _).eqTrans hr)
  have shorter := coefficient_stabilized (Γ := Γ) P Q one (succ (succ (succ r))) (succ r) (le_succ_self _)
  have source := GaussianRationalPolynomialProduct.product_lookup (Γ := Γ) P Q (succ (succ r)) one (succ r)
    (le_of_eq_add (d := two) (by ipra_ring))
  exact (GaussianRationalPolynomialProduct.product_lookup P Q N one (succ r) range).eqTrans
    (stable.eqTrans (shorter.eqSymm.eqTrans (source.eqSymm.eqTrans
      (GaussianPolynomialLinearFactorCoefficients.quadratic_value P Q r))))

theorem actual_convolution_trailing_rows_are_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (succ (var 4)) (var 3) ⟶
      coefficient (var 0) (var 1) (var 2) (var 3) (var 4) ≐
        coefficient (var 0) (var 1) (var 2) (succ (var 4)) (var 4)) :=
  closeUniv 5 (.impI (coefficient_stabilized _ _ _ _ _ Prf.hyp0))

theorem original_right_linear_factor_all_interior_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (succ (var 3)) (var 2) ⟶
      entry (product (var 0) (var 1) (var 2) one) (succ (var 3)) ≐
        qadd (qmul (entry (var 0) (var 3)) (entry (var 1) one))
          (qmul (entry (var 0) (succ (var 3))) (entry (var 1) zero))) :=
  closeUniv 4 (.impI (original_interior_row _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialRightLinearRows

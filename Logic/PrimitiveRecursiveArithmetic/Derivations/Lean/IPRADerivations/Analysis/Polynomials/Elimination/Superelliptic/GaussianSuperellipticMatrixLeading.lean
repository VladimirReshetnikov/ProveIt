import IPRADerivations.Analysis.Polynomials.Elimination.Superelliptic.GaussianSuperellipticMatrixCoefficients
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalPaddedProductDegree
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct

/-!
# Computed first indices and leading values of the original cells

The actual smaller polynomial buffer and its proved coefficient witness
determine the first nonzero coefficient of the ORIGINAL superelliptic
matrix cell. Raw rows are compared through canonical recodes. The source
nonzero f guard derives the actual wrapped product success; no cell or
polynomial degree identity is an incoming premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixLeading

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr qzero_canonical)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_congr recode_eq recode_canonical zeroPrefix zero_prefix_at)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (first flag degree nonzeroCoefficients allZero first_bound first_zero_prefix first_nonzero first_from_witness
    success_index flag_cases flag_one_of_nonzero nonzero_of_flag_one found_of_flag_one flag_one_of_found
    all_zero_of_flag_zero flag_zero_of_all_zero degree_balance)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialProductDegree
  (leading leading_canonical product_first product_success product_leading product_failure_left)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion
  (normalizedRow normalized_length rowShape)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF power_zero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot width)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixEntries (input entryPolynomial)
open LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixCoefficients
  (APolynomial wrapped localBound localPolynomial witness)
open LeanProofs.IPRA.Foundations.RuntimeCyclicPermutation (inverseIndex wrap)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

/-- Only individual bounded recoded observations are compared. -/
def recodedEntries (C D N : PTm n) : Fm PTm n := .all (le (var 0) (Syn.shift N) ⟶
  recode (entry (Syn.shift C) (var 0)) ≐ recode (entry (Syn.shift D) (var 0)))
ipra_subst recodedEntries [Syn.subst_shift, Syn.shift_subst]
theorem recoded_at (C D N i : PTm n) (h : Γ ⊢[PRAAx] recodedEntries C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] recode (entry C i) ≐ recode (entry D i) := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ recode (entry C i) ≐ recode (entry D i) := by
    simpa [recodedEntries] using h.allE i
  exact .impE rule hi
theorem recoded_symm (C D N : PTm n) (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx]
    recodedEntries D C N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] recodedEntries (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,subst_recodedEntries,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  exact (recoded_at _ _ _ _ hs.wk Prf.hyp0).eqSymm
theorem recoded_nonzero (C D N : PTm n) (hC : Γ ⊢[PRAAx] nonzeroCoefficients C N)
    (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx] nonzeroCoefficients D N := by
  have bound := success_index C N (flag_one_of_nonzero C N hC)
  have found := first_from_witness D N (first C N) ((succ_monus_succ _ _).eqTrans bound)
    (.impI (.impE (first_nonzero C N (found_of_flag_one C N (flag_one_of_nonzero C N hC))).wk
      ((recoded_at _ _ _ _ h bound).wk.eqTrans Prf.hyp0)))
  exact nonzero_of_flag_one D N (flag_one_of_found D N (.andE₁ found))
theorem recoded_zero (C D N : PTm n) (hC : Γ ⊢[PRAAx] allZero C N)
    (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx] allZero D N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] recodedEntries (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,subst_recodedEntries,Syn.shift] using h.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  exact (recoded_at _ _ _ _ hs.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)).eqSymm.eqTrans
    (zero_prefix_at _ _ _ zs.wk Prf.hyp0)
theorem recoded_flag (C D N : PTm n) (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx]
    flag C N ≐ flag D N := by
  refine .orE (flag_cases C N) ?_ ?_
  · exact Prf.hyp0.eqTrans (flag_zero_of_all_zero D N
      (recoded_zero C D N (all_zero_of_flag_zero C N Prf.hyp0) h.wk)).eqSymm
  · exact Prf.hyp0.eqTrans (flag_one_of_nonzero D N
      (recoded_nonzero C D N (nonzero_of_flag_one C N Prf.hyp0) h.wk)).eqSymm
theorem recoded_first (C D N : PTm n) (hC : Γ ⊢[PRAAx] nonzeroCoefficients C N)
    (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx] first C N ≐ first D N := by
  have hD := recoded_nonzero C D N hC h
  have c := success_index C N (flag_one_of_nonzero C N hC)
  have d := success_index D N (flag_one_of_nonzero D N hD)
  have forward := first_from_witness D N (first C N) ((succ_monus_succ _ _).eqTrans c)
    (.impI (.impE (first_nonzero C N (found_of_flag_one C N (flag_one_of_nonzero C N hC))).wk
      ((recoded_at _ _ _ _ h c).wk.eqTrans Prf.hyp0)))
  have backward := first_from_witness C N (first D N) ((succ_monus_succ _ _).eqTrans d)
    (.impI (.impE (first_nonzero D N (found_of_flag_one D N (flag_one_of_nonzero D N hD))).wk
      ((recoded_at _ _ _ _ h d).wk.eqSymm.eqTrans Prf.hyp0)))
  exact le_antisymm (.andE₂ backward) (.andE₂ forward)
theorem recoded_degree (C D N : PTm n) (hC : Γ ⊢[PRAAx] nonzeroCoefficients C N)
    (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx] degree C N ≐ degree D N :=
  congrMonus (.eqRefl _) (recoded_first _ _ _ hC h)
theorem recoded_leading (C D N : PTm n) (hC : Γ ⊢[PRAAx] nonzeroCoefficients C N)
    (h : Γ ⊢[PRAAx] recodedEntries C D N) : Γ ⊢[PRAAx] leading C N ≐ leading D N :=
  (recoded_at _ _ _ _ h (success_index C N (flag_one_of_nonzero C N hC))).eqTrans
    (recode_congr (entry_congr (.eqRefl _) (recoded_first _ _ _ hC h)))

theorem normalized_entry (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) : Γ ⊢[PRAAx]
    entry (normalizedRow C) i ≐ recode (entry C i) :=
  (GaussianRationalCoefficientScaling.scaled_lookup _ _ _ hi).eqTrans (GaussianRationalFiniteProduct.raw_one_left _)
theorem normalized_recoded (C N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    recodedEntries C (normalizedRow C) N := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have e := normalized_entry (Γ := Δ) (Syn.shift C) (var 0)
    (lt_congr (.eqRefl _) cs.wk.eqSymm ((succ_monus_succ _ _).eqTrans Prf.hyp0))
  simpa only [Δ,Syn.shift,GaussianPolynomialMonicCompanion.subst_normalizedRow] using
    ((recode_congr e).eqTrans (recode_eq _ (recode_canonical _))).eqSymm

theorem first_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    first C N ≐ first D M := by
  ipra_congr (first (var 0) (var 1) : PTm 2) with [hC, hN]
theorem flag_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    flag C N ≐ flag D M := by
  ipra_congr (flag (var 0) (var 1) : PTm 2) with [hC, hN]
theorem leading_congr {C D N M : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ M) : Γ ⊢[PRAAx]
    leading C N ≐ leading D M :=
  recode_congr (entry_congr hC (first_congr hC hN))

theorem padded_zero (C N p : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] allZero C N) : Γ ⊢[PRAAx] allZero (leftPad C p) (p+N) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] allZero (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalPolynomialDegree.subst_allZero,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  have bound : lt (var 0) (Syn.shift (succ (p+N))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Syn.shift p+succ (Syn.shift N)) :=
    lt_congr (.eqRefl _) (by simp only [Syn.shift,ConciseIPRA.PTm.subst_succ,PTm.subst_add]; ipra_ring) Prf.hyp0
  simpa only [Syn.shift,GaussianRationalPolynomialBuffers.subst_leftPad] using
    GaussianRationalLinearCancellation.pad_zero_before (Syn.shift C) (Syn.shift p) (succ (Syn.shift N)) (var 0)
      (le_congr (.eqRefl _) cs.wk.eqSymm (le_refl _)) zs.wk bound
theorem padded_flag (C N p : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    flag (leftPad C p) (p+N) ≐ flag C N := by
  refine .orE (flag_cases C N) ?_ ?_
  · exact (flag_zero_of_all_zero _ _ (padded_zero C N p hC.wk (all_zero_of_flag_zero C N Prf.hyp0))).eqTrans Prf.hyp0.eqSymm
  · exact (flag_one_of_nonzero _ _ (GaussianRationalPaddedProductDegree.padded_nonzero C N p hC.wk
      (nonzero_of_flag_one C N Prf.hyp0))).eqTrans Prf.hyp0.eqSymm
theorem padded_leading (C N p : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (h : Γ ⊢[PRAAx] nonzeroCoefficients C N) : Γ ⊢[PRAAx]
    leading (leftPad C p) (p+N) ≐ leading C N :=
  (recode_congr (entry_congr (.eqRefl _) (GaussianRationalLinearCancellation.pad_first C N p hC h))).eqTrans
    (recode_congr (GaussianRationalPolynomialBuffers.pad_tail C p (first C N)
      (lt_congr (.eqRefl _) hC.eqSymm (found_of_flag_one C N (flag_one_of_nonzero C N h)))))

def selectedRow (G m r j : PTm n) : PTm n := entry G (slot m (inverseIndex m j r))
ipra_subst selectedRow
theorem selected_length (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    length (selectedRow G m r j) ≐ succ a :=
  (normalized_length _).eqSymm.eqTrans (GaussianSuperellipticMatrixCoefficients.A_length _ _ _ _ _
    (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))
theorem selected_recoded (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    recodedEntries (selectedRow G m r j) (APolynomial G m r j) a :=
  normalized_recoded _ _ (selected_length f G m a c r j h)
theorem product_flag (P Q N M : PTm n) (hQ : Γ ⊢[PRAAx] nonzeroCoefficients Q M) : Γ ⊢[PRAAx]
    flag (GaussianRationalPolynomialProduct.product P Q N M) (N+M) ≐ flag P N := by
  refine .orE (flag_cases P N) ?_ ?_
  · exact (product_failure_left _ _ _ _ Prf.hyp0).eqTrans Prf.hyp0.eqSymm
  · exact (product_success _ _ _ _ (nonzero_of_flag_one P N Prf.hyp0) hQ.wk).eqTrans Prf.hyp0.eqSymm
theorem local_flag (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) : Γ ⊢[PRAAx]
    flag (localPolynomial f G m a c r j) (localBound a c r j) ≐ flag (selectedRow G m r j) a := by
  have nf := recoded_nonzero f (normalizedRow f) c hf
    (normalized_recoded f c (.andE₁ (.andE₂ (.andE₁ h))))
  have row := (recoded_flag _ _ _ (selected_recoded f G m a c r j h)).eqSymm
  refine .orE (lt_or_le r j) ?_ ?_
  · exact (flag_congr (GaussianSuperellipticMatrixCoefficients.wrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.wrapped_bound_value a c r j Prf.hyp0)).eqTrans
      ((product_flag (APolynomial G m r j) (normalizedRow f) a c nf.wk).eqTrans row.wk)
  · exact (flag_congr (GaussianSuperellipticMatrixCoefficients.unwrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.unwrapped_bound_value a c r j Prf.hyp0)).eqTrans row.wk
theorem local_nonzero (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    nonzeroCoefficients (localPolynomial f G m a c r j) (localBound a c r j) :=
  nonzero_of_flag_one _ _ ((local_flag _ _ _ _ _ _ _ h hf).eqTrans (flag_one_of_nonzero _ _ hA))
theorem local_first (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    first (localPolynomial f G m a c r j) (localBound a c r j) ≐
      first (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*first f c := by
  have nr := selected_recoded f G m a c r j h
  have fr := normalized_recoded f c (.andE₁ (.andE₂ (.andE₁ h)))
  have nA := recoded_nonzero _ _ _ hA nr
  have nf := recoded_nonzero _ _ _ hf fr
  have Ar := (recoded_first _ _ _ hA nr).eqSymm
  have ff := (recoded_first _ _ _ hf fr).eqSymm
  refine .orE (lt_or_le r j) ?_ ?_
  · have left := (first_congr (GaussianSuperellipticMatrixCoefficients.wrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.wrapped_bound_value a c r j Prf.hyp0)).eqTrans
      ((product_first _ _ _ _ nA.wk nf.wk).eqTrans (congrAdd Ar.wk ff.wk))
    have right : (lt r j) :: Γ ⊢[PRAAx]
        first (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*first f c ≐
          first (selectedRow G m r j) a+first f c := (congrAdd (.eqRefl (first (selectedRow G m r j) a))
      (congrMul (GaussianSuperellipticMatrixEntries.inverse_wrap_one m r j (.andE₂ (.andE₂ h.wk)) Prf.hyp0)
        (.eqRefl (first f c)))).eqTrans (by ipra_ring)
    exact left.eqTrans right.eqSymm
  · have left := (first_congr (GaussianSuperellipticMatrixCoefficients.unwrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.unwrapped_bound_value a c r j Prf.hyp0)).eqTrans Ar.wk
    have right : (le j r) :: Γ ⊢[PRAAx]
        first (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*first f c ≐
          first (selectedRow G m r j) a := (congrAdd (.eqRefl (first (selectedRow G m r j) a))
      (congrMul (GaussianSuperellipticMatrixEntries.inverse_wrap_zero m r j (.andE₁ (.andE₂ h.wk)) Prf.hyp0)
        (.eqRefl (first f c)))).eqTrans (by ipra_ring)
    exact left.eqTrans right.eqSymm
theorem local_degree (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    degree (localPolynomial f G m a c r j) (localBound a c r j) ≐
      degree (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*degree f c := by
  ipra_lc natEq (degree_balance _ _ (flag_one_of_nonzero _ _ (local_nonzero _ _ _ _ _ _ _ h hf hA)))-
    natEq (local_first _ _ _ _ _ _ _ h hf hA)+
    natEq (GaussianSuperellipticMatrixCoefficients.local_bound_wrap m a c r j (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))-
    natEq (degree_balance _ _ (flag_one_of_nonzero _ _ hA))-
    𝔞(wrap m (inverseIndex m j r) j)*natEq (degree_balance _ _ (flag_one_of_nonzero _ _ hf))
theorem local_leading (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    leading (localPolynomial f G m a c r j) (localBound a c r j) ≐
      qmul (leading (selectedRow G m r j) a) (power (leading f c) (wrap m (inverseIndex m j r) j)) := by
  have nr := selected_recoded f G m a c r j h
  have fr := normalized_recoded f c (.andE₁ (.andE₂ (.andE₁ h)))
  have nA := recoded_nonzero _ _ _ hA nr
  have nf := recoded_nonzero _ _ _ hf fr
  have Ar := (recoded_leading _ _ _ hA nr).eqSymm
  have ff := (recoded_leading _ _ _ hf fr).eqSymm
  refine .orE (lt_or_le r j) ?_ ?_
  · have left := (leading_congr (GaussianSuperellipticMatrixCoefficients.wrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.wrapped_bound_value a c r j Prf.hyp0)).eqTrans
      ((product_leading _ _ _ _ nA.wk nf.wk).eqTrans (qmul_congr Ar.wk ff.wk))
    have right : (lt r j) :: Γ ⊢[PRAAx]
        qmul (leading (selectedRow G m r j) a) (power (leading f c) (wrap m (inverseIndex m j r) j)) ≐
          qmul (leading (selectedRow G m r j) a) (leading f c) := qmul_congr (.eqRefl (leading (selectedRow G m r j) a))
      ((congrAp2 powerF (GaussianSuperellipticMatrixEntries.inverse_wrap_one m r j (.andE₂ (.andE₂ h.wk)) Prf.hyp0)
        (.eqRefl (leading f c))).eqTrans (GaussianRationalPowerAlgebra.power_one _ (leading_canonical _ _)))
    exact left.eqTrans right.eqSymm
  · have left := (leading_congr (GaussianSuperellipticMatrixCoefficients.unwrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.unwrapped_bound_value a c r j Prf.hyp0)).eqTrans Ar.wk
    have right : (le j r) :: Γ ⊢[PRAAx]
        qmul (leading (selectedRow G m r j) a) (power (leading f c) (wrap m (inverseIndex m j r) j)) ≐
          leading (selectedRow G m r j) a := (qmul_congr (.eqRefl (leading (selectedRow G m r j) a))
      ((congrAp2 powerF (GaussianSuperellipticMatrixEntries.inverse_wrap_zero m r j (.andE₁ (.andE₂ h.wk)) Prf.hyp0)
        (.eqRefl (leading f c))).eqTrans (power_zero _))).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (leading_canonical _ _))
    exact left.eqTrans right.eqSymm

theorem coefficient_recoded (C D N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalGridCoefficientEquality.coefficientsEqual C D N) : Γ ⊢[PRAAx]
    recodedEntries C D N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalGridCoefficientEquality.coefficientsEqual
      (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  exact recode_congr (GaussianRationalLinearCancellation.coefficients_at _ _ _ _ hs.wk Prf.hyp0)
theorem cell_recoded (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    recodedEntries (entryPolynomial f G m a c r j) (witness f G m a c r j) (width m a c) :=
  coefficient_recoded _ _ _ (GaussianSuperellipticMatrixCoefficients.coefficients_equal _ _ _ _ _ _ _ h)
theorem padding_balance (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    monus (width m a c) (localBound a c r j)+localBound a c r j ≐ width m a c :=
  (add_comm _ _).eqTrans (eq_add_of_le (GaussianSuperellipticMatrixCoefficients.local_store_bound _ _ _ _ _ _ _ h)).eqSymm
theorem cell_local_flag (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j) : Γ ⊢[PRAAx]
    flag (entryPolynomial f G m a c r j) (width m a c) ≐
      flag (localPolynomial f G m a c r j) (localBound a c r j) :=
  (recoded_flag _ _ _ (cell_recoded _ _ _ _ _ _ _ h)).eqTrans
    ((flag_congr (.eqRefl _) (padding_balance _ _ _ _ _ _ _ h).eqSymm).eqTrans
      (padded_flag _ _ _ (GaussianSuperellipticMatrixCoefficients.local_length f G m a c r j
        (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))))
theorem cell_flag (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) : Γ ⊢[PRAAx]
    flag (entryPolynomial f G m a c r j) (width m a c) ≐ flag (selectedRow G m r j) a :=
  (cell_local_flag _ _ _ _ _ _ _ h).eqTrans (local_flag _ _ _ _ _ _ _ h hf)
theorem cell_nonzero (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    nonzeroCoefficients (entryPolynomial f G m a c r j) (width m a c) :=
  nonzero_of_flag_one _ _ ((cell_flag _ _ _ _ _ _ _ h hf).eqTrans (flag_one_of_nonzero _ _ hA))
theorem cell_nonzero_iff (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) : Γ ⊢[PRAAx]
    Fm.iff (nonzeroCoefficients (entryPolynomial f G m a c r j) (width m a c))
      (nonzeroCoefficients (selectedRow G m r j) a) :=
  .andI (.impI (nonzero_of_flag_one _ _ ((cell_flag _ _ _ _ _ _ _ h.wk hf.wk).eqSymm.eqTrans
    (flag_one_of_nonzero _ _ Prf.hyp0)))) (.impI (cell_nonzero _ _ _ _ _ _ _ h.wk hf.wk Prf.hyp0))
theorem cell_zero (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hA : Γ ⊢[PRAAx] flag (selectedRow G m r j) a ≐ zero) : Γ ⊢[PRAAx]
    flag (entryPolynomial f G m a c r j) (width m a c) ≐ zero := by
  have row := (recoded_flag _ _ _ (selected_recoded f G m a c r j h)).eqSymm.eqTrans hA
  apply (cell_local_flag _ _ _ _ _ _ _ h).eqTrans
  refine .orE (lt_or_le r j) ?_ ?_
  · exact (flag_congr (GaussianSuperellipticMatrixCoefficients.wrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.wrapped_bound_value a c r j Prf.hyp0)).eqTrans
      (product_failure_left _ _ _ _ row.wk)
  · exact (flag_congr (GaussianSuperellipticMatrixCoefficients.unwrapped_value f G m a c r j Prf.hyp0)
      (GaussianSuperellipticMatrixCoefficients.unwrapped_bound_value a c r j Prf.hyp0)).eqTrans row.wk
theorem cell_first (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    first (entryPolynomial f G m a c r j) (width m a c) ≐
      monus (width m a c) (localBound a c r j)+first (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*first f c :=
  (recoded_first _ _ _ (cell_nonzero _ _ _ _ _ _ _ h hf hA) (cell_recoded _ _ _ _ _ _ _ h)).eqTrans
    ((first_congr (.eqRefl _) (padding_balance _ _ _ _ _ _ _ h).eqSymm).eqTrans
      ((GaussianRationalLinearCancellation.pad_first _ _ _
        (GaussianSuperellipticMatrixCoefficients.local_length f G m a c r j
          (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))
        (local_nonzero _ _ _ _ _ _ _ h hf hA)).eqTrans
        ((congrAdd (.eqRefl _) (local_first _ _ _ _ _ _ _ h hf hA)).eqTrans (by ipra_ring))))
theorem cell_degree (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    degree (entryPolynomial f G m a c r j) (width m a c) ≐
      degree (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*degree f c := by
  ipra_lc natEq (degree_balance _ _ (flag_one_of_nonzero _ _ (cell_nonzero _ _ _ _ _ _ _ h hf hA)))-
    natEq (cell_first _ _ _ _ _ _ _ h hf hA)+
    natEq (GaussianSuperellipticMatrixCoefficients.local_bound_wrap m a c r j (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))-
    natEq (padding_balance _ _ _ _ _ _ _ h)-natEq (degree_balance _ _ (flag_one_of_nonzero _ _ hA))-
    𝔞(wrap m (inverseIndex m j r) j)*natEq (degree_balance _ _ (flag_one_of_nonzero _ _ hf))
theorem cell_leading (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    leading (entryPolynomial f G m a c r j) (width m a c) ≐
      qmul (leading (selectedRow G m r j) a) (power (leading f c) (wrap m (inverseIndex m j r) j)) :=
  (recoded_leading _ _ _ (cell_nonzero _ _ _ _ _ _ _ h hf hA) (cell_recoded _ _ _ _ _ _ _ h)).eqTrans
    ((leading_congr (.eqRefl _) (padding_balance _ _ _ _ _ _ _ h).eqSymm).eqTrans
      ((padded_leading _ _ _ (GaussianSuperellipticMatrixCoefficients.local_length f G m a c r j
        (.andE₂ (.andE₂ (.andE₁ h))) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))
        (local_nonzero _ _ _ _ _ _ _ h hf hA)).eqTrans (local_leading _ _ _ _ _ _ _ h hf hA)))
theorem weighted_cell_balance (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] input f G m a c r j)
    (hf : Γ ⊢[PRAAx] nonzeroCoefficients f c) (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    m*degree (entryPolynomial f G m a c r j) (width m a c)+degree f c*r ≐
      (m*degree (selectedRow G m r j) a+degree f c*inverseIndex m j r)+degree f c*j := by
  ipra_lc 𝔞(m)*natEq (cell_degree _ _ _ _ _ _ _ h hf hA)-
    𝔞(degree f c)*natEq (GaussianSuperellipticMatrixEntries.index_equation m r j (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)))

def sourceInput (f G m a c r j : PTm n) : Fm PTm n := input f G m a c r j ⋏ nonzeroCoefficients f c
def expectedFirst (f G m a c r j : PTm n) : PTm n :=
  monus (width m a c) (localBound a c r j)+first (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*first f c
def expectedDegree (f G m a c r j : PTm n) : PTm n := degree (selectedRow G m r j) a+wrap m (inverseIndex m j r) j*degree f c
def expectedLeading (f G m a c r j : PTm n) : PTm n :=
  qmul (leading (selectedRow G m r j) a) (power (leading f c) (wrap m (inverseIndex m j r) j))
def certificate (f G m a c r j : PTm n) : Fm PTm n :=
  (flag (entryPolynomial f G m a c r j) (width m a c) ≐ flag (selectedRow G m r j) a) ⋏
    (nonzeroCoefficients (selectedRow G m r j) a ⟶
      ((first (entryPolynomial f G m a c r j) (width m a c) ≐ expectedFirst f G m a c r j) ⋏
        ((degree (entryPolynomial f G m a c r j) (width m a c) ≐ expectedDegree f G m a c r j) ⋏
          ((leading (entryPolynomial f G m a c r j) (width m a c) ≐ expectedLeading f G m a c r j) ⋏
            (m*degree (entryPolynomial f G m a c r j) (width m a c)+degree f c*r ≐
              (m*degree (selectedRow G m r j) a+degree f c*inverseIndex m j r)+degree f c*j)))))
ipra_subst sourceInput
ipra_subst expectedFirst
ipra_subst expectedDegree
ipra_subst expectedLeading
ipra_subst certificate
theorem matrix_leading (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] sourceInput f G m a c r j) : Γ ⊢[PRAAx]
    certificate f G m a c r j :=
  .andI (cell_flag _ _ _ _ _ _ _ (.andE₁ h) (.andE₂ h)) (.impI
    (.andI (cell_first _ _ _ _ _ _ _ (.andE₁ h.wk) (.andE₂ h.wk) Prf.hyp0)
      (.andI (cell_degree _ _ _ _ _ _ _ (.andE₁ h.wk) (.andE₂ h.wk) Prf.hyp0)
        (.andI (cell_leading _ _ _ _ _ _ _ (.andE₁ h.wk) (.andE₂ h.wk) Prf.hyp0)
          (weighted_cell_balance _ _ _ _ _ _ _ (.andE₁ h.wk) (.andE₂ h.wk) Prf.hyp0)))))

/-! A total actual PR7 returns the original polynomial cell, selected raw
row, actual wrap, and both computed and derived degree/leading values. -/
def output (f G m a c r j : PTm n) : PTm n := pairT (entryPolynomial f G m a c r j)
  (pairT (selectedRow G m r j) (pairT (wrap m (inverseIndex m j r) j)
    (pairT (degree (entryPolynomial f G m a c r j) (width m a c))
      (pairT (expectedDegree f G m a c r j)
        (pairT (leading (entryPolynomial f G m a c r j) (width m a c)) (expectedLeading f G m a c r j))))))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (f G m a c r j : PTm n) : PTm n := app outputF ![f,G,m,a,c,r,j]
def fields (p : PTm n) (i : Fin 7) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),
    fstT (sndT (sndT (sndT (sndT p)))),fstT (sndT (sndT (sndT (sndT (sndT p))))),
      sndT (sndT (sndT (sndT (sndT (sndT p)))))] i
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 7) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem program_at (f G m a c r j : PTm n) : Γ ⊢[PRAAx] run f G m a c r j ≐ output f G m a c r j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![f,G,m,a,c,r,j]
theorem returned_fields (f G m a c r j : PTm n) (i : Fin 7) : Γ ⊢[PRAAx]
    fields (run f G m a c r j) i ≐
      ![entryPolynomial f G m a c r j,selectedRow G m r j,wrap m (inverseIndex m j r) j,
        degree (entryPolynomial f G m a c r j) (width m a c),expectedDegree f G m a c r j,
          leading (entryPolynomial f G m a c r j) (width m a c),expectedLeading f G m a c r j] i :=
  pairVectorField_eq 6 _ (program_at f G m a c r j) i
theorem returned_degree (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] sourceInput f G m a c r j)
    (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    fields (run f G m a c r j) 3 ≐ fields (run f G m a c r j) 4 :=
  (returned_fields _ _ _ _ _ _ _ 3).eqTrans
    ((cell_degree _ _ _ _ _ _ _ (.andE₁ h) (.andE₂ h) hA).eqTrans (returned_fields _ _ _ _ _ _ _ 4).eqSymm)
theorem returned_leading (f G m a c r j : PTm n) (h : Γ ⊢[PRAAx] sourceInput f G m a c r j)
    (hA : Γ ⊢[PRAAx] nonzeroCoefficients (selectedRow G m r j) a) : Γ ⊢[PRAAx]
    fields (run f G m a c r j) 5 ≐ fields (run f G m a c r j) 6 :=
  (returned_fields _ _ _ _ _ _ _ 5).eqTrans
    ((cell_leading _ _ _ _ _ _ _ (.andE₁ h) (.andE₂ h) hA).eqTrans (returned_fields _ _ _ _ _ _ _ 6).eqSymm)

/-! Every original polynomial, shape, matrix position and stored bound
is numerical and bound internally. No determinant claim is asserted. -/
theorem actual_recoded_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (recodedEntries (var 0) (var 1) (var 2) ⟶ flag (var 0) (var 2) ≐ flag (var 1) (var 2)) :=
  closeUniv 3 (.impI (recoded_flag _ _ _ Prf.hyp0))
theorem actual_zero_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      flag (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ≐ zero ⟶
        flag (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)) ≐ zero) :=
  closeUniv 7 (.impI (.impI (cell_zero _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cell_nonzero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      Fm.iff (nonzeroCoefficients (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)))
        (nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3))) :=
  closeUniv 7 (.impI (cell_nonzero_iff _ _ _ _ _ _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_cell_first_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ⟶
        first (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)) ≐
          expectedFirst (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (cell_first _ _ _ _ _ _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))
theorem actual_cell_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ⟶
        degree (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)) ≐
          expectedDegree (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (cell_degree _ _ _ _ _ _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))
theorem actual_cell_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ⟶
        leading (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4)) ≐
          expectedLeading (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (cell_leading _ _ _ _ _ _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))
theorem actual_weighted_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ⟶
        (var 2)*degree (entryPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (width (var 2) (var 3) (var 4))+
          degree (var 0) (var 4)*(var 5) ≐
            ((var 2)*degree (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3)+
              degree (var 0) (var 4)*inverseIndex (var 2) (var 6) (var 5))+degree (var 0) (var 4)*(var 6)) :=
  closeUniv 7 (.impI (.impI (weighted_cell_balance _ _ _ _ _ _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))
theorem actual_matrix_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (matrix_leading _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem actual_returned_leading_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      nonzeroCoefficients (selectedRow (var 1) (var 2) (var 5) (var 6)) (var 3) ⟶
        ((fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) 3 ≐
          fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) 4) ⋏
            (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) 5 ≐
              fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) 6))) :=
  closeUniv 7 (.impI (.impI (.andI (returned_degree _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (returned_leading _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticMatrixLeading

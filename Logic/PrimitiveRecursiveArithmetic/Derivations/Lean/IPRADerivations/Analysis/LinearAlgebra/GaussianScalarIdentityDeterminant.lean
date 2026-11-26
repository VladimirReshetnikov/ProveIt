import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDeterminant
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductAlgebra
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Analysis.LinearAlgebra.GaussianDeterminantSignTransport

/-!
# The actual identity table has determinant one at every numerical size

The existing retained scan contains the computed identity word. Its real
inversion count is zero. Every other retained word has an actual bounded
mismatching digit, found from the finite equality test; its genuinely
zero identity-table factor is absorbed by the existing product fold.
The SAME determinant sum then collapses by the proved Gaussian spike
sum. No successful selector, parity, determinant law or host dimension
is supplied, including at sizes zero and one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarIdentityDeterminant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell signPoint)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (delta table)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (scalarDet rawProduct factorBody factorData signedTerm signedBody)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr length subst_length)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords
  (digit identity encode position words count retained_bound retained_position_unique)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def identityBody : PTm 3 := delta (var 0) (var 1)
def identityTable (m : PTm n) : PTm n := table identityBody m m zero
def identityWord (m : PTm n) : PTm n := encode (identity m) m
def identityRank (m : PTm n) : PTm n := position (identity m) m
@[simp] theorem subst_identityTable {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (identityTable m) = identityTable (Syn.subst σ m) := by simp [identityTable]
@[simp] theorem subst_identityWord {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (identityWord m) = identityWord (Syn.subst σ m) := by simp [identityWord]
@[simp] theorem subst_identityRank {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (identityRank m) = identityRank (Syn.subst σ m) := by simp [identityRank]

theorem identity_lookup (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (identityTable m) r j ≐ delta r j := by
  simpa [identityTable,identityBody] using GaussianRationalFiberVandermonde.table_lookup identityBody m m zero r j hr hj
theorem identity_word_bound (m : PTm n) : Γ ⊢[PRAAx] lt (identityWord m) (Foundations.RuntimePermutationWords.horizon m) :=
  Foundations.RuntimePermutationWords.encode_bound _ _ (.andE₁ (.andE₂ (Foundations.RuntimePermutationWords.identity_tuple m)))
theorem identity_rank_bound (m : PTm n) : Γ ⊢[PRAAx] lt (identityRank m) (count m) :=
  .andE₁ (Foundations.RuntimePermutationWords.listed _ _ (Foundations.RuntimePermutationWords.identity_tuple m))
theorem identity_rank_word (m : PTm n) : Γ ⊢[PRAAx] GaussianPolynomialDeterminant.wordCode m (identityRank m) ≐ identityWord m :=
  .andE₂ (Foundations.RuntimePermutationWords.listed _ _ (Foundations.RuntimePermutationWords.identity_tuple m))
theorem identity_digit (m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx] digit m (identityWord m) i ≐ i :=
  (Foundations.RuntimePermutationWords.encode_decode _ _ _ (.andE₁ (.andE₂ (Foundations.RuntimePermutationWords.identity_tuple m))) hi).eqTrans
    (Foundations.RuntimePermutationWords.identity_lookup _ _ hi)

theorem identity_inversion_bit (m i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.inversionBit m (identityWord m) i j ≐ zero := by
  refine .orE (Foundations.RuntimePermutationWords.inversion_cases m (identityWord m) i j) Prf.hyp0 ?_
  have bad : (Foundations.RuntimePermutationWords.inversionBit m (identityWord m) i j ≐ one) :: Γ ⊢[PRAAx]
      lt i j ⋏ lt (digit m (identityWord m) j) (digit m (identityWord m) i) :=
    (Foundations.RuntimePermutationWords.inversion_reflection _ _ _ _).iffMp Prf.hyp0
  exact le_lt_absurd _ (le_of_lt (.andE₁ bad))
    (lt_congr (identity_digit _ _ hj.wk) (identity_digit _ _ hi.wk) (.andE₂ bad))

theorem identity_inversion_row (m i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    Foundations.RuntimePermutationWords.rowPrefix m (identityWord m) i m ≐ zero := by
  apply sum_zero_of_bounded
  refine .allI (.impI ?_)
  have ii : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hi.shift
  have e := (Foundations.RuntimePermutationWords.inversion_column_at
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (Syn.shift m) (identityWord (Syn.shift m)) (Syn.shift i) (var 0)).eqTrans
      (identity_inversion_bit _ _ _ ii.wk Prf.hyp0)
  simpa only [Syn.shift,subst_pairT,Foundations.RuntimePermutationWords.subst_data,subst_identityWord] using e

theorem identity_inversions (m : PTm n) : Γ ⊢[PRAAx] Foundations.RuntimePermutationWords.inversions m (identityWord m) ≐ zero := by
  apply sum_zero_of_bounded
  refine .allI (.impI ?_)
  have e := (Foundations.RuntimePermutationWords.inversion_row_at
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (Syn.shift m) (identityWord (Syn.shift m)) (var 0)).eqTrans
      (identity_inversion_row _ _ Prf.hyp0)
  simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_data,subst_identityWord] using e

theorem identity_sign (m : PTm n) : Γ ⊢[PRAAx] signPoint m (identityWord m) ≐ qone :=
  GaussianPolynomialDeterminantTerms.sign_even _ _ ((congrAp1 parF (identity_inversions m)).eqTrans par_zero)
theorem identity_product (m : PTm n) : Γ ⊢[PRAAx] rawProduct (identityTable m) m (identityWord m) ≐ qone := by
  apply GaussianRationalProductAlgebra.product_one_of_terms
  refine .allI (.impI ?_)
  have e := (GaussianScalarDeterminant.factor_body_at
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (identityTable (Syn.shift m)) (Syn.shift m) (identityWord (Syn.shift m)) (var 0)).eqTrans
      ((identity_lookup _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0).eqTrans
        (GaussianRationalLagrangeCardinals.delta_equal _ _ (identity_digit _ _ Prf.hyp0)))
  simpa only [GaussianRationalProductAlgebra.oneTerms,Syn.shift,GaussianScalarDeterminant.subst_factorData,
    subst_identityTable,subst_identityWord] using e

/-- The actual all-bit test of matching every identity digit. -/
def matchBody : PTm 2 := eqb (digit (fstT (var 1)) (sndT (var 1)) (var 0)) (var 0)
def matchBit (m w : PTm n) : PTm n := allB matchBody m (pairT m w)
@[simp] theorem subst_matchBit {l : ℕ} (σ : Fin n → PTm l) (m w : PTm n) :
    Syn.subst σ (matchBit m w) = matchBit (Syn.subst σ m) (Syn.subst σ w) := by simp [matchBit,allB]

theorem match_body_at (m w i : PTm n) : Γ ⊢[PRAAx] inst2 matchBody i (pairT m w) ≐ eqb (digit m w i) i := by
  simp only [matchBody,inst2,subst_eqb,Foundations.RuntimePermutationWords.subst_digit,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact AnalyticNumberTheory.Euler.congrEqb
    (Foundations.RuntimeAdjacentPermutationSwap.digit_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)) (.eqRefl _)
theorem matched_digit (m w i : PTm n) (h : Γ ⊢[PRAAx] matchBit m w ≐ one) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    digit m w i ≐ i := by
  have no := Foundations.BoundedReflection.all_elim (f := matchBody) h hi
  apply AnalyticNumberTheory.Valuation.eq_of_eqb_ne
  exact .impI (.impE no.wk ((match_body_at _ _ _).eqTrans Prf.hyp0))

theorem matched_word (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (h : Γ ⊢[PRAAx] matchBit m w ≐ one) : Γ ⊢[PRAAx] w ≐ identityWord m := by
  apply Foundations.RuntimePermutationWords.word_unique _ _ _ hw (identity_word_bound m)
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] matchBit (Syn.shift m) (Syn.shift w) ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_matchBit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using h.shift
  have e := (Foundations.RuntimePermutationWords.word_lookup
    (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (Syn.shift m) (Syn.shift w) (var 0) Prf.hyp0).eqTrans
      ((matched_digit _ _ _ hs.wk Prf.hyp0).eqTrans
        ((identity_digit _ _ Prf.hyp0).eqSymm.eqTrans (Foundations.RuntimePermutationWords.word_lookup _ _ _ Prf.hyp0).eqSymm))
  simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_word,subst_identityWord] using e

theorem different_word_fails (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hne : Γ ⊢[PRAAx] neg (w ≐ identityWord m)) : Γ ⊢[PRAAx] matchBit m w ≐ zero := by
  refine .orE (Foundations.BoundedReflection.all_cases matchBody m (pairT m w)) Prf.hyp0 ?_
  exact .botE _ (.impE hne.wk (matched_word _ _ hw.wk Prf.hyp0))

theorem different_word_product_zero (m w : PTm n) (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hne : Γ ⊢[PRAAx] neg (w ≐ identityWord m)) : Γ ⊢[PRAAx] rawProduct (identityTable m) m w ≐ qzero := by
  have failed := Foundations.BoundedReflection.all_fail (f := matchBody) (different_word_fails _ _ hw hne)
  let c := Search.mu matchBody m (pairT m w)
  have hc : Γ ⊢[PRAAx] lt c m := .andE₁ failed
  have ne : Γ ⊢[PRAAx] neg (digit m w c ≐ c) := AnalyticNumberTheory.Valuation.ne_of_eqb_zero
    ((match_body_at _ _ _).eqSymm.eqTrans (.andE₂ failed))
  have factor := (GaussianScalarDeterminant.factor_body_at (Γ := Γ) (identityTable m) m w c).eqTrans
    ((identity_lookup _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ hc) hc).eqTrans
      (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne))
  exact GaussianRationalProductAlgebra.product_zero_at factorBody m c (factorData (identityTable m) m w) hc factor

theorem selected_term_one (m r : PTm n) (he : Γ ⊢[PRAAx] GaussianPolynomialDeterminant.wordCode m r ≐ identityWord m) : Γ ⊢[PRAAx]
    signedTerm (identityTable m) m r ≐ qone :=
  (qmul_congr (GaussianDeterminantSignTransport.sign_congr (.eqRefl _) he)
    (GaussianRationalFiniteProduct.product_index_congr factorBody (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) he)))).eqTrans
      ((qmul_congr (identity_sign m) (identity_product m)).eqTrans (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
theorem other_term_zero (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m))
    (hne : Γ ⊢[PRAAx] neg (r ≐ identityRank m)) : Γ ⊢[PRAAx] signedTerm (identityTable m) m r ≐ qzero := by
  have nw : Γ ⊢[PRAAx] neg (GaussianPolynomialDeterminant.wordCode m r ≐ identityWord m) := by
    refine .impI (.impE hne.wk ?_)
    exact retained_position_unique m r (identityRank m) hr.wk (identity_rank_bound m).wk
      (Prf.hyp0.eqTrans (identity_rank_word m).wk.eqSymm)
  exact (qmul_congr (.eqRefl _) (different_word_product_zero _ _ (retained_bound m r hr) nw)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

/-- The SAME actual retained determinant scan has one nonzero summand. -/
theorem identity_det (m : PTm n) : Γ ⊢[PRAAx] scalarDet (identityTable m) m ≐ qone := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual signedBody
      GaussianRationalMonicReconstruction.spikeBody (count m) (pairT (identityTable m) m)
      (GaussianRationalMonicReconstruction.spikeData (identityRank m) qone) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (count m)) :: Γ.map Fm.shift
    have rr : Δ ⊢[PRAAx] lt (var 0) (count (Syn.shift m)) := by
      simpa only [Δ,Syn.shift,Foundations.RuntimePermutationWords.subst_count] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have e : Δ ⊢[PRAAx] signedTerm (identityTable (Syn.shift m)) (Syn.shift m) (var 0) ≐
        GaussianRationalMonicReconstruction.spike (identityRank (Syn.shift m)) qone (var 0) := by
      refine .orE (eq_or_ne (var 0) (identityRank (Syn.shift m))) ?_ ?_
      · have word : ((var 0) ≐ identityRank (Syn.shift m)) :: Δ ⊢[PRAAx]
            GaussianPolynomialDeterminant.wordCode (Syn.shift m) (var 0) ≐ identityWord (Syn.shift m) :=
          (entry_congr (.eqRefl _) Prf.hyp0).eqTrans (identity_rank_word (Syn.shift m))
        exact (selected_term_one _ _ word).eqTrans (GaussianRationalMonicReconstruction.spike_hit _ _ _ Prf.hyp0).eqSymm
      · exact (other_term_zero _ _ rr.wk Prf.hyp0).eqTrans (GaussianRationalMonicReconstruction.spike_miss _ _ _ Prf.hyp0).eqSymm
    have actual := (GaussianScalarDeterminant.signed_body_at (Γ := Δ) (identityTable (Syn.shift m)) (Syn.shift m) (var 0)).eqTrans
      (e.eqTrans (GaussianRationalMonicReconstruction.spike_body_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,subst_identityTable,subst_identityRank,subst_pairT,
      GaussianRationalMonicReconstruction.subst_spikeData,GaussianRationalSyntheticDivision.subst_qone] using actual
  exact (GaussianScalarDeterminant.scalar_leibniz _ _).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      ((GaussianRationalMonicReconstruction.spike_sum _ _ _ qone_canonical).eqTrans
        (GaussianRationalMonicReconstruction.active_on _ _ _ (identity_rank_bound m))))

theorem identity_length (m : PTm n) : Γ ⊢[PRAAx] length (identityTable m) ≐ m :=
  GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem identity_row_length (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (identityTable m) r) ≐ m := GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ hr
theorem identity_cell_canonical (m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (identityTable m) r j) :=
  GaussianRationalHorner.canonical_congr (identity_lookup _ _ _ hr hj) (GaussianRationalFiberVandermonde.delta_canonical _ _)

/-- A bounded local identity-table certificate, not a determinant conclusion. -/
def identityRow (A m r : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ cell (Syn.shift A) (Syn.shift r) (var 0) ≐ delta (Syn.shift r) (var 0))
def identityEntries (A m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ identityRow (Syn.shift A) (Syn.shift m) (var 0))
@[simp] theorem subst_identityRow {l : ℕ} (σ : Fin n → PTm l) (A m r : PTm n) :
    (identityRow A m r).subst σ = identityRow (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ r) := by
  simp [identityRow,cell,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_identityEntries {l : ℕ} (σ : Fin n → PTm l) (A m : PTm n) :
    (identityEntries A m).subst σ = identityEntries (Syn.subst σ A) (Syn.subst σ m) := by
  simp [identityEntries,cell,Syn.subst_shift,Syn.shift_subst]
theorem identity_entry_at (A m r j : PTm n) (h : Γ ⊢[PRAAx] identityEntries A m)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] cell A r j ≐ delta r j := by
  have first : Γ ⊢[PRAAx] lt r m ⟶ identityRow A m r := by
    simpa [identityEntries] using h.allE r
  have second : Γ ⊢[PRAAx] lt j m ⟶ cell A r j ≐ delta r j := by
    simpa [identityRow] using (Prf.impE first hr).allE j
  exact .impE second hj

/-- Native field-equal identity cells suffice, without canonical raw input tables. -/
theorem identity_det_of_values (A m : PTm n)
    (h : Γ ⊢[PRAAx] GaussianScalarDeterminant.scalarCellsEqual A (identityTable m) m) : Γ ⊢[PRAAx]
    scalarDet A m ≐ qone := (GaussianScalarDeterminant.scalar_det_congr _ _ _ h).eqTrans (identity_det m)
theorem identity_det_of_entries (A m : PTm n) (h : Γ ⊢[PRAAx] identityEntries A m) : Γ ⊢[PRAAx]
    scalarDet A m ≐ qone := by
  apply identity_det_of_values
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
  have hs : Δ ⊢[PRAAx] identityEntries (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_identityEntries,Syn.shift] using h.shift.shift.wk.wk
  have e := (identity_entry_at _ _ _ _ hs rr jj).eqTrans (identity_lookup _ _ _ rr jj).eqSymm
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_identityTable] using
    GaussianRationalValueEquality.value_equal_of_code e

/-- Original table, genuine retained index/word, SAME scalar-det program and its value. -/
def output (m : PTm n) : PTm n := pairT (identityTable m)
  (pairT (identityRank m) (pairT (identityWord m) (pairT
    (GaussianScalarDeterminant.run (identityTable m) m) (scalarDet (identityTable m) m))))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (m : PTm n) : PTm n := ap1 outputF m
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (output m) = output (Syn.subst σ m) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (run m) = run (Syn.subst σ m) := by simp [run]
theorem program_at (m : PTm n) : Γ ⊢[PRAAx] run m ≐ output m := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![m]
theorem returned_table (m : PTm n) : Γ ⊢[PRAAx] fstT (run m) ≐ identityTable m :=
  (congrFst (program_at _)).eqTrans (fst_pair _ _)
theorem returned_rank (m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run m)) ≐ identityRank m :=
  (congrFst ((congrSnd (program_at _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_word (m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run m))) ≐ identityWord m :=
  (congrFst ((congrSnd ((congrSnd (program_at _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_scalar_run (m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run m)))) ≐
    GaussianScalarDeterminant.run (identityTable m) m :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_value (m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run m)))) ≐ scalarDet (identityTable m) m :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_value_one (m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run m)))) ≐ qone :=
  (returned_value m).eqTrans (identity_det m)

theorem actual_identity_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (scalarDet (identityTable (var 0)) (var 0) ≐ qone) := closeUniv 1 (identity_det _)
theorem actual_identity_rank_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((lt (identityRank (var 0)) (count (var 0))) ⋏
      GaussianPolynomialDeterminant.wordCode (var 0) (identityRank (var 0)) ≐ identityWord (var 0)) :=
  closeUniv 1 (.andI (identity_rank_bound _) (identity_rank_word _))
theorem actual_identity_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (signPoint (var 0) (identityWord (var 0)) ≐ qone) := closeUniv 1 (identity_sign _)
theorem actual_identity_factor_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (rawProduct (identityTable (var 0)) (var 0) (identityWord (var 0)) ≐ qone) := closeUniv 1 (identity_product _)
theorem actual_identity_entries_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (identityEntries (var 0) (var 1) ⟶ scalarDet (var 0) (var 1) ≐ qone) :=
  closeUniv 2 (.impI (identity_det_of_entries _ _ Prf.hyp0))
theorem actual_identity_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((run (var 0) ≐ output (var 0)) ⋏ (sndT (sndT (sndT (sndT (run (var 0))))) ≐ qone)) :=
  closeUniv 1 (.andI (program_at _) (returned_value_one _))

end LeanProofs.IPRA.Analysis.GaussianScalarIdentityDeterminant

import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarIdentityDeterminant

/-!
# Actual diagonal row scaling and its numerical scalar determinant

A stored scalar table has d in the first t diagonal positions and one in
all later positions, with zero off the diagonal. Its real product action
is derived from the existing delta sum. The SAME retained determinant scan
has only the computed identity summand, and its value is the actual power
d^t when t<=m. Original scalar and table codes may be raw or zero. No
matrix action, determinant, product or nonzero-weight law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDiagonalDeterminant

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (delta table table_lookup)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell signPoint)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct (qprod product_zero product_succ product_index_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_zero power_succ power_canonical)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (d t r : PTm n) : PTm n := sel (Signum.sg (monus t r)) d qone
def diagonalData (d t : PTm n) : PTm n := pairT d t
def diagonalBody : PTm 3 := qmul (delta (var 0) (var 1)) (weight (fstT (var 2)) (sndT (var 2)) (var 0))
def diagonal (d t m : PTm n) : PTm n := table diagonalBody m m (diagonalData d t)
def weightBody : PTm 2 := weight (fstT (var 1)) (sndT (var 1)) (var 0)
def weightProduct (d t k : PTm n) : PTm n := qprod weightBody k (diagonalData d t)
ipra_subst weight [sel]
ipra_subst diagonalData
ipra_subst diagonal
ipra_subst weightProduct
theorem weight_upper (d t r : PTm n) (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx] weight d t r ≐ d :=
  sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem weight_lower (d t r : PTm n) (hr : Γ ⊢[PRAAx] le t r) : Γ ⊢[PRAAx] weight d t r ≐ qone :=
  sel_zero (Foundations.BoundedFormulas.sg_of_zero hr)
theorem weight_congr {d e t u r s : PTm n} (hd : Γ ⊢[PRAAx] d ≐ e)
    (ht : Γ ⊢[PRAAx] t ≐ u) (hr : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx] weight d t r ≐ weight e u s := by
  ipra_congr (weight (var 0) (var 1) (var 2) : PTm 3) with [hd, ht, hr]
theorem diagonal_lookup (d t m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (diagonal d t m) r j ≐ qmul (delta r j) (weight d t r) := by
  have e : Γ ⊢[PRAAx] cell (diagonal d t m) r j ≐ qmul (delta r j) (weight (fstT (diagonalData d t)) (sndT (diagonalData d t)) r) := by
    simpa [diagonal,diagonalBody] using table_lookup diagonalBody m m (diagonalData d t) r j hr hj
  exact e.eqTrans (qmul_congr (.eqRefl _) (weight_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)))
theorem diagonal_length (d t m : PTm n) : Γ ⊢[PRAAx] length (diagonal d t m) ≐ m :=
  GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem diagonal_row_length (d t m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (diagonal d t m) r) ≐ m := GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ hr
theorem diagonal_shape (d t m : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (diagonal d t m) m := by
  refine .andI (diagonal_length _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_diagonal] using
    diagonal_row_length (Syn.shift d) (Syn.shift t) (Syn.shift m) (var 0) Prf.hyp0
theorem diagonal_cell_canonical (d t m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (diagonal d t m) r j) :=
  GaussianRationalHorner.canonical_congr (diagonal_lookup _ _ _ _ _ hr hj) (GaussianRationalHorner.qmul_canonical _ _)
theorem weight_body_at (d t i : PTm n) : Γ ⊢[PRAAx] inst2 weightBody i (diagonalData d t) ≐ weight d t i := by
  simp only [weightBody,inst2,subst_weight,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact weight_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

/-- Genuine guarded QF prefix, so the first t factors really are d. -/
theorem weight_prefix (d t k : PTm n) (hk : Γ ⊢[PRAAx] le k t) : Γ ⊢[PRAAx] weightProduct d t k ≐ power d k := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift t) ⟶ weightProduct (Syn.shift d) (Syn.shift t) (var 0) ≐ power (Syn.shift d) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, subst_weightProduct, GaussianRationalReciprocal.subst_power]
    · exact .impI ((product_zero _ _).eqTrans (power_zero _).eqSymm)
    · refine .impI ?_
      exact (product_succ _ _ _).eqTrans
        ((qmul_congr (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
          ((weight_body_at _ _ _).eqTrans (weight_upper _ _ _ Prf.hyp0))).eqTrans (power_succ _ _).eqSymm)
  have rule : Γ ⊢[PRAAx] le k t ⟶ weightProduct d t k ≐ power d k := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,subst_weightProduct,GaussianRationalReciprocal.subst_power,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem weight_tail (d t k : PTm n) : Γ ⊢[PRAAx]
    qprod (offB weightBody) k (pairT t (diagonalData d t)) ≐ qone := by
  apply GaussianRationalProductAlgebra.product_one_of_terms
  refine .allI (.impI ?_)
  have e := (GaussianRationalFiniteProduct.offset_at (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift)
    weightBody (Syn.shift t) (var 0) (diagonalData (Syn.shift d) (Syn.shift t))).eqTrans
      ((weight_body_at _ _ _).eqTrans (weight_lower _ _ _ (le_add_right _ _)))
  simpa only [GaussianRationalProductAlgebra.oneTerms,Syn.shift,subst_pairT,subst_diagonalData] using e

theorem weight_product (d t m : PTm n) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx] weightProduct d t m ≐ power d t :=
  (product_index_congr weightBody (eq_add_of_le ht) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteProduct.product_split _ _ _ _).eqTrans
      ((qmul_congr (weight_prefix _ _ _ (le_refl _)) (weight_tail _ _ _)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (power_canonical _ _))))


/-- The identity factors are recoded original weights; raw d is never
silently identified with a normalized qone*d. -/
theorem identity_product (d t m : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.rawProduct (diagonal d t m) m (GaussianScalarIdentityDeterminant.identityWord m) ≐ weightProduct d t m := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianScalarDeterminant.factorBody
      (GaussianRationalFiniteProduct.recodeBody weightBody) m
      (GaussianScalarDeterminant.factorData (diagonal d t m) m (GaussianScalarIdentityDeterminant.identityWord m)) (diagonalData d t) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have idig := GaussianScalarIdentityDeterminant.identity_digit (Γ := Δ) (Syn.shift m) (var 0) Prf.hyp0
    have e := (GaussianScalarDeterminant.factor_body_at (Γ := Δ) (diagonal (Syn.shift d) (Syn.shift t) (Syn.shift m)) (Syn.shift m)
      (GaussianScalarIdentityDeterminant.identityWord (Syn.shift m)) (var 0)).eqTrans
        ((diagonal_lookup _ _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0).eqTrans
          ((qmul_congr (GaussianRationalLagrangeCardinals.delta_equal _ _ idig) (weight_congr (.eqRefl _) (.eqRefl _) idig)).eqTrans
            ((GaussianRationalFiniteProduct.raw_one_left _).eqTrans (recode_congr (weight_body_at _ _ _)).eqSymm)))
    simpa only [Δ,Syn.shift,GaussianScalarDeterminant.subst_factorData,subst_diagonal,
      GaussianScalarIdentityDeterminant.subst_identityWord,subst_diagonalData,GaussianRationalFiniteProduct.recode_body_at] using e
  exact (GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ terms).eqTrans
    (GaussianRationalFiniteProduct.product_recode weightBody m (diagonalData d t))

/-- The least mismatching digit comes from the actual finite equality test.
No diagonal weight is assumed nonzero. -/
theorem different_word_product_zero (d t m w : PTm n)
    (hw : Γ ⊢[PRAAx] lt w (Foundations.RuntimePermutationWords.horizon m))
    (hne : Γ ⊢[PRAAx] neg (w ≐ GaussianScalarIdentityDeterminant.identityWord m)) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.rawProduct (diagonal d t m) m w ≐ qzero := by
  have failed := Foundations.BoundedReflection.all_fail (f := GaussianScalarIdentityDeterminant.matchBody)
    (GaussianScalarIdentityDeterminant.different_word_fails m w hw hne)
  let c := Search.mu GaussianScalarIdentityDeterminant.matchBody m (pairT m w)
  have hc : Γ ⊢[PRAAx] lt c m := .andE₁ failed
  have ne : Γ ⊢[PRAAx] neg (Foundations.RuntimePermutationWords.digit m w c ≐ c) :=
    AnalyticNumberTheory.Valuation.ne_of_eqb_zero
      ((GaussianScalarIdentityDeterminant.match_body_at _ _ _).eqSymm.eqTrans (.andE₂ failed))
  have factor := (GaussianScalarDeterminant.factor_body_at (Γ := Γ) (diagonal d t m) m w c).eqTrans
    ((diagonal_lookup _ _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ hc) hc).eqTrans
      ((qmul_congr (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _)))
  exact GaussianRationalProductAlgebra.product_zero_at GaussianScalarDeterminant.factorBody m c
    (GaussianScalarDeterminant.factorData (diagonal d t m) m w) hc factor

theorem identity_term (d t m r : PTm n)
    (he : Γ ⊢[PRAAx] GaussianPolynomialDeterminant.wordCode m r ≐ GaussianScalarIdentityDeterminant.identityWord m) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.signedTerm (diagonal d t m) m r ≐ weightProduct d t m :=
  (qmul_congr (GaussianDeterminantSignTransport.sign_congr (.eqRefl _) he)
    (product_index_congr GaussianScalarDeterminant.factorBody (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) he)))).eqTrans
      ((qmul_congr (GaussianScalarIdentityDeterminant.identity_sign m) (identity_product d t m)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalFiniteProduct.product_canonical _ _ _)))
theorem other_term_zero (d t m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (Foundations.RuntimePermutationWords.count m))
    (hne : Γ ⊢[PRAAx] neg (r ≐ GaussianScalarIdentityDeterminant.identityRank m)) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.signedTerm (diagonal d t m) m r ≐ qzero := by
  have nw : Γ ⊢[PRAAx] neg (GaussianPolynomialDeterminant.wordCode m r ≐ GaussianScalarIdentityDeterminant.identityWord m) := by
    refine .impI (.impE hne.wk ?_)
    exact Foundations.RuntimePermutationWords.retained_position_unique m r (GaussianScalarIdentityDeterminant.identityRank m) hr.wk
      (GaussianScalarIdentityDeterminant.identity_rank_bound m).wk
      (Prf.hyp0.eqTrans (GaussianScalarIdentityDeterminant.identity_rank_word m).wk.eqSymm)
  exact (qmul_congr (.eqRefl _) (different_word_product_zero d t m _ (Foundations.RuntimePermutationWords.retained_bound m r hr) nw)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

/-- The same retained signed scan, with its actual identity rank, reduces
to the real diagonal weight fold. This theorem is unconditional in t. -/
theorem diagonal_det_weights (d t m : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarDet (diagonal d t m) m ≐ weightProduct d t m := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianScalarDeterminant.signedBody
      GaussianRationalMonicReconstruction.spikeBody (Foundations.RuntimePermutationWords.count m) (pairT (diagonal d t m) m)
      (GaussianRationalMonicReconstruction.spikeData (GaussianScalarIdentityDeterminant.identityRank m) (weightProduct d t m)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift
    have rr : Δ ⊢[PRAAx] lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift m)) := by
      simpa only [Δ,Syn.shift,Foundations.RuntimePermutationWords.subst_count] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have e : Δ ⊢[PRAAx] GaussianScalarDeterminant.signedTerm (diagonal (Syn.shift d) (Syn.shift t) (Syn.shift m)) (Syn.shift m) (var 0) ≐
        GaussianRationalMonicReconstruction.spike (GaussianScalarIdentityDeterminant.identityRank (Syn.shift m)) (weightProduct (Syn.shift d) (Syn.shift t) (Syn.shift m)) (var 0) := by
      refine .orE (eq_or_ne (var 0) (GaussianScalarIdentityDeterminant.identityRank (Syn.shift m))) ?_ ?_
      · have word : ((var 0) ≐ GaussianScalarIdentityDeterminant.identityRank (Syn.shift m)) :: Δ ⊢[PRAAx]
            GaussianPolynomialDeterminant.wordCode (Syn.shift m) (var 0) ≐ GaussianScalarIdentityDeterminant.identityWord (Syn.shift m) :=
          (Foundations.SequenceComposition.entry_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianScalarIdentityDeterminant.identity_rank_word _)
        exact (identity_term _ _ _ _ word).eqTrans (GaussianRationalMonicReconstruction.spike_hit _ _ _ Prf.hyp0).eqSymm
      · exact (other_term_zero _ _ _ _ rr.wk Prf.hyp0).eqTrans (GaussianRationalMonicReconstruction.spike_miss _ _ _ Prf.hyp0).eqSymm
    have actual := (GaussianScalarDeterminant.signed_body_at (Γ := Δ) (diagonal (Syn.shift d) (Syn.shift t) (Syn.shift m)) (Syn.shift m) (var 0)).eqTrans
      (e.eqTrans (GaussianRationalMonicReconstruction.spike_body_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,subst_diagonal,subst_weightProduct,subst_pairT,GaussianScalarIdentityDeterminant.subst_identityRank,
      GaussianRationalMonicReconstruction.subst_spikeData] using actual
  exact (GaussianScalarDeterminant.scalar_leibniz _ _).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      ((GaussianRationalMonicReconstruction.spike_sum _ _ _ (GaussianRationalFiniteProduct.product_canonical _ _ _)).eqTrans
        (GaussianRationalMonicReconstruction.active_on _ _ _ (GaussianScalarIdentityDeterminant.identity_rank_bound m))))

theorem diagonal_det (d t m : PTm n) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarDet (diagonal d t m) m ≐ power d t :=
  (diagonal_det_weights _ _ _).eqTrans (weight_product _ _ _ ht)


/-- This actual reader stores the original raw right table and queried row
and column; its product output is canonical even when all inputs are raw. -/
def actionData (d t E r j : PTm n) : PTm n := pairT d (pairT t (pairT E (pairT r j)))
def actionFields (p : PTm n) (i : Fin 5) : PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))] i
def actionBody : PTm 2 := qmul (weight (actionFields (var 1) 0) (actionFields (var 1) 1) (actionFields (var 1) 3))
  (cell (actionFields (var 1) 2) (var 0) (actionFields (var 1) 4))
ipra_subst actionData
@[simp] theorem subst_actionFields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (actionFields p i) = actionFields (Syn.subst σ p) i := by fin_cases i <;> simp [actionFields]
theorem action_fields_at (d t E r j : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    actionFields (actionData d t E r j) i ≐ ![d,t,E,r,j] i := by
  fin_cases i
  · exact fst_pair _ _
  · exact (snd_pair _ _).fstE
  · exact (snd_pair _ _).sndE.fstE
  · exact (snd_pair _ _).sndE.sndE.fstE
  · exact (snd_pair _ _).sndE.sndE.sndE
theorem action_body_at (d t E r j k : PTm n) : Γ ⊢[PRAAx]
    inst2 actionBody k (actionData d t E r j) ≐ qmul (weight d t r) (cell E k j) := by
  simp only [actionBody,inst2,GaussianRationalHorner.subst_qmul,subst_weight,GaussianPolynomialDeterminantTerms.subst_cell,
    subst_actionFields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (weight_congr (action_fields_at _ _ _ _ _ 0) (action_fields_at _ _ _ _ _ 1) (action_fields_at _ _ _ _ _ 3))
    (Foundations.SequenceComposition.entry_congr
      (Foundations.SequenceComposition.entry_congr (action_fields_at _ _ _ _ _ 2) (.eqRefl _)) (action_fields_at _ _ _ _ _ 4))

theorem diagonal_dot (d t m E r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    GaussianRationalMatrixFiniteSums.scalarDot (diagonal d t m) E m r j ≐ qmul (weight d t r) (cell E r j) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianRationalMatrixFiniteSums.scalarBody
      (GaussianRationalMatrixFiniteSums.deltaBody actionBody) m
      (GaussianRationalMatrixFiniteSums.scalarData (diagonal d t m) E r j) (pairT r (actionData d t E r j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e := (GaussianRationalMatrixFiniteSums.scalar_body_at (Γ := Δ) (diagonal (Syn.shift d) (Syn.shift t) (Syn.shift m))
      (Syn.shift E) (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
        ((qmul_congr (diagonal_lookup _ _ _ _ _ rs.wk Prf.hyp0) (.eqRefl _)).eqTrans
          ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
            ((qmul_congr (.eqRefl _) (action_body_at _ _ _ _ _ _).eqSymm).eqTrans
              (GaussianRationalMatrixFiniteSums.delta_body_at _ _ _ _).eqSymm)))
    simpa only [Δ,Syn.shift,GaussianRationalMatrixFiniteSums.subst_scalarData,subst_diagonal,subst_pairT,subst_actionData] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta_canonical actionBody m r (actionData d t E r j) hr
      (GaussianRationalHorner.canonical_congr (action_body_at _ _ _ _ _ _) (GaussianRationalHorner.qmul_canonical _ _))).eqTrans
        (action_body_at _ _ _ _ _ _))

/-- Exact action of the SAME actual scalar matrix product. No shape,
canonical-cell, nonzero-weight or t<=m hypothesis is needed here. -/
theorem diagonal_left_action (d t m E r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (GaussianRationalMatrixFiniteSums.matrixProduct (diagonal d t m) E m) r j ≐ qmul (weight d t r) (cell E r j) :=
  (GaussianRationalMatrixFiniteSums.product_lookup _ _ _ _ _ hr hj).eqTrans (diagonal_dot _ _ _ _ _ _ hr)


theorem empty_diagonal (d t : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarDet (diagonal d t zero) zero ≐ qone :=
  GaussianPolynomialDeterminant.empty_evaluation _ _ _
theorem zero_weight_count (d m : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarDet (diagonal d zero m) m ≐ qone :=
  (diagonal_det _ _ _ (zero_le _)).eqTrans (power_zero _)
theorem one_diagonal_raw (d : PTm n) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarDet (diagonal d one one) one ≐ recode d :=
  (diagonal_det _ _ _ (le_refl _)).eqTrans ((power_succ d zero).eqTrans
    ((qmul_congr (power_zero d) (.eqRefl _)).eqTrans (GaussianRationalFiniteProduct.raw_one_left _)))

/-- Four actual fields retain the generated table, SAME scalar-det run,
its real value and the independently computed numerical power. -/
def output (d t m : PTm n) : PTm n := pairT (diagonal d t m)
  (pairT (GaussianScalarDeterminant.run (diagonal d t m) m)
    (pairT (GaussianScalarDeterminant.scalarDet (diagonal d t m) m) (power d t)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (d t m : PTm n) : PTm n := ap3 outputF d t m
ipra_subst output
ipra_subst run
theorem program_at (d t m : PTm n) : Γ ⊢[PRAAx] run d t m ≐ output d t m := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2)) ![d,t,m]
theorem returned_table (d t m : PTm n) : Γ ⊢[PRAAx] fstT (run d t m) ≐ diagonal d t m :=
  (program_at _ _ _).fstE
theorem returned_scalar_run (d t m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run d t m)) ≐ GaussianScalarDeterminant.run (diagonal d t m) m :=
  (program_at _ _ _).sndE.fstE
theorem returned_value (d t m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run d t m))) ≐ GaussianScalarDeterminant.scalarDet (diagonal d t m) m :=
  (program_at _ _ _).sndE.sndE.fstE
theorem returned_power (d t m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run d t m))) ≐ power d t :=
  (program_at _ _ _).sndE.sndE.sndE
theorem returned_det_power (d t m : PTm n) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run d t m))) ≐ sndT (sndT (sndT (run d t m))) :=
  (returned_value _ _ _).eqTrans ((diagonal_det _ _ _ ht).eqTrans (returned_power _ _ _).eqSymm)
theorem returned_value_canonical (d t m : PTm n) : Γ ⊢[PRAAx] canonical (fstT (sndT (sndT (run d t m)))) :=
  GaussianRationalHorner.canonical_congr (returned_value _ _ _) (GaussianScalarDeterminant.scalar_det_canonical _ _)

/-! Closed ordinary PRA endpoints keep every weight, matrix, size, count,
row and column query numerical. The only determinant-power guard is t<=m. -/
theorem actual_weight_branches_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((lt (var 2) (var 1) ⟶ weight (var 0) (var 1) (var 2) ≐ var 0) ⋏
      (le (var 1) (var 2) ⟶ weight (var 0) (var 1) (var 2) ≐ qone)) :=
  closeUniv 3 (.andI (.impI (weight_upper _ _ _ Prf.hyp0)) (.impI (weight_lower _ _ _ Prf.hyp0)))
theorem actual_diagonal_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMatrixFiniteSums.squareShape (diagonal (var 0) (var 1) (var 2)) (var 2)) :=
  closeUniv 3 (diagonal_shape _ _ _)
theorem actual_diagonal_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 2) ⟶ lt (var 4) (var 2) ⟶
      (cell (diagonal (var 0) (var 1) (var 2)) (var 3) (var 4) ≐ qmul (delta (var 3) (var 4)) (weight (var 0) (var 1) (var 3))) ⋏
        canonical (cell (diagonal (var 0) (var 1) (var 2)) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.andI (diagonal_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0) (diagonal_cell_canonical _ _ _ _ _ Prf.hyp1 Prf.hyp0))))
theorem actual_diagonal_weight_fold_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianScalarDeterminant.scalarDet (diagonal (var 0) (var 1) (var 2)) (var 2) ≐ weightProduct (var 0) (var 1) (var 2)) :=
  closeUniv 3 (diagonal_det_weights _ _ _)
theorem actual_diagonal_det_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ GaussianScalarDeterminant.scalarDet (diagonal (var 0) (var 1) (var 2)) (var 2) ≐ power (var 0) (var 1)) :=
  closeUniv 3 (.impI (diagonal_det _ _ _ Prf.hyp0))
theorem actual_diagonal_left_action_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      cell (GaussianRationalMatrixFiniteSums.matrixProduct (diagonal (var 0) (var 1) (var 2)) (var 3) (var 2)) (var 4) (var 5) ≐
        qmul (weight (var 0) (var 1) (var 4)) (cell (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (diagonal_left_action _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_empty_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianScalarDeterminant.scalarDet (diagonal (var 0) (var 1) zero) zero ≐ qone) := closeUniv 2 (empty_diagonal _ _)
theorem actual_raw_singleton_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianScalarDeterminant.scalarDet (diagonal (var 0) one one) one ≐ recode (var 0)) := closeUniv 1 (one_diagonal_raw _)
theorem actual_diagonal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_diagonal_det_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶
      ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ⋏
        canonical (fstT (sndT (sndT (run (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.impI (.andI (returned_det_power _ _ _ Prf.hyp0) (returned_value_canonical _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianScalarDiagonalDeterminant

import IPRADerivations.Analysis.RationalPolynomialProductGaussianEmbedding
import IPRADerivations.Analysis.RationalScalarDeterminantGaussianEmbedding
import IPRADerivations.Analysis.GaussianPolynomialDeterminantTerms
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Original rational polynomial determinant terms and coefficient embedding

Numerical cells are original descending rational coefficient lists. Actual
rational product stages use the same column-position word reader. The
embedded table stores the original declared coefficient prefixes, and the
stage coefficient invariant is derived by compiled bounded QF induction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantTermsGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed scalarOne)
open RationalPolynomialGaussianEmbedding (coefficients coefficient_lookup coefficients_length embed_congr)
open GaussianPolynomialDeterminantTerms (cell factor data tableShape rowCells)
open GaussianRationalFiberVandermonde (table table_lookup table_length table_row_length)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cellBody : PTm 3 := coefficients (cell (fstT (var 2)) (var 0) (var 1)) (succ (sndT (var 2)))
def embeddedTable (M m L : PTm n) : PTm n := table cellBody m m (pairT M L)
@[simp] theorem subst_embeddedTable {l : ℕ} (σ : Fin n → PTm l) (M m L : PTm n) :
    Syn.subst σ (embeddedTable M m L) = embeddedTable (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by simp [embeddedTable]
theorem coefficients_congr {C D N K : PTm n} (hC : Γ ⊢[PRAAx] C ≐ D) (hN : Γ ⊢[PRAAx] N ≐ K) : Γ ⊢[PRAAx]
    coefficients C N ≐ coefficients D K :=
  (RationalPolynomialGaussianEmbedding.coefficients_at _ _).eqSymm.eqTrans
    ((congrAp2 RationalPolynomialGaussianEmbedding.coefficientsF hC hN).eqTrans (RationalPolynomialGaussianEmbedding.coefficients_at _ _))
theorem table_cell (M m L r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (embeddedTable M m L) r j ≐ coefficients (cell M r j) (succ L) := by
  have e : Γ ⊢[PRAAx] cell (embeddedTable M m L) r j ≐
      coefficients (cell (fstT (pairT M L)) r j) (succ (sndT (pairT M L))) := by
    simpa [embeddedTable,cellBody] using table_lookup cellBody m m (pairT M L) r j hr hj
  exact e.eqTrans (coefficients_congr (entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (.eqRefl _)) (congrSucc (snd_pair _ _)))
theorem table_cell_length (M m L r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell (embeddedTable M m L) r j) ≐ succ L := (congrFst (table_cell M m L r j hr hj)).eqTrans (coefficients_length _ _)
theorem embedded_row_cells (M m L r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] rowCells (embeddedTable M m L) m L r := by
  refine .allI (.impI ?_)
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  simpa only [Syn.shift,subst_embeddedTable,ConciseIPRA.PTm.subst_succ] using
    table_cell_length (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift r) (var 0) hrs.wk Prf.hyp0
theorem embedded_shape (M m L : PTm n) : Γ ⊢[PRAAx] tableShape (embeddedTable M m L) m L := by
  refine .andI (table_length _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_embeddedTable,embeddedTable,GaussianRationalFiberVandermonde.subst_table,subst_pairT] using
      table_row_length cellBody (Syn.shift m) (Syn.shift m) (pairT (Syn.shift M) (Syn.shift L)) (var 0) Prf.hyp0
  · simpa only [Syn.shift,subst_embeddedTable] using embedded_row_cells (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) Prf.hyp0
theorem embedded_factor (M m L w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    factor (embeddedTable M m L) m w j ≐ coefficients (factor M m w j) (succ L) :=
  table_cell M m L _ j (Foundations.RuntimePermutationWords.digit_bound m w j hj) hj

def entriesEqual (P Q N : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ entry (Syn.shift P) (var 0) ≐ entry (Syn.shift Q) (var 0))
@[simp] theorem subst_entriesEqual {l : ℕ} (σ : Fin n → PTm l) (P Q N : PTm n) :
    (entriesEqual P Q N).subst σ = entriesEqual (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ N) := by
  simp [entriesEqual,Syn.subst_shift,Syn.shift_subst]
theorem entry_equal_at (P Q N i : PTm n) (h : Γ ⊢[PRAAx] entriesEqual P Q N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry P i ≐ entry Q i := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ entry P i ≐ entry Q i := by simpa [entriesEqual] using h.allE i
  exact .impE rule hi
theorem coefficient_left_entries (P P' Q M H t k : PTm n) (h : Γ ⊢[PRAAx] entriesEqual P P' H)
    (ht : Γ ⊢[PRAAx] le t H) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialProduct.coefficient P Q M t k ≐ GaussianRationalPolynomialProduct.coefficient P' Q M t k := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (Syn.shift P) (Syn.shift P') (Syn.shift H) := by
    simpa only [Fm.shift,subst_entriesEqual,Syn.shift] using h.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift H) := by simpa only [Fm.shift,subst_le,Syn.shift] using ht.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ t _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
  have term : Δ ⊢[PRAAx] GaussianRationalPolynomialProduct.contribution (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0) ≐
      GaussianRationalPolynomialProduct.contribution (Syn.shift P') (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0) := by
    refine .orE (lt_or_le (Syn.shift k) (var 0)) ?_ ?_
    · exact (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqTrans
        (GaussianRationalPolynomialProduct.contribution_outside _ _ _ _ _ Prf.hyp0).eqSymm
    · exact (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ Prf.hyp0).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr
          (entry_equal_at _ _ _ _ hs.wk.wk (le_trans Prf.hyp1 ts.wk.wk)) (.eqRefl _)).eqTrans
            (GaussianRationalPolynomialProduct.contribution_inside _ _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialProduct.subst_data] using
    (GaussianRationalPolynomialProduct.contribution_body_at (Γ := Δ) (Syn.shift P) (Syn.shift Q) (Syn.shift M) (Syn.shift k) (var 0)).eqTrans
      (term.eqTrans (GaussianRationalPolynomialProduct.contribution_body_at _ _ _ _ _).eqSymm)

def stepBody : PTm 3 := RationalPolynomialProductGaussianEmbedding.product (var 1)
  (inst2 GaussianPolynomialDeterminantTerms.factorBody (var 0) (var 2))
  (var 0*fstT (sndT (sndT (var 2)))) (fstT (sndT (sndT (var 2))))
def stageF : PR 2 := rec2 (singleton scalarOne : PTm 1) stepBody
def stage (M m L w j : PTm n) : PTm n := ap2 stageF j (data M m L w)
def term (M m L w : PTm n) : PTm n := RationalPolynomialBuffersGaussianEmbedding.scaled (stage M m L w m)
  (RationalScalarDeterminantGaussianEmbedding.sign m w)
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (stage M m L w j) = stage (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [stage]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (M m L w : PTm n) :
    Syn.subst σ (term M m L w) = term (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) := by simp [term]
theorem stage_congr {M M' m m' L L' w w' j j' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hw : Γ ⊢[PRAAx] w ≐ w') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    stage M m L w j ≐ stage M' m' L' w' j' :=
  congrAp2 stageF hj (congrPairT hM (congrPairT hm (congrPairT hL hw)))
theorem product_congr {P P' Q Q' N N' L L' : PTm n} (hP : Γ ⊢[PRAAx] P ≐ P') (hQ : Γ ⊢[PRAAx] Q ≐ Q')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') : Γ ⊢[PRAAx]
    RationalPolynomialProductGaussianEmbedding.product P Q N L ≐ RationalPolynomialProductGaussianEmbedding.product P' Q' N' L' :=
  (RationalPolynomialProductGaussianEmbedding.program_at _ _ _ _).eqSymm.eqTrans
    ((congrApp RationalPolynomialProductGaussianEmbedding.productF (fun i => by fin_cases i; exact hP; exact hQ; exact hN; exact hL)).eqTrans
      (RationalPolynomialProductGaussianEmbedding.program_at _ _ _ _))
theorem stage_zero (M m L w : PTm n) : Γ ⊢[PRAAx] stage M m L w zero ≐ singleton scalarOne := by
  simpa only [stage,stageF,GaussianRationalMonicReduction.subst_singleton,RationalGaussianEmbedding.subst_scalarOne] using
    rec2_zero (Γ := Γ) (singleton scalarOne : PTm 1) stepBody (data M m L w)
theorem stage_succ (M m L w j : PTm n) : Γ ⊢[PRAAx] stage M m L w (succ j) ≐
    RationalPolynomialProductGaussianEmbedding.product (stage M m L w j) (factor M m w j) (j*L) L := by
  have e := rec2_succ (Γ := Γ) (singleton scalarOne : PTm 1) stepBody j (data M m L w)
  simp only [stepBody,RationalPolynomialProductGaussianEmbedding.subst_product,subst_inst2,PTm.subst_mul,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at e
  have hL : Γ ⊢[PRAAx] fstT (sndT (sndT (data M m L w))) ≐ L := by
    simpa only [GaussianPolynomialDeterminantTerms.widthBody,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero] using
      GaussianPolynomialDeterminantTerms.width_at M m L w
  exact e.eqTrans (product_congr (.eqRefl _) (GaussianPolynomialDeterminantTerms.factor_body_at _ _ _ _ _) (congrMul (.eqRefl _) hL) hL)
theorem stage_length (M m L w j : PTm n) : Γ ⊢[PRAAx] length (stage M m L w j) ≐ succ (j*L) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact (congrFst ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_zero _ _ _ _))).eqTrans
      ((singleton_length _).eqTrans (congrSucc ((congrMul Prf.hyp0 (.eqRefl L)).eqTrans (zero_mul _))).eqSymm)
  · have target : (j ≐ succ (PTm.pred j)) :: Γ ⊢[PRAAx] succ (PTm.pred j*L+L) ≐ succ (j*L) :=
      (by ipra_ring : (j ≐ succ (PTm.pred j)) :: Γ ⊢[PRAAx] succ (PTm.pred j*L+L) ≐ succ (succ (PTm.pred j)*L)).eqTrans
        (congrSucc (congrMul Prf.hyp0.eqSymm (.eqRefl _)))
    exact (congrFst ((stage_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans (stage_succ _ _ _ _ _))).eqTrans
      ((RationalPolynomialProductGaussianEmbedding.product_length _ _ _ _).eqTrans target)

theorem embedded_entries_to_codes (C D H : PTm n)
    (h : Γ ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries C D H) : Γ ⊢[PRAAx]
    entriesEqual (coefficients C H) D H := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries
      (Syn.shift C) (Syn.shift D) (Syn.shift H) := by
    simpa only [Fm.shift,RationalPolynomialBuffersGaussianEmbedding.subst_embeddedEntries,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift H) :: Γ.map Fm.shift
  have rule : Δ ⊢[PRAAx] lt (var 0) (Syn.shift H) ⟶ embed (entry (Syn.shift C) (var 0)) ≐ entry (Syn.shift D) (var 0) := by
    simpa only [RationalPolynomialBuffersGaussianEmbedding.embeddedEntries,Fm.subst_imp,Fm.subst_eq,subst_lt,
      RationalGaussianEmbedding.subst_embed,Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      hs.wk.allE (var 0)
  simpa only [Δ,Syn.shift,RationalPolynomialGaussianEmbedding.subst_coefficients] using
    (coefficient_lookup (Syn.shift C) (Syn.shift H) (var 0) (Γ := Δ) Prf.hyp0).eqTrans (.impE rule Prf.hyp0)

def stageEntries (M m L w j : PTm n) : Fm PTm n := RationalPolynomialBuffersGaussianEmbedding.embeddedEntries
  (stage M m L w j) (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j) (succ (j*L))
def stageLaw (M m L w j : PTm n) : Fm PTm n := le j m ⟶ stageEntries M m L w j
@[simp] theorem subst_stageEntries {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (stageEntries M m L w j).subst σ = stageEntries (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by
  simp [stageEntries]
@[simp] theorem subst_stageLaw {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    (stageLaw M m L w j).subst σ = stageLaw (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by
  simp [stageLaw]

theorem stage_base_entry (M m L w i : PTm n) (hi : Γ ⊢[PRAAx] lt i (succ (zero*L))) : Γ ⊢[PRAAx]
    embed (entry (stage M m L w zero) i) ≐ entry (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w zero) i := by
  have i0 := GaussianPolynomialDeterminantTerms.index_one_zero i (lt_congr (.eqRefl _) (congrSucc (zero_mul L)) hi)
  have lo := (embed_congr (entry_congr (stage_zero M m L w) i0)).eqTrans
    ((embed_congr (singleton_lookup scalarOne)).eqTrans RationalGaussianEmbedding.embed_one)
  have rhs := (entry_congr (GaussianPolynomialDeterminantTerms.stage_zero (embeddedTable M m L) m L w) i0).eqTrans (singleton_lookup _)
  exact lo.eqTrans rhs.eqSymm
theorem stage_entries_base (M m L w : PTm n) : Γ ⊢[PRAAx] stageEntries M m L w zero := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_stage,subst_embeddedTable,GaussianPolynomialDeterminantTerms.subst_stage,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using
    stage_base_entry (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0) Prf.hyp0

theorem stage_entry_step (M m L w j s : PTm n) (hj : Γ ⊢[PRAAx] lt j m)
    (ih : Γ ⊢[PRAAx] stageEntries M m L w j) (hs : Γ ⊢[PRAAx] le s (succ j*L)) : Γ ⊢[PRAAx]
    embed (entry (stage M m L w (succ j)) s) ≐
      entry (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w (succ j)) s := by
  have range : Γ ⊢[PRAAx] le s (j*L+L) := le_congr (.eqRefl _) (by ipra_ring) hs
  have original := (embed_congr (entry_congr (stage_succ M m L w j) (.eqRefl s))).eqTrans
    (RationalPolynomialProductGaussianEmbedding.product_embedding _ _ (j*L) L s range)
  have convolution := GaussianRationalPolynomialProduct.product_lookup
    (coefficients (stage M m L w j) (succ (j*L))) (coefficients (factor M m w j) (succ L)) (j*L) L s range
  have left := coefficient_left_entries
    (coefficients (stage M m L w j) (succ (j*L))) (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j)
    (coefficients (factor M m w j) (succ L)) L (succ (j*L)) (succ (j*L)) s
    (embedded_entries_to_codes _ _ _ ih) (le_refl _)
  have right := GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialProduct.contributionBody (.eqRefl (succ (j*L)))
    (congrPairT (.eqRefl (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j))
      (congrPairT (embedded_factor M m L w j hj).eqSymm (.eqRefl (pairT L s))))
  exact original.eqTrans (convolution.eqTrans (left.eqTrans (right.eqTrans
    (GaussianPolynomialDeterminantTerms.stage_coefficient_succ _ _ _ _ _ _ hs).eqSymm)))

theorem stage_entries_step (M m L w j : PTm n) (hj : Γ ⊢[PRAAx] lt j m)
    (ih : Γ ⊢[PRAAx] stageEntries M m L w j) : Γ ⊢[PRAAx] stageEntries M m L w (succ j) := by
  have ijs : Γ.map Fm.shift ⊢[PRAAx] stageEntries (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift j) := by
    simpa only [Fm.shift,subst_stageEntries,Syn.shift] using ih.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (succ (Syn.shift j)*Syn.shift L)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (succ (Syn.shift j)*Syn.shift L) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_stage,subst_embeddedTable,GaussianPolynomialDeterminantTerms.subst_stage,ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using
    stage_entry_step (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift j) (var 0) hjs.wk ijs.wk bound

def embeddedSyntax (C D H : PTm n) : BFm n := .all H
  (.eq (embed (entry (Syn.shift C) (var 0))) (entry (Syn.shift D) (var 0)))
def stageSyntax (M m L w j : PTm n) : BFm n := .imp (.le j m)
  (embeddedSyntax (stage M m L w j) (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j) (succ (j*L)))
theorem stage_formula (M m L w j : PTm n) : formula (stageSyntax M m L w j) = stageLaw M m L w j := rfl

theorem stage_entries (M m L w j : PTm n) (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx] stageEntries M m L w j := by
  let S := stageSyntax (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)
  have all : Γ ⊢[PRAAx] .all (stageLaw (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (stage_entries_base M m L w).wk
    · simp only [S,stage_formula,subst_stageLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact stage_entries_step _ _ _ _ _ Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] stageLaw M m L w j := by
    simpa only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem stage_entry_embedding (M m L w j s : PTm n) (hj : Γ ⊢[PRAAx] le j m) (hs : Γ ⊢[PRAAx] le s (j*L)) : Γ ⊢[PRAAx]
    embed (entry (stage M m L w j) s) ≐ entry (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j) s := by
  have gate : Γ ⊢[PRAAx] lt s (succ (j*L)) ⟶ embed (entry (stage M m L w j) s) ≐
      entry (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j) s := by
    simpa [stageEntries,RationalPolynomialBuffersGaussianEmbedding.embeddedEntries] using (stage_entries M m L w j hj).allE s
  exact .impE gate ((succ_monus_succ _ _).eqTrans hs)
theorem term_length (M m L w : PTm n) : Γ ⊢[PRAAx] length (term M m L w) ≐ succ (m*L) :=
  (RationalPolynomialBuffersGaussianEmbedding.scaled_length _ _).eqTrans (stage_length _ _ _ _ _)
theorem term_entry_embedding (M m L w s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    embed (entry (term M m L w) s) ≐ entry (GaussianPolynomialDeterminantTerms.term (embeddedTable M m L) m L w) s :=
  (embed_congr (RationalPolynomialBuffersGaussianEmbedding.scaled_lookup _ _ _
    (lt_congr (.eqRefl _) (stage_length M m L w m).eqSymm ((succ_monus_succ _ _).eqTrans hs)))).eqTrans
      ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (RationalScalarDeterminantGaussianEmbedding.sign_embedding _ _)
          (stage_entry_embedding M m L w m s (le_refl _) hs)).eqTrans
            (GaussianPolynomialDeterminantTerms.term_coefficient _ _ _ _ _ hs).eqSymm))
theorem term_entries (M m L w : PTm n) : Γ ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries
    (term M m L w) (GaussianPolynomialDeterminantTerms.term (embeddedTable M m L) m L w) (succ (m*L)) := by
  refine .allI (.impI ?_)
  have bound : lt (var 0) (succ (Syn.shift m*Syn.shift L)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (Syn.shift m*Syn.shift L) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,subst_term,subst_embeddedTable,GaussianPolynomialDeterminantTerms.subst_term,ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using
    term_entry_embedding (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0) bound

theorem stage_evaluation_conjugacy (M m L w j z : PTm n) (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate (stage M m L w j) z) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialDeterminantTerms.stage (embeddedTable M m L) m L w j) (embed z) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ (succ (j*L)) z (stage_length _ _ _ _ _)
    (GaussianPolynomialDeterminantTerms.stage_length _ _ _ _ _) (stage_entries M m L w j hj)
theorem term_evaluation_conjugacy (M m L w z : PTm n) : Γ ⊢[PRAAx]
    embed (RationalPolynomialGaussianEmbedding.evaluate (term M m L w) z) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialDeterminantTerms.term (embeddedTable M m L) m L w) (embed z) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ (succ (m*L)) z (term_length _ _ _ _)
    (GaussianPolynomialDeterminantTerms.term_length _ _ _ _) (term_entries M m L w)

def output (M m L w j : PTm n) : PTm n := pairT (stage M m L w j) (term M m L w)
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (M m L w j : PTm n) : PTm n := PTm.app outputF ![M,m,L,w,j]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (output M m L w j) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L w j : PTm n) :
    Syn.subst σ (run M m L w j) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ w) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (M m L w j : PTm n) : Γ ⊢[PRAAx] run M m L w j ≐ output M m L w j := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![M,m,L,w,j]
theorem returned_stage (M m L w j : PTm n) : Γ ⊢[PRAAx] fstT (run M m L w j) ≐ stage M m L w j :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_term (M m L w j : PTm n) : Γ ⊢[PRAAx] sndT (run M m L w j) ≐ term M m L w :=
  (congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _)

theorem actual_rational_embedded_table_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (tableShape (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2)) := closeUniv 3 (embedded_shape _ _ _)
theorem actual_rational_embedded_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 1) ⟶
      cell (embeddedTable (var 0) (var 1) (var 2)) (var 3) (var 4) ≐ coefficients (cell (var 0) (var 3) (var 4)) (succ (var 2))) :=
  closeUniv 5 (.impI (.impI (table_cell _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_term_stage_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (stage (var 0) (var 1) (var 2) (var 3) (succ (var 4)) ≐ RationalPolynomialProductGaussianEmbedding.product
      (stage (var 0) (var 1) (var 2) (var 3) (var 4)) (factor (var 0) (var 1) (var 3) (var 4)) (var 4*var 2) (var 2)) :=
  closeUniv 5 (stage_succ _ _ _ _ _)
theorem actual_rational_term_stage_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (stage (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ succ (var 4*var 2)) := closeUniv 5 (stage_length _ _ _ _ _)
theorem actual_rational_term_stage_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 4) (var 1) ⟶ le (var 5) (var 4*var 2) ⟶ embed (entry (stage (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) ≐
      entry (GaussianPolynomialDeterminantTerms.stage (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (stage_entry_embedding _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_rational_signed_term_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1*var 2) ⟶ embed (entry (term (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐
      entry (GaussianPolynomialDeterminantTerms.term (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (term_entry_embedding _ _ _ _ _ Prf.hyp0))
theorem actual_rational_signed_term_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (term (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1*var 2)) := closeUniv 4 (term_length _ _ _ _)
theorem actual_rational_term_stage_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 4) (var 1) ⟶ embed (RationalPolynomialGaussianEmbedding.evaluate
      (stage (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) ≐ GaussianRationalHorner.evaluate
        (GaussianPolynomialDeterminantTerms.stage (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3) (var 4)) (embed (var 5))) :=
  closeUniv 6 (.impI (stage_evaluation_conjugacy _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_signed_term_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (embed (RationalPolynomialGaussianEmbedding.evaluate (term (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐ GaussianRationalHorner.evaluate
      (GaussianPolynomialDeterminantTerms.term (embeddedTable (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3)) (embed (var 4))) :=
  closeUniv 5 (term_evaluation_conjugacy _ _ _ _ _)
theorem actual_rational_determinant_terms_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ stage (var 0) (var 1) (var 2) (var 3) (var 4) ⋏
      sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ term (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.andI (returned_stage _ _ _ _ _) (returned_term _ _ _ _ _))

end LeanProofs.IPRA.Analysis.RationalPolynomialDeterminantTermsGaussianEmbedding

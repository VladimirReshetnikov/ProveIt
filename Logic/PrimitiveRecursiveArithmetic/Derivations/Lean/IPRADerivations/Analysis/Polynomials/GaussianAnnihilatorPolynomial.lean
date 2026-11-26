import IPRADerivations.Analysis.Inequalities.GaussianWeightedMonomialBasis
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialWeightedDegree
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalMonicReconstruction
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual descending polynomial from finite annihilator coefficients

Each retained original lexicographic monomial reads its actual coefficient
rank. The generated X coefficients and Y rows use the existing descending
storage conventions. Shape and lookups are unconditional; a genuine finite
nonzero coefficient witness derives nonzero rows and the computed weighted
degree bound. No annihilator elimination, evaluator or output law is input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianAnnihilatorPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianWeightedMonomialBasis
  (count labels label position decodeY decodeX keep admissible)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero canonical canonical_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qzero_canonical canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr recode_eq recode_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialDegree
  (first degree flag nonzeroCoefficients nonzero_of_flag_one success_index first_nonzero found_of_flag_one)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (rowShape)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot slot_range slot_complement)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (a m d L i j : PTm n) : PTm n :=
  sel (keep m d L (label L i j)) (recode (entry a (position m d L i j))) qzero
def data (a m d L : PTm n) : PTm n := pairT a (GaussianWeightedMonomialBasis.data m d L)
def fields (p : PTm n) : Fin 4 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
def rowData (a m d L i : PTm n) : PTm n := pairT i (data a m d L)
def rowBody : PTm 2 := coefficient (fields (sndT (var 1)) 0) (fields (sndT (var 1)) 1)
  (fields (sndT (var 1)) 2) (fields (sndT (var 1)) 3) (fstT (var 1)) (monus (fields (sndT (var 1)) 3) (var 0))
def row (a m d L i : PTm n) : PTm n := sequence rowBody (succ L) (rowData a m d L i)
def outerBody : PTm 2 := row (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (fields (var 1) 3)
  (slot (fields (var 1) 1) (var 0))
def polynomial (a m d L : PTm n) : PTm n := sequence outerBody m (data a m d L)

@[simp] theorem subst_coefficient {l : ℕ} (σ : Fin n → PTm l) (a m d L i j : PTm n) :
    Syn.subst σ (coefficient a m d L i j) = coefficient (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d)
      (Syn.subst σ L) (Syn.subst σ i) (Syn.subst σ j) := by simp [coefficient,sel]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    Syn.subst σ (data a m d L) = data (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [data]
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (a m d L i : PTm n) :
    Syn.subst σ (rowData a m d L i) = rowData (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ i) := by simp [rowData]
@[simp] theorem subst_row {l : ℕ} (σ : Fin n → PTm l) (a m d L i : PTm n) :
    Syn.subst σ (row a m d L i) = row (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) (Syn.subst σ i) := by simp [row]
@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    Syn.subst σ (polynomial a m d L) = polynomial (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [polynomial]

theorem val_five {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem coefficient_congr {a a' m m' d d' L L' i i' j j' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hi : Γ ⊢[PRAAx] i ≐ i') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    coefficient a m d L i j ≐ coefficient a' m' d' L' i' j' := by
  simpa only [subst_coefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,val_five,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![a,m,d,L,i,j]) (σ' := ![a',m',d',L',i',j'])
      (fun q => by fin_cases q <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']; exact ha; exact hm; exact hd; exact hL; exact hi; exact hj)
theorem row_congr {a a' m m' d d' L L' i i' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hm : Γ ⊢[PRAAx] m ≐ m') (hd : Γ ⊢[PRAAx] d ≐ d')
    (hL : Γ ⊢[PRAAx] L ≐ L') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] row a m d L i ≐ row a' m' d' L' i' := by
  simpa only [subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (row (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![a,m,d,L,i]) (σ' := ![a',m',d',L',i'])
      (fun q => by fin_cases q <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ']; exact ha; exact hm; exact hd; exact hL; exact hi)
theorem field_congr (i : Fin 4) {p q : PTm n} (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx] fields p i ≐ fields q i := by
  ipra_congr (fields (var 0) i : PTm 1) with [h]
theorem fields_at (a m d L : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] fields (data a m d L) i ≐ ![a,m,d,L] i := by
  have e0 := snd_pair (Γ := Γ) a (GaussianWeightedMonomialBasis.data m d L)
  have e1 := (congrSnd e0).eqTrans (snd_pair m (pairT d L))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrSnd e1).eqTrans (snd_pair _ _)

theorem row_body_at (a m d L i s : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody s (rowData a m d L i) ≐ coefficient a m d L i (monus L s) := by
  have params (q : Fin 4) : Γ ⊢[PRAAx] fields (sndT (rowData a m d L i)) q ≐ ![a,m,d,L] q :=
    (field_congr q (snd_pair _ _)).eqTrans (fields_at _ _ _ _ q)
  simpa only [rowBody,inst2,subst_coefficient,subst_fields,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,rowData,PTm.subst_monus] using
      coefficient_congr (params 0) (params 1) (params 2) (params 3) (fst_pair _ _)
        (congrMonus (params 3) (.eqRefl s))
theorem outer_body_at (a m d L r : PTm n) : Γ ⊢[PRAAx]
    inst2 outerBody r (data a m d L) ≐ row a m d L (slot m r) := by
  simpa only [outerBody,inst2,subst_row,subst_fields,GaussianPolynomialMultiplicationMatrix.subst_slot,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,slot,PTm.subst_monus,ConciseIPRA.PTm.subst_succ] using
      row_congr (Γ := Γ) (fields_at a m d L 0) (fields_at a m d L 1) (fields_at a m d L 2)
        (fields_at a m d L 3) (congrMonus (fields_at a m d L 1) (.eqRefl (succ r)))
theorem row_length (a m d L i : PTm n) : Γ ⊢[PRAAx] length (row a m d L i) ≐ succ L := sequence_length _ _ _
theorem polynomial_length (a m d L : PTm n) : Γ ⊢[PRAAx] length (polynomial a m d L) ≐ m := sequence_length _ _ _
theorem row_lookup (a m d L i s : PTm n) (hs : Γ ⊢[PRAAx] le s L) : Γ ⊢[PRAAx]
    entry (row a m d L i) s ≐ coefficient a m d L i (monus L s) :=
  (sequence_decode rowBody (x := rowData a m d L i) ((succ_monus_succ _ _).eqTrans hs)).eqTrans (row_body_at _ _ _ _ _ _)
theorem outer_lookup (a m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (polynomial a m d L) r ≐ row a m d L (slot m r) :=
  (sequence_decode outerBody (x := data a m d L) hr).eqTrans (outer_body_at _ _ _ _ _)
theorem polynomial_shape (a m d L : PTm n) : Γ ⊢[PRAAx] rowShape (polynomial a m d L) m L := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_polynomial,ConciseIPRA.PTm.subst_succ,length] using
    (congrFst (outer_lookup (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
      (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L) (var 0) Prf.hyp0)).eqTrans (row_length _ _ _ _ _)
theorem polynomial_row (a m d L i : PTm n) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.row (polynomial a m d L) m i ≐ row a m d L i :=
  (outer_lookup _ _ _ _ _ (slot_range m i hi)).eqTrans
    (row_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (slot_complement m i hi))
theorem polynomial_coefficient (a m d L i j : PTm n) (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] le j L) : Γ ⊢[PRAAx]
    entry (GaussianPolynomialWeightedDegree.row (polynomial a m d L) m i) (monus L j) ≐ coefficient a m d L i j :=
  (entry_congr (polynomial_row a m d L i hi) (.eqRefl _)).eqTrans
    ((row_lookup _ _ _ _ _ _ (GaussianRationalMonicReconstruction.monus_le_left _ _)).eqTrans
      (coefficient_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (GaussianRationalMonicReconstruction.complement L j hj)))


theorem coefficient_kept (a m d L i j : PTm n) (h : Γ ⊢[PRAAx] admissible m d L i j) : Γ ⊢[PRAAx]
    coefficient a m d L i j ≐ recode (entry a (position m d L i j)) :=
  Foundations.GuardedTotalization.sel_one (GaussianWeightedMonomialBasis.label_keep m d L i j h)
theorem coefficient_rejected (a m d L i j : PTm n) (h : Γ ⊢[PRAAx] keep m d L (label L i j) ≐ zero) : Γ ⊢[PRAAx]
    coefficient a m d L i j ≐ qzero := Foundations.GuardedTotalization.sel_zero h
theorem coefficient_canonical (a m d L i j : PTm n) : Γ ⊢[PRAAx] canonical (coefficient a m d L i j) := by
  refine .orE (eq_or_ne (keep m d L (label L i j)) zero) ?_ ?_
  · exact canonical_congr (coefficient_rejected _ _ _ _ _ _ Prf.hyp0) qzero_canonical
  · exact canonical_congr (Foundations.GuardedTotalization.sel_one
      (GaussianWeightedMonomialBasis.keep_one m d L (label L i j)
        (GaussianWeightedMonomialBasis.keep_bound m d L (label L i j) Prf.hyp0))) (recode_canonical _)
theorem row_canonical (a m d L i : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (row a m d L i) := by
  simp only [canonicalCoefficients,Syn.shift,subst_row]
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (row (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L) (Syn.shift i))) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift L) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (row_length _ _ _ _ _) Prf.hyp0)
  exact canonical_congr (row_lookup _ _ _ _ _ _ bound) (coefficient_canonical _ _ _ _ _ _)
theorem canonical_rows (a m d L : PTm n) : Γ ⊢[PRAAx] .all
    (lt (var 0) (Syn.shift m) ⟶ canonicalCoefficients (entry (Syn.shift (polynomial a m d L)) (var 0))) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_polynomial] using GaussianRationalMonicReduction.canonical_coefficients_congr
    (outer_lookup (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (Syn.shift a) (Syn.shift m)
      (Syn.shift d) (Syn.shift L) (var 0) Prf.hyp0) (row_canonical _ _ _ _ _)

theorem selected_position (m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    position m d L (decodeY L (entry (labels m d L) r)) (decodeX L (entry (labels m d L) r)) ≐ r :=
  (congrAp2 (sumF (Foundations.BoundedReflection.sgB GaussianWeightedMonomialBasis.keepBody))
    (GaussianWeightedMonomialBasis.label_decode L (entry (labels m d L) r)) (.eqRefl _)).eqTrans
      (GaussianWeightedMonomialBasis.label_rank m d L r hr)

/-- The actual stored basis rank, not a caller-selected monomial index,
reads the original annihilator entry at that SAME rank. -/
theorem selected_coefficient (a m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L)) : Γ ⊢[PRAAx]
    entry (GaussianPolynomialWeightedDegree.row (polynomial a m d L) m (decodeY L (entry (labels m d L) r)))
      (monus L (decodeX L (entry (labels m d L) r))) ≐ recode (entry a r) := by
  have valid := GaussianWeightedMonomialBasis.labels_admissible m d L r hr
  exact (polynomial_coefficient _ _ _ _ _ _ (.andE₁ valid)
    (GaussianWeightedMonomialBasis.admissible_x_bound _ _ _ _ _ valid)).eqTrans
      ((coefficient_kept _ _ _ _ _ _ valid).eqTrans (recode_congr (entry_congr (.eqRefl a) (selected_position m d L r hr))))

theorem coefficient_weight (a m d L i j : PTm n) (hj : Γ ⊢[PRAAx] le j L)
    (h : Γ ⊢[PRAAx] neg (coefficient a m d L i j ≐ qzero)) : Γ ⊢[PRAAx] le (m*j+d*i) L := by
  have retained : Γ ⊢[PRAAx] neg (keep m d L (label L i j) ≐ zero) :=
    .impI (.impE h.wk (coefficient_rejected a m d L i j Prf.hyp0))
  have weight := GaussianWeightedMonomialBasis.keep_bound m d L (label L i j) retained
  have dec := GaussianWeightedMonomialBasis.decode_label L i j hj
  exact le_congr (congrAdd (congrMul (.eqRefl _) (.andE₂ dec)) (congrMul (.eqRefl _) (.andE₁ dec))) (.eqRefl _) weight

def nonzeroLambda (a m d L : PTm n) : Fm PTm n := .ex (lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) ⋏
  neg (recode (entry (Syn.shift a) (var 0)) ≐ qzero))
def input (a m d L : PTm n) : Fm PTm n := le one m ⋏ ((length a ≐ count m d L) ⋏ nonzeroLambda a m d L)
@[simp] theorem subst_nonzeroLambda {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    (nonzeroLambda a m d L).subst σ = nonzeroLambda (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by
  simp [nonzeroLambda,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    (input a m d L).subst σ = input (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [input]

theorem selected_nonzero_row (a m d L r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count m d L))
    (ha : Γ ⊢[PRAAx] neg (recode (entry a r) ≐ qzero)) : Γ ⊢[PRAAx]
    nonzeroCoefficients (GaussianPolynomialWeightedDegree.row (polynomial a m d L) m
      (decodeY L (entry (labels m d L) r))) L := by
  have slotBound := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) L (decodeX L (entry (labels m d L) r))
  have value := (recode_congr (selected_coefficient a m d L r hr)).eqTrans (recode_eq _ (recode_canonical _))
  have found := GaussianRationalPolynomialDegree.first_from_witness _ L _
    ((succ_monus_succ _ _).eqTrans slotBound) (.impI (.impE ha.wk (value.wk.eqSymm.eqTrans Prf.hyp0)))
  exact nonzero_of_flag_one _ _ (GaussianRationalPolynomialDegree.flag_one_of_found _ _ (.andE₁ found))
theorem nonzero_rows_witness (G m L i : PTm n) (hi : Γ ⊢[PRAAx] lt i m)
    (h : Γ ⊢[PRAAx] nonzeroCoefficients (GaussianPolynomialWeightedDegree.row G m i) L) :
    Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.nonzeroRows G m L := by
  refine .exI i ?_
  simpa only [GaussianPolynomialWeightedDegree.nonzeroRows,Fm.subst_and,subst_lt,
    GaussianRationalPolynomialDegree.subst_nonzeroCoefficients,GaussianPolynomialWeightedDegree.subst_row,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hi h

theorem nonzero_rows (a m d L : PTm n) (h : Γ ⊢[PRAAx] nonzeroLambda a m d L) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.nonzeroRows (polynomial a m d L) m L := by
  refine .exE h ?_
  let Δ := (lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) ⋏
    neg (recode (entry (Syn.shift a) (var 0)) ≐ qzero)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] lt (var 0) (count (Syn.shift m) (Syn.shift d) (Syn.shift L)) := .andE₁ Prf.hyp0
  have original : Δ ⊢[PRAAx] neg (recode (entry (Syn.shift a) (var 0)) ≐ qzero) := .andE₂ Prf.hyp0
  have valid := GaussianWeightedMonomialBasis.labels_admissible (Syn.shift m) (Syn.shift d) (Syn.shift L) (var 0) bound
  simpa only [Δ,Fm.shift,GaussianPolynomialWeightedDegree.subst_nonzeroRows,subst_polynomial,Syn.shift] using
    nonzero_rows_witness (polynomial (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L)) (Syn.shift m) (Syn.shift L)
      (decodeY (Syn.shift L) (entry (labels (Syn.shift m) (Syn.shift d) (Syn.shift L)) (var 0))) (.andE₁ valid)
      (selected_nonzero_row (Syn.shift a) (Syn.shift m) (Syn.shift d) (Syn.shift L) (var 0) bound original)

theorem generated_input (a m d L : PTm n) (h : Γ ⊢[PRAAx] input a m d L) : Γ ⊢[PRAAx]
    GaussianPolynomialWeightedDegree.input (polynomial a m d L) m L :=
  .andI (.andE₁ h) (.andI (polynomial_shape a m d L) (nonzero_rows a m d L (.andE₂ (.andE₂ h))))

theorem row_weight_bound (a m d L i : PTm n) (hi : Γ ⊢[PRAAx] lt i m)
    (hFlag : Γ ⊢[PRAAx] GaussianPolynomialWeightedDegree.rowFlag (polynomial a m d L) m L i ≐ one) : Γ ⊢[PRAAx]
    le (GaussianPolynomialWeightedDegree.weight (polynomial a m d L) m L d i) L := by
  let G := polynomial a m d L
  let e := first (GaussianPolynomialWeightedDegree.row G m i) L
  let j := degree (GaussianPolynomialWeightedDegree.row G m i) L
  have eBound := success_index (GaussianPolynomialWeightedDegree.row G m i) L hFlag
  have jBound : Γ ⊢[PRAAx] le j L := GaussianRationalMonicReconstruction.monus_le_left _ _
  have complement : Γ ⊢[PRAAx] monus L j ≐ e := GaussianRationalMonicReconstruction.complement L e eBound
  have value := (entry_congr (.eqRefl (GaussianPolynomialWeightedDegree.row G m i)) complement.eqSymm).eqTrans
    (polynomial_coefficient a m d L i j hi jBound)
  have actual : Γ ⊢[PRAAx] recode (entry (GaussianPolynomialWeightedDegree.row G m i) e) ≐ coefficient a m d L i j :=
    (recode_congr value).eqTrans (recode_eq _ (coefficient_canonical _ _ _ _ _ _))
  have nonzero := first_nonzero (GaussianPolynomialWeightedDegree.row G m i) L (found_of_flag_one _ _ hFlag)
  exact coefficient_weight a m d L i j jBound (.impI (.impE nonzero.wk (actual.wk.eqTrans Prf.hyp0)))
theorem weighted_bound (a m d L : PTm n) (h : Γ ⊢[PRAAx] input a m d L) : Γ ⊢[PRAAx]
    le (GaussianPolynomialWeightedDegree.weightedDegree (polynomial a m d L) m L d) L := by
  let G := polynomial a m d L
  have rows := nonzero_rows a m d L (.andE₂ (.andE₂ h))
  have indexBound := Prf.andE₁ (GaussianPolynomialWeightedDegree.index_attains G m L d (.andE₁ h))
  have selected := GaussianPolynomialWeightedDegree.selected_flag_one G m L d (.andE₁ h) rows
  have bound := row_weight_bound a m d L (GaussianPolynomialWeightedDegree.index G m L d) indexBound selected
  exact le_congr (GaussianPolynomialWeightedDegree.maximum_eq_weight G m L d (.andE₁ h) rows).eqSymm (.eqRefl _) bound


def certificate (a m d L : PTm n) : Fm PTm n := (length (polynomial a m d L) ≐ m) ⋏
  (rowShape (polynomial a m d L) m L ⋏ (GaussianPolynomialWeightedDegree.nonzeroRows (polynomial a m d L) m L ⋏
    le (GaussianPolynomialWeightedDegree.weightedDegree (polynomial a m d L) m L d) L))
theorem polynomial_correct (a m d L : PTm n) (h : Γ ⊢[PRAAx] input a m d L) : Γ ⊢[PRAAx] certificate a m d L :=
  .andI (polynomial_length _ _ _ _) (.andI (polynomial_shape _ _ _ _)
    (.andI (nonzero_rows _ _ _ _ (.andE₂ (.andE₂ h))) (weighted_bound _ _ _ _ h)))

def polynomialF : PR 4 := PTm.toPR (polynomial (var 0) (var 1) (var 2) (var 3))
def output (a m d L : PTm n) : PTm n := pairT (polynomial a m d L)
  (pairT (count m d L) (pairT (labels m d L) (GaussianPolynomialWeightedDegree.weightedDegree (polynomial a m d L) m L d)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (a m d L : PTm n) : PTm n := app outputF ![a,m,d,L]
def outputField (p : PTm n) (i : Fin 4) : PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))] i
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    (certificate a m d L).subst σ = certificate (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [certificate]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    Syn.subst σ (output a m d L) = output (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (a m d L : PTm n) :
    Syn.subst σ (run a m d L) = run (Syn.subst σ a) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ L) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_outputField {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (outputField p i) = outputField (Syn.subst σ p) i := by fin_cases i <;> simp [outputField]
theorem polynomial_program_at (a m d L : PTm n) : Γ ⊢[PRAAx] app polynomialF ![a,m,d,L] ≐ polynomial a m d L := by
  simpa [polynomialF] using toPR_eq (Γ := Γ) (polynomial (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,m,d,L]
theorem program_at (a m d L : PTm n) : Γ ⊢[PRAAx] run a m d L ≐ output a m d L := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,m,d,L]
theorem returned_fields (a m d L : PTm n) (i : Fin 4) : Γ ⊢[PRAAx]
    outputField (run a m d L) i ≐ ![polynomial a m d L,count m d L,labels m d L,
      GaussianPolynomialWeightedDegree.weightedDegree (polynomial a m d L) m L d] i := by
  have e0 := program_at (Γ := Γ) a m d L
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem returned_length (a m d L : PTm n) : Γ ⊢[PRAAx] length (outputField (run a m d L) 0) ≐ m :=
  (congrFst (returned_fields _ _ _ _ 0)).eqTrans (polynomial_length _ _ _ _)
theorem returned_weight (a m d L : PTm n) (h : Γ ⊢[PRAAx] input a m d L) : Γ ⊢[PRAAx]
    le (outputField (run a m d L) 3) L := le_congr (returned_fields _ _ _ _ 3).eqSymm (.eqRefl _) (weighted_bound a m d L h)

theorem actual_polynomial_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (polynomial (var 0) (var 1) (var 2) (var 3)) ≐ var 1) ⋏ rowShape (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) :=
  closeUniv 4 (.andI (polynomial_length _ _ _ _) (polynomial_shape _ _ _ _))
theorem actual_coefficient_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 1) ⟶ le (var 5) (var 3) ⟶
      entry (GaussianPolynomialWeightedDegree.row (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 4))
        (monus (var 3) (var 5)) ≐ coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (polynomial_coefficient _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_kept_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (admissible (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
        recode (entry (var 0) (position (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (coefficient_kept _ _ _ _ _ _ Prf.hyp0))
theorem actual_selected_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (count (var 1) (var 2) (var 3)) ⟶
      entry (GaussianPolynomialWeightedDegree.row (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1)
        (decodeY (var 3) (entry (labels (var 1) (var 2) (var 3)) (var 4))))
          (monus (var 3) (decodeX (var 3) (entry (labels (var 1) (var 2) (var 3)) (var 4)))) ≐ recode (entry (var 0) (var 4))) :=
  closeUniv 5 (.impI (selected_coefficient _ _ _ _ _ Prf.hyp0))
theorem actual_nonzero_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonzeroLambda (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianPolynomialWeightedDegree.nonzeroRows (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3)) :=
  closeUniv 4 (.impI (nonzero_rows _ _ _ _ Prf.hyp0))
theorem actual_weight_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶
      le (GaussianPolynomialWeightedDegree.weightedDegree (polynomial (var 0) (var 1) (var 2) (var 3)) (var 1) (var 3) (var 2)) (var 3)) :=
  closeUniv 4 (.impI (weighted_bound _ _ _ _ Prf.hyp0))
theorem actual_annihilator_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (polynomial_correct _ _ _ _ Prf.hyp0))
theorem actual_polynomial_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((app polynomialF ![var 0,var 1,var 2,var 3] ≐ polynomial (var 0) (var 1) (var 2) (var 3)) ⋏
      (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (polynomial_program_at _ _ _ _) (program_at _ _ _ _))
theorem actual_returned_length_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (outputField (run (var 0) (var 1) (var 2) (var 3)) 0) ≐ var 1) ⋏
      (outputField (run (var 0) (var 1) (var 2) (var 3)) 1 ≐ count (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (returned_length _ _ _ _) (returned_fields _ _ _ _ 1))
theorem actual_returned_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ le (outputField (run (var 0) (var 1) (var 2) (var 3)) 3) (var 3)) :=
  closeUniv 4 (.impI (returned_weight _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianAnnihilatorPolynomial

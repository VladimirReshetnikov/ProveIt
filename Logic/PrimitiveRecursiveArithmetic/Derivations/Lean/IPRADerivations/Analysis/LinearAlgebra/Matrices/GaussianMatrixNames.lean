import IPRADerivations.Analysis.Names.Approximation.GaussianNameBounds
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicFactorBounds

/-!
# Original regular entry names and actual finite matrix samples

The fixed PR4 schema takes row, column, precision and data. All numerical
sizes and indices remain inputs. Each row uses the existing precision-zero
L1 maximum. The uniform integer bound is deliberately larger than one
global maximum: one plus the sum of the row bounds 3+ceil(max L1).
It is positive even for the empty matrix. Original regularity alone gives
every sampled entry bound and the exact two-precision entry-distance bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianMatrixNames

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalFiberVandermonde (table table_length table_lookup table_row_length)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalRowElimination (shape)
open GaussianCharacteristicFactorBounds (entryBounds entryDistances rowBounds rowDistances)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def entry (a : PR 4) (r j s x : PTm n) : PTm n := app a ![r,j,s,x]
def rowData (r x : PTm n) : PTm n := pairT r x
def rowReaderBody (a : PR 4) : PTm 3 := entry a (fstT (var 2)) (var 0) (var 1) (sndT (var 2))
def rowReaderF (a : PR 4) : PR 3 := PTm.toPR (rowReaderBody a)
def rowCN (a : PR 4) (N r x : PTm n) : Fm PTm n := GaussianCoefficientNameBounds.CN (rowReaderF a) N (rowData r x)
def CN (a : PR 4) (N x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ rowCN a (Syn.shift N) (var 0) (Syn.shift x))
def sampleBody (a : PR 4) : PTm 3 := entry a (var 0) (var 1) (fstT (var 2)) (sndT (var 2))
def sample (a : PR 4) (N s x : PTm n) : PTm n := table (sampleBody a) N N (pairT s x)
def rowRadiusF (a : PR 4) : PR 2 := PTm.toPR (GaussianCoefficientNameBounds.A (rowReaderF a) (var 0) (var 1))
def rowBound (a : PR 4) (N r x : PTm n) : PTm n := ap2 (rowRadiusF a) N (rowData r x)
def boundData (N x : PTm n) : PTm n := pairT N x
def boundBody (a : PR 4) : PTm 2 := rowBound a (fstT (var 1)) (var 0) (sndT (var 1))
def B (a : PR 4) (N x : PTm n) : PTm n := one+ap2 (sumF (boundBody a)) N (boundData N x)

ipra_subst entry
ipra_subst rowData
ipra_subst rowCN
ipra_subst CN [Syn.subst_shift, Syn.shift_subst]
ipra_subst sample
ipra_subst rowBound
ipra_subst boundData
ipra_subst B

theorem entry_congr (a : PR 4) {r r' j j' s s' x x' : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ r') (hj : Γ ⊢[PRAAx] j ≐ j') (hs : Γ ⊢[PRAAx] s ≐ s') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] entry a r j s x ≐ entry a r' j' s' x' :=
  congrApp a (fun i => by fin_cases i; exact hr; exact hj; exact hs; exact hx)

theorem row_reader_at (a : PR 4) (r j s x : PTm n) : Γ ⊢[PRAAx]
    ap3 (rowReaderF a) j s (rowData r x) ≐ entry a r j s x := by
  have h := toPR_eq (Γ := Γ) (rowReaderBody a) ![j,s,rowData r x]
  simp only [rowReaderBody,subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  exact h.eqTrans (entry_congr a (fst_pair _ _) (.eqRefl _) (.eqRefl _) (snd_pair _ _))

theorem row_cn_at (a : PR 4) (N x r : PTm n) (h : Γ ⊢[PRAAx] CN a N x) (hr : Γ ⊢[PRAAx] lt r N) :
    Γ ⊢[PRAAx] rowCN a N r x := by
  have rule : Γ ⊢[PRAAx] lt r N ⟶ rowCN a N r x := by simpa [CN] using h.allE r
  exact .impE rule hr

theorem entry_regular (a : PR 4) (N x r j s t : PTm n) (h : Γ ⊢[PRAAx] CN a N x)
    (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    distanceBounded (entry a r j s x) (entry a r j t x) (unit s+unit t) (unit s*unit t) :=
  GaussianRationalDistanceOrder.distance_congr (row_reader_at a r j s x) (row_reader_at a r j t x) (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.CN_at (rowReaderF a) N (rowData r x) j s t (row_cn_at a N x r h hr) hj)

theorem sample_lookup (a : PR 4) (N s x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] cell (sample a N s x) r j ≐ entry a r j s x := by
  have h := table_lookup (Γ := Γ) (sampleBody a) N N (pairT s x) r j hr hj
  simp only [sampleBody,subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at h
  exact h.eqTrans (entry_congr a (.eqRefl _) (.eqRefl _) (fst_pair _ _) (snd_pair _ _))
theorem sample_shape (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx] shape (sample a N s x) N N := by
  refine .andI (table_length _ _ _ _) (.allI (.impI ?_))
  simpa [Syn.shift,sample] using table_row_length (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (sampleBody a) (Syn.shift N) (Syn.shift N) (pairT (Syn.shift s) (Syn.shift x)) (var 0) Prf.hyp0

theorem row_bound_value (a : PR 4) (N r x : PTm n) : Γ ⊢[PRAAx]
    rowBound a N r x ≐ GaussianCoefficientNameBounds.A (rowReaderF a) N (rowData r x) := by
  simpa [rowBound,rowRadiusF,ap2] using
    toPR_eq (Γ := Γ) (GaussianCoefficientNameBounds.A (rowReaderF a) (var 0) (var 1) : PTm 2) ![N,rowData r x]
theorem bound_body_at (a : PR 4) (N x r : PTm n) : Γ ⊢[PRAAx]
    inst2 (boundBody a) r (boundData N x) ≐ rowBound a N r x := by
  simp only [boundBody,inst2,subst_rowBound,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp2 (rowRadiusF a) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
theorem B_positive (a : PR 4) (N x : PTm n) : Γ ⊢[PRAAx] le one (B a N x) := le_add_right _ _
theorem row_bound_le_B (a : PR 4) (N x r : PTm n) (hr : Γ ⊢[PRAAx] lt r N) : Γ ⊢[PRAAx]
    le (GaussianCoefficientNameBounds.A (rowReaderF a) N (rowData r x)) (B a N x) := by
  have term := le_congr (bound_body_at a N x r) (.eqRefl _)
    (LeanProofs.IPRA.term_le_sum (boundBody a) (i := r) (M := N) (x := boundData N x) hr)
  exact le_congr (row_bound_value a N r x) (.eqRefl _) (le_trans term
    (le_of_eq_add (d := one) (by unfold B; ipra_ring)))

theorem entry_bound (a : PR 4) (N x r j s : PTm n) (h : Γ ⊢[PRAAx] CN a N x)
    (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] bounded (entry a r j s x) (B a N x) one := by
  let A := GaussianCoefficientNameBounds.A (rowReaderF a) N (rowData r x)
  have small := GaussianCoefficientNameBounds.sample_bound (rowReaderF a) N (rowData r x) j s (row_cn_at a N x r h hr) hj
  have disk := GaussianRationalReciprocal.bound_congr (row_reader_at a r j s x) (.eqRefl _) (.eqRefl _) small
  have radius : Γ ⊢[PRAAx] le (PTm.monus A one) (B a N x) :=
    le_trans (GaussianMonicResidualRadius.monus_le_left A one) (row_bound_le_B a N x r hr)
  exact GaussianCoefficientNameBounds.bounded_radius_mono_one radius disk

theorem sample_row_bounds (a : PR 4) (N s x r : PTm n) (h : Γ ⊢[PRAAx] CN a N x) (hr : Γ ⊢[PRAAx] lt r N) :
    Γ ⊢[PRAAx] rowBounds (sample a N s x) N (B a N x) r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_CN,Syn.shift] using h.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have value := sample_lookup (Γ := Δ) a (Syn.shift N) (Syn.shift s) (Syn.shift x) (Syn.shift r) (var 0) hrs.wk Prf.hyp0
  have actual := GaussianRationalReciprocal.bound_congr value.eqSymm (.eqRefl _) (.eqRefl _)
    (entry_bound a (Syn.shift N) (Syn.shift x) (Syn.shift r) (var 0) (Syn.shift s) hs.wk hrs.wk Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_sample,subst_B] using actual

theorem sample_entry_bounds (a : PR 4) (N s x : PTm n) (h : Γ ⊢[PRAAx] CN a N x) :
    Γ ⊢[PRAAx] entryBounds (sample a N s x) N (B a N x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_CN,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_sample,subst_B] using sample_row_bounds
    (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) a (Syn.shift N) (Syn.shift s) (Syn.shift x) (var 0) hs.wk Prf.hyp0

theorem sample_row_distances (a : PR 4) (N s t x r : PTm n) (h : Γ ⊢[PRAAx] CN a N x) (hr : Γ ⊢[PRAAx] lt r N) :
    Γ ⊢[PRAAx] rowDistances (sample a N s x) (sample a N t x) N (unit s+unit t) (unit s*unit t) r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_CN,Syn.shift] using h.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have vs := sample_lookup (Γ := Δ) a (Syn.shift N) (Syn.shift s) (Syn.shift x) (Syn.shift r) (var 0) hrs.wk Prf.hyp0
  have vt := sample_lookup (Γ := Δ) a (Syn.shift N) (Syn.shift t) (Syn.shift x) (Syn.shift r) (var 0) hrs.wk Prf.hyp0
  have actual := GaussianRationalDistanceOrder.distance_congr vs.eqSymm vt.eqSymm (.eqRefl _) (.eqRefl _)
    (entry_regular a (Syn.shift N) (Syn.shift x) (Syn.shift r) (var 0) (Syn.shift s) (Syn.shift t) hs.wk hrs.wk Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_sample,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul] using actual

theorem sample_distances (a : PR 4) (N s t x : PTm n) (h : Γ ⊢[PRAAx] CN a N x) :
    Γ ⊢[PRAAx] entryDistances (sample a N s x) (sample a N t x) N (unit s+unit t) (unit s*unit t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_CN,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_sample,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul] using sample_row_distances
    (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) a (Syn.shift N) (Syn.shift s) (Syn.shift t) (Syn.shift x) (var 0) hs.wk Prf.hyp0

theorem sample_pair_input (a : PR 4) (N s t x : PTm n) (h : Γ ⊢[PRAAx] CN a N x) : Γ ⊢[PRAAx]
    GaussianCharacteristicFactorBounds.input (sample a N s x) (sample a N t x) N (B a N x) (unit s+unit t) (unit s*unit t) :=
  .andI (sample_shape a N s x) (.andI (sample_shape a N t x)
    (.andI (sample_entry_bounds a N s x h) (.andI (sample_entry_bounds a N t x h)
      (.andI (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t)) (sample_distances a N s t x h)))))

def sampleF (a : PR 4) : PR 3 := PTm.toPR (sample a (var 0) (var 1) (var 2))
def boundF (a : PR 4) : PR 2 := PTm.toPR (B a (var 0) (var 1))
def output (a : PR 4) (N s x : PTm n) : PTm n := pairT (sample a N s x) (B a N x)
def outputF (a : PR 4) : PR 3 := PTm.toPR (output a (var 0) (var 1) (var 2))
def run (a : PR 4) (N s x : PTm n) : PTm n := ap3 (outputF a) N s x
ipra_subst output
ipra_subst run
theorem sample_at (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx] ap3 (sampleF a) N s x ≐ sample a N s x := by
  simpa [sampleF,ap3] using toPR_eq (Γ := Γ) (sample a (var 0) (var 1) (var 2) : PTm 3) ![N,s,x]
theorem bound_at (a : PR 4) (N x : PTm n) : Γ ⊢[PRAAx] ap2 (boundF a) N x ≐ B a N x := by
  simpa [boundF,ap2] using toPR_eq (Γ := Γ) (B a (var 0) (var 1) : PTm 2) ![N,x]
theorem program_at (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx] run a N s x ≐ output a N s x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) : PTm 3) ![N,s,x]
theorem returned_sample (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx] fstT (run a N s x) ≐ sample a N s x :=
  (program_at a N s x).fstE
theorem returned_bound (a : PR 4) (N s x : PTm n) : Γ ⊢[PRAAx] sndT (run a N s x) ≐ B a N x :=
  (program_at a N s x).sndE
theorem returned_entry_bound (a : PR 4) (N s x r j : PTm n) (h : Γ ⊢[PRAAx] CN a N x)
    (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    bounded (cell (fstT (run a N s x)) r j) (sndT (run a N s x)) one :=
  GaussianRationalReciprocal.bound_congr
    ((Foundations.SequenceComposition.entry_congr (Foundations.SequenceComposition.entry_congr (returned_sample a N s x)
      (.eqRefl _)) (.eqRefl _)).eqTrans (sample_lookup a N s x r j hr hj)).eqSymm
    (returned_bound a N s x).eqSymm (.eqRefl _) (entry_bound a N x r j s h hr hj)

theorem actual_source_bound_positive_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (B a (var 0) (var 1))) := closeUniv 2 (B_positive a _ _)
theorem actual_matrix_sample_shape_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (shape (sample a (var 0) (var 1) (var 2)) (var 0) (var 0)) := closeUniv 3 (sample_shape a _ _ _)
theorem actual_original_entry_regular_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (CN a (var 0) (var 1) ⟶ lt (var 2) (var 0) ⟶ lt (var 3) (var 0) ⟶
      distanceBounded (entry a (var 2) (var 3) (var 4) (var 1)) (entry a (var 2) (var 3) (var 5) (var 1))
        (unit (var 4)+unit (var 5)) (unit (var 4)*unit (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (entry_regular a _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_original_sample_bound_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (CN a (var 0) (var 1) ⟶ lt (var 2) (var 0) ⟶ lt (var 3) (var 0) ⟶
      bounded (entry a (var 2) (var 3) (var 4) (var 1)) (B a (var 0) (var 1)) one) :=
  closeUniv 5 (.impI (.impI (.impI (entry_bound a _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_sample_entry_bounds_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ entryBounds (sample a (var 0) (var 1) (var 2)) (var 0) (B a (var 0) (var 2))) :=
  closeUniv 3 (.impI (sample_entry_bounds a _ _ _ Prf.hyp0))
theorem actual_sample_pair_input_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (CN a (var 0) (var 3) ⟶ GaussianCharacteristicFactorBounds.input
      (sample a (var 0) (var 1) (var 3)) (sample a (var 0) (var 2) (var 3)) (var 0) (B a (var 0) (var 3))
        (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) := closeUniv 4 (.impI (sample_pair_input a _ _ _ _ Prf.hyp0))
theorem actual_matrix_sample_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (sampleF a) (var 0) (var 1) (var 2) ≐ sample a (var 0) (var 1) (var 2)) := closeUniv 3 (sample_at a _ _ _)
theorem actual_matrix_bound_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (boundF a) (var 0) (var 1) ≐ B a (var 0) (var 1)) := closeUniv 2 (bound_at a _ _)
theorem actual_matrix_output_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run a (var 0) (var 1) (var 2) ≐ output a (var 0) (var 1) (var 2) ⋏
      (fstT (run a (var 0) (var 1) (var 2)) ≐ sample a (var 0) (var 1) (var 2) ⋏
        sndT (run a (var 0) (var 1) (var 2)) ≐ B a (var 0) (var 2))) :=
  closeUniv 3 (.andI (program_at a _ _ _) (.andI (returned_sample a _ _ _) (returned_bound a _ _ _)))
theorem actual_returned_matrix_entry_bound_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (CN a (var 0) (var 2) ⟶ lt (var 3) (var 0) ⟶ lt (var 4) (var 0) ⟶
      bounded (cell (fstT (run a (var 0) (var 1) (var 2))) (var 3) (var 4))
        (sndT (run a (var 0) (var 1) (var 2))) one) :=
  closeUniv 5 (.impI (.impI (.impI (returned_entry_bound a _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianMatrixNames

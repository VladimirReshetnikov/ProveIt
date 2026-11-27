import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalRowElimination
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini

/-!
# Actual finite row combinations and their homogeneous dot equations

One fixed PR program builds every column of the original numerical row
combination. A single actual triple-product body and the proved Gaussian
finite-sum interchange derive its dot identity. Membership supplies only
the exact per-column field-value certificate for that produced vector.
No span solver, rank theorem or output dot law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRowSpan

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell subst_cell)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (singleton singleton_lookup)
open LeanProofs.IPRA.Analysis.GaussianRationalRowElimination (rowDot nullRows)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_congr_bounded sum_index_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalValueEquality (valueEqual)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def columnData (A C j : PTm n) : PTm n := pairT A (pairT C j)
def columnBody : PTm 2 := qmul (entry (fstT (sndT (var 1))) (var 0))
  (cell (fstT (var 1)) (var 0) (sndT (sndT (var 1))))
def combinationAt (A R C j : PTm n) : PTm n := sum columnBody R (columnData A C j)
def combinationData (A R C : PTm n) : PTm n := pairT A (pairT R C)
def combinationBody : PTm 2 := combinationAt (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def rowCombination (A R N C : PTm n) : PTm n := sequence combinationBody N (combinationData A R C)
def vectorDot (N v l : PTm n) : PTm n := rowDot (singleton v) N l zero
def tripleData (A C l : PTm n) : PTm n := pairT A (pairT C l)
def triple (A C l i j : PTm n) : PTm n := qmul (qmul (entry C i) (cell A i j)) (entry l j)
def tripleBody : PTm 3 := triple (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
def weightedData (A N C l : PTm n) : PTm n := pairT A (pairT N (pairT C l))
def weightedBody : PTm 2 := qmul (entry (fstT (sndT (sndT (var 1)))) (var 0))
  (rowDot (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (sndT (var 1)))) (var 0))
def weightedDot (A R N C l : PTm n) : PTm n := sum weightedBody R (weightedData A N C l)

ipra_subst columnData
ipra_subst combinationAt
ipra_subst combinationData
ipra_subst rowCombination
ipra_subst vectorDot
ipra_subst tripleData
ipra_subst triple
ipra_subst weightedData
ipra_subst weightedDot

theorem column_body_at (A C j i : PTm n) : Γ ⊢[PRAAx]
    inst2 columnBody i (columnData A C j) ≐ qmul (entry C i) (cell A i j) := by
  simp only [columnBody,inst2,GaussianRationalHorner.subst_qmul,subst_entry,subst_cell,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (entry_congr (snd_pair _ _).fstE (.eqRefl _))
    (entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _).sndE)
theorem combination_body_at (A R C j : PTm n) : Γ ⊢[PRAAx]
    inst2 combinationBody j (combinationData A R C) ≐ combinationAt A R C j := by
  simp only [combinationBody,inst2,subst_combinationAt,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  simpa using Prf.eqCongr (Γ := Γ) (combinationAt (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (combinationData A R C),fstT (sndT (combinationData A R C)),sndT (sndT (combinationData A R C)),j])
    (σ' := ![A,R,C,j]) (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
theorem combination_length (A R N C : PTm n) : Γ ⊢[PRAAx] length (rowCombination A R N C) ≐ N := sequence_length _ _ _
theorem combination_lookup (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (rowCombination A R N C) j ≐ combinationAt A R C j :=
  (sequence_decode combinationBody hj).eqTrans (combination_body_at _ _ _ _)
theorem combination_canonical (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    canonical (entry (rowCombination A R N C) j) :=
  GaussianRationalHorner.canonical_congr (combination_lookup _ _ _ _ _ hj) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem vector_dot_term (v l j : PTm n) : Γ ⊢[PRAAx]
    inst2 GaussianRationalRowElimination.dotBody j (GaussianRationalRowElimination.dotData (singleton v) l zero) ≐
      qmul (entry v j) (entry l j) :=
  (GaussianRationalRowElimination.dot_body_at _ _ _ _).eqTrans
    (qmul_congr (entry_congr (singleton_lookup _) (.eqRefl _)) (.eqRefl _))
theorem vector_dot_canonical (N v l : PTm n) : Γ ⊢[PRAAx] canonical (vectorDot N v l) :=
  GaussianRationalRowElimination.row_dot_canonical _ _ _ _
theorem triple_body_at (A C l i j : PTm n) : Γ ⊢[PRAAx]
    inst3 tripleBody i j (tripleData A C l) ≐ triple A C l i j := by
  simp only [tripleBody,inst3,subst_triple,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  simpa using Prf.eqCongr (Γ := Γ) (triple (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (tripleData A C l),fstT (sndT (tripleData A C l)),sndT (sndT (tripleData A C l)),i,j])
    (σ' := ![A,C,l,i,j]) (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _
      · exact .eqRefl _)
theorem weighted_body_at (A N C l i : PTm n) : Γ ⊢[PRAAx]
    inst2 weightedBody i (weightedData A N C l) ≐ qmul (entry C i) (rowDot A N l i) := by
  have tail := snd_pair (Γ := Γ) A (pairT N (pairT C l))
  have rest := (congrSnd tail).eqTrans (snd_pair N (pairT C l))
  simp only [weightedBody,inst2,GaussianRationalHorner.subst_qmul,subst_entry,GaussianRationalRowElimination.subst_rowDot,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr (entry_congr rest.fstE (.eqRefl _))
    (GaussianRationalRowElimination.row_dot_congr (fst_pair _ _) tail.fstE
      rest.sndE (.eqRefl _))

def rightMultiplyBody (f : PTm 2) : PTm 2 := qmul (inst2 f (var 0) (sndT (var 1))) (fstT (var 1))
theorem right_multiply_at (f : PTm 2) (a i z : PTm n) : Γ ⊢[PRAAx]
    inst2 (rightMultiplyBody f) i (pairT a z) ≐ qmul (inst2 f i z) a := by
  have read : Syn.subst ![i,pairT a z] (Syn.subst ![var 0,sndT (var 1)] f) = inst2 f i (sndT (pairT a z)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext k
    fin_cases k <;> simp
  simp only [rightMultiplyBody,inst2,GaussianRationalHorner.subst_qmul,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,read]
  exact qmul_congr (congrInst2 f (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)
theorem sum_right_multiply (f : PTm 2) (a N z : PTm n) : Γ ⊢[PRAAx]
    sum (rightMultiplyBody f) N (pairT a z) ≐ qmul (sum f N z) a := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (rightMultiplyBody f) (GaussianRationalFiniteSum.multiplyBody f) N (pairT a z) (pairT a z) ?_).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply f a N z).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT] using
    (right_multiply_at f (Syn.shift a) (var 0) (Syn.shift z)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianRationalFiniteSum.multiply_body_at f (Syn.shift a) (var 0) (Syn.shift z)).eqSymm)

theorem row_factor (A N C l i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row tripleBody i N (tripleData A C l) ≐ qmul (entry C i) (rowDot A N l i) := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (GaussianRationalFubini.rowBody tripleBody)
    (GaussianRationalFiniteSum.multiplyBody GaussianRationalRowElimination.dotBody) N (pairT i (tripleData A C l))
      (pairT (entry C i) (GaussianRationalRowElimination.dotData A l i)) ?_).eqTrans
        (GaussianRationalFiniteSum.sum_multiply _ _ _ _)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have low := (GaussianRationalFubini.row_entry (Γ := Δ) tripleBody (Syn.shift i) (var 0)
    (tripleData (Syn.shift A) (Syn.shift C) (Syn.shift l))).eqTrans
      ((triple_body_at _ _ _ _ _).eqTrans (GaussianReciprocalHorner.qmul_associative _ _ _))
  have high := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) GaussianRationalRowElimination.dotBody
    (entry (Syn.shift C) (Syn.shift i)) (var 0) (GaussianRationalRowElimination.dotData (Syn.shift A) (Syn.shift l) (Syn.shift i))).eqTrans
      (qmul_congr (.eqRefl _) (GaussianRationalRowElimination.dot_body_at _ _ _ _))
  simpa only [Δ,Syn.shift,subst_pairT,subst_entry,subst_tripleData,GaussianRationalRowElimination.subst_dotData] using low.eqTrans high.eqSymm
theorem column_factor (A R C l j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column tripleBody j R (tripleData A C l) ≐ qmul (combinationAt A R C j) (entry l j) := by
  refine (GaussianRationalFiniteSum.sum_congr_bounded (GaussianRationalFubini.columnBody tripleBody)
    (rightMultiplyBody columnBody) R (pairT j (tripleData A C l)) (pairT (entry l j) (columnData A C j)) ?_).eqTrans
      (sum_right_multiply _ _ _ _)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have low := (GaussianRationalFubini.column_entry (Γ := Δ) tripleBody (var 0) (Syn.shift j)
    (tripleData (Syn.shift A) (Syn.shift C) (Syn.shift l))).eqTrans (triple_body_at _ _ _ _ _)
  have high := (right_multiply_at (Γ := Δ) columnBody (entry (Syn.shift l) (Syn.shift j)) (var 0)
    (columnData (Syn.shift A) (Syn.shift C) (Syn.shift j))).eqTrans
      (qmul_congr (column_body_at _ _ _ _) (.eqRefl _))
  simpa only [Δ,Syn.shift,subst_pairT,subst_entry,subst_tripleData,subst_columnData] using low.eqTrans high.eqSymm
theorem dot_columns (A R N C l : PTm n) : Γ ⊢[PRAAx]
    vectorDot N (rowCombination A R N C) l ≐ GaussianRationalFubini.columnFirst tripleBody R N (tripleData A C l) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have low := (vector_dot_term (Γ := Δ) (rowCombination (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C))
    (Syn.shift l) (var 0)).eqTrans (qmul_congr (combination_lookup _ _ _ _ _ Prf.hyp0) (.eqRefl _))
  have high := (GaussianRationalFubini.column_sum_at (Γ := Δ) tripleBody (var 0) (Syn.shift R)
    (tripleData (Syn.shift A) (Syn.shift C) (Syn.shift l))).eqTrans (column_factor _ _ _ _ _)
  simpa only [Δ,Syn.shift,subst_pairT,subst_tripleData,subst_rowCombination,GaussianRationalRowElimination.subst_dotData,
    GaussianRationalMonicReduction.subst_singleton,ConciseIPRA.PTm.subst_zero] using low.eqTrans high.eqSymm
theorem rows_weighted (A R N C l : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.rowFirst tripleBody R N (tripleData A C l) ≐ weightedDot A R N C l := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have low := (GaussianRationalFubini.row_sum_at (Γ := Δ) tripleBody (var 0) (Syn.shift N)
    (tripleData (Syn.shift A) (Syn.shift C) (Syn.shift l))).eqTrans (row_factor _ _ _ _ _)
  simpa only [Δ,Syn.shift,subst_pairT,subst_tripleData,subst_weightedData] using
    low.eqTrans (weighted_body_at (Γ := Δ) (Syn.shift A) (Syn.shift N) (Syn.shift C) (Syn.shift l) (var 0)).eqSymm
theorem combination_dot (A R N C l : PTm n) : Γ ⊢[PRAAx]
    vectorDot N (rowCombination A R N C) l ≐ weightedDot A R N C l :=
  (dot_columns _ _ _ _ _).eqTrans
    ((GaussianRationalFubini.fubini tripleBody R N (tripleData A C l)).eqSymm.eqTrans (rows_weighted _ _ _ _ _))
theorem weighted_zero (A R N C l : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx]
    weightedDot A R N C l ≐ qzero := by
  apply GaussianRationalMatrixFiniteSums.sum_zero_of_terms
  have hs : Γ.map Fm.shift ⊢[PRAAx] nullRows (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift l) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_nullRows,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have eq := (weighted_body_at (Γ := Δ) (Syn.shift A) (Syn.shift N) (Syn.shift C) (Syn.shift l) (var 0)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalRowElimination.null_at _ _ _ _ _ hs.wk Prf.hyp0)).eqTrans (qmul_zero_right _))
  simpa only [Δ,Syn.shift,subst_weightedData,GaussianRationalHorner.subst_qzero] using eq
theorem combination_zero (A R N C l : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx]
    vectorDot N (rowCombination A R N C) l ≐ qzero := (combination_dot _ _ _ _ _).eqTrans (weighted_zero _ _ _ _ _ h)

def membership (A R N C v : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  valueEqual (entry (Syn.shift v) (var 0))
    (entry (rowCombination (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C)) (var 0)))
def witness (A R N C v : PTm n) : Fm PTm n := GaussianRationalRowElimination.shape A R N ⋏
  ((length C ≐ R) ⋏ ((length v ≐ N) ⋏ membership A R N C v))
ipra_subst membership [Syn.subst_shift, Syn.shift_subst]
ipra_subst witness
theorem membership_at (A R N C v j : PTm n) (h : Γ ⊢[PRAAx] membership A R N C v)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] valueEqual (entry v j) (entry (rowCombination A R N C) j) := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ valueEqual (entry v j) (entry (rowCombination A R N C) j) := by
    simpa only [membership,Fm.subst_imp,GaussianRationalValueEquality.subst_valueEqual,subst_lt,subst_entry,subst_rowCombination,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE rule hj
theorem product_left_values (a b c : PTm n) (h : Γ ⊢[PRAAx] valueEqual a b) : Γ ⊢[PRAAx] qmul a c ≐ qmul b c :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalValueEquality.qmul_right_recode_equal c a b
      (GaussianRationalValueEquality.recode_equal_of_equal_values _ _ h)).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
theorem membership_dot_equal (A R N C v l : PTm n) (h : Γ ⊢[PRAAx] membership A R N C v) : Γ ⊢[PRAAx]
    vectorDot N v l ≐ vectorDot N (rowCombination A R N C) l := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  have hs : Γ.map Fm.shift ⊢[PRAAx] membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C) (Syn.shift v) := by
    simpa only [Fm.shift,subst_membership,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have eq := (vector_dot_term (Γ := Δ) (Syn.shift v) (Syn.shift l) (var 0)).eqTrans
    ((product_left_values _ _ _ (membership_at _ _ _ _ _ _ hs.wk Prf.hyp0)).eqTrans
      (vector_dot_term (rowCombination (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift C)) (Syn.shift l) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,GaussianRationalMonicReduction.subst_singleton,
    subst_rowCombination,ConciseIPRA.PTm.subst_zero] using eq
theorem membership_zero (A R N C v l : PTm n) (hm : Γ ⊢[PRAAx] membership A R N C v)
    (ha : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx] vectorDot N v l ≐ qzero :=
  (membership_dot_equal _ _ _ _ _ _ hm).eqTrans (combination_zero _ _ _ _ _ ha)
theorem witness_zero (A R N C v l : PTm n) (hw : Γ ⊢[PRAAx] witness A R N C v)
    (ha : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx] vectorDot N v l ≐ qzero :=
  membership_zero _ _ _ _ _ _ (.andE₂ (.andE₂ (.andE₂ hw))) ha

theorem empty_rows_at (A N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (rowCombination A zero N C) j ≐ qzero :=
  (combination_lookup _ _ _ _ _ hj).eqTrans (GaussianRationalFiniteSum.sum_zero _ _)
theorem empty_dot (v l : PTm n) : Γ ⊢[PRAAx] vectorDot zero v l ≐ qzero := GaussianRationalRowElimination.empty_dot _ _ _
theorem vector_dot_congr {N N' v v' l l' : PTm n} (hN : Γ ⊢[PRAAx] N ≐ N')
    (hv : Γ ⊢[PRAAx] v ≐ v') (hl : Γ ⊢[PRAAx] l ≐ l') : Γ ⊢[PRAAx] vectorDot N v l ≐ vectorDot N' v' l' := by
  ipra_congr (vectorDot (var 0) (var 1) (var 2) : PTm 3) with [hN, hv, hl]

/-! The PR4 producer has no lambda or presumed span witness as an extra
input. The supplied C is the original numerical coefficient vector. -/
def outputF : PR 4 := PTm.toPR (rowCombination (var 0) (var 1) (var 2) (var 3))
def run (A R N C : PTm n) : PTm n := app outputF ![A,R,N,C]
ipra_subst run
theorem program_at (A R N C : PTm n) : Γ ⊢[PRAAx] run A R N C ≐ rowCombination A R N C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (rowCombination (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,R,N,C]
theorem returned_length (A R N C : PTm n) : Γ ⊢[PRAAx] length (run A R N C) ≐ N :=
  (congrFst (program_at _ _ _ _)).eqTrans (combination_length _ _ _ _)
theorem returned_lookup (A R N C j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (run A R N C) j ≐ combinationAt A R C j :=
  (entry_congr (program_at _ _ _ _) (.eqRefl _)).eqTrans (combination_lookup _ _ _ _ _ hj)
theorem returned_dot (A R N C l : PTm n) : Γ ⊢[PRAAx] vectorDot N (run A R N C) l ≐ weightedDot A R N C l :=
  (vector_dot_congr (.eqRefl _) (program_at _ _ _ _) (.eqRefl _)).eqTrans (combination_dot _ _ _ _ _)
theorem returned_zero (A R N C l : PTm n) (h : Γ ⊢[PRAAx] nullRows A R N l) : Γ ⊢[PRAAx]
    vectorDot N (run A R N C) l ≐ qzero := (returned_dot _ _ _ _ _).eqTrans (weighted_zero _ _ _ _ _ h)

/-! Every original rectangular size, code, witness and vector query is
bound internally. These are span-certificate transports, not a solver. -/
theorem actual_combination_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (rowCombination (var 0) (var 1) (var 2) (var 3)) ≐ var 2) := closeUniv 4 (combination_length _ _ _ _)
theorem actual_combination_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ entry (rowCombination (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      combinationAt (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (combination_lookup _ _ _ _ _ Prf.hyp0))
theorem actual_combination_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (vectorDot (var 2) (rowCombination (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      weightedDot (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (combination_dot _ _ _ _ _)
theorem actual_null_combination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (nullRows (var 0) (var 1) (var 2) (var 4) ⟶
      vectorDot (var 2) (rowCombination (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (combination_zero _ _ _ _ _ Prf.hyp0))
theorem actual_membership_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (membership (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      vectorDot (var 2) (var 4) (var 5) ≐ vectorDot (var 2) (rowCombination (var 0) (var 1) (var 2) (var 3)) (var 5)) :=
  closeUniv 6 (.impI (membership_dot_equal _ _ _ _ _ _ Prf.hyp0))
theorem actual_membership_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (membership (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ nullRows (var 0) (var 1) (var 2) (var 5) ⟶
      vectorDot (var 2) (var 4) (var 5) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (membership_zero _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_span_witness_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (witness (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ nullRows (var 0) (var 1) (var 2) (var 5) ⟶
      vectorDot (var 2) (var 4) (var 5) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (witness_zero _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_empty_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ entry (rowCombination (var 0) zero (var 1) (var 2)) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (empty_rows_at _ _ _ _ Prf.hyp0))
theorem actual_empty_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (vectorDot zero (var 0) (var 1) ≐ qzero) := closeUniv 2 (empty_dot _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((run (var 0) (var 1) (var 2) (var 3) ≐ rowCombination (var 0) (var 1) (var 2) (var 3)) ⋏
      (length (run (var 0) (var 1) (var 2) (var 3)) ≐ var 2)) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (returned_length _ _ _ _))
theorem actual_returned_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (vectorDot (var 2) (run (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
      weightedDot (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (returned_dot _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalRowSpan

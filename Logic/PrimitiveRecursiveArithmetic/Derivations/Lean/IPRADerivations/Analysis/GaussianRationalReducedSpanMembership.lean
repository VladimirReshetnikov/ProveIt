import IPRADerivations.Analysis.GaussianRationalFullReducedSpan

/-!
# Exact bounded membership test for the computed reduced row span

The target's tagged coordinates determine the coefficients of all
marked rows in any representation. Unmarked rows contribute zero.
The actual candidate coefficients therefore represent the target if
any coefficient list does. The bounded test checks that candidate at
all original column indices.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalReducedSpanMembership

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qzero)
open GaussianRationalRowElimination (shape)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalRowSpan
  (columnBody columnData combinationAt rowCombination column_body_at combination_lookup
    combination_canonical membership membership_at)
open GaussianRationalEliminationTagProfile (rowColumn row_column_found)
open GaussianRationalFreeColumnVector (pivotRow pivot_row_at field_zero_at)
open GaussianRationalRankNullityCriterion (finalMatrix finalHistory reader reader_at)
open GaussianRationalEliminationLoop (matrix history)
open GaussianRationalFullReducedSpan (weights weights_lookup tagged_column)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianRationalSyntheticCoefficientValues (qmul_recode_right)
open GaussianRationalValueEquality
  (recode_equal_of_equal_values equal_values_of_recode_equal qmul_right_recode_equal)
open GaussianTranslatedNonconstant (recode recode_eq recode_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_elim all_intro all_cases eq_of_eqb eqb_cases one_ne_zero)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem marked_column_combination (A R N C j i : PTm n)
    (hA : Γ ⊢[PRAAx] shape A R N) (hj : Γ ⊢[PRAAx] lt j N) (hi : Γ ⊢[PRAAx] lt i R)
    (tag : Γ ⊢[PRAAx] entry (finalHistory A R N) j ≐ succ i) :
    Γ ⊢[PRAAx] combinationAt (finalMatrix A R N) R C j ≐ recode (entry C i) := by
  let H := finalHistory A R N
  let E := finalMatrix A R N
  let p := pivotRow H j
  have hn : Γ ⊢[PRAAx] neg (entry H j ≐ zero) :=
    .impI (succ_ne_zero (tag.wk.eqSymm.eqTrans Prf.hyp0))
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hA.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  have hns : Γ.map Fm.shift ⊢[PRAAx] neg (entry (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift j) ≐ zero) := by
    simpa [Fm.shift, Syn.shift, H] using hn.shift
  have folded : Γ ⊢[PRAAx]
      combinationAt E R C j ≐ GaussianRationalMatrixFiniteSums.deltaSum reader R p C := by
    refine GaussianRationalFiniteSum.sum_congr_bounded columnBody
      (GaussianRationalMatrixFiniteSums.deltaBody reader) R (columnData E C j) (pairT p C)
      (.allI (.impI ?_))
    let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
    have col := tagged_column (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift j) (var 0)
      hAs.wk hjs.wk Prf.hyp0 hns.wk
    have low := column_body_at (Γ := Δ) (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift C) (Syn.shift j) (var 0)
    have high := GaussianRationalMatrixFiniteSums.delta_body_at (Γ := Δ) reader
      (pivotRow (finalHistory (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift j)) (var 0) (Syn.shift C)
    rw [reader_at] at high
    simpa only [Δ, Syn.shift, E, p, H, GaussianRationalRowSpan.subst_columnData,
      GaussianRationalRankNullityCriterion.subst_finalMatrix, GaussianRationalRankNullityCriterion.subst_finalHistory,
      GaussianRationalFreeColumnVector.subst_pivotRow, subst_pairT] using
      low.eqTrans ((qmul_recode_right _ _).eqSymm.eqTrans
        ((qmul_congr (.eqRefl _) col).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans high.eqSymm)))
  have hp := pivot_row_at H j i tag
  exact folded.eqTrans ((GaussianRationalMatrixFiniteSums.sum_delta reader R p C
    (lt_congr hp.eqSymm (.eqRefl _) hi)).eqTrans (by
      rw [reader_at]
      exact recode_congr (Foundations.SequenceComposition.entry_congr (.eqRefl _) hp)))

theorem value_at (E R N C v j : PTm n) (h : Γ ⊢[PRAAx] membership E R N C v)
    (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] recode (entry v j) ≐ combinationAt E R C j :=
  (recode_equal_of_equal_values _ _ (membership_at E R N C v j h hj)).eqTrans
    ((recode_eq _ (combination_canonical E R N C j hj)).eqTrans (combination_lookup E R N C j hj))

theorem candidate_summand (A R N C v i j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (h : Γ ⊢[PRAAx] membership (finalMatrix A R N) R N C v)
    (hi : Γ ⊢[PRAAx] lt i R) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] qmul (entry (weights A R N v) i) (cell (finalMatrix A R N) i j) ≐
      qmul (entry C i) (cell (finalMatrix A R N) i j) := by
  let H := finalHistory A R N
  let E := finalMatrix A R N
  let p := rowColumn A R N N i
  refine .orE (GaussianRationalPivotSearch.available_cases H N i) ?_ ?_
  · have hit := row_column_found (Γ := (GaussianRationalPivotSearch.available H N i ≐ zero) :: Γ)
      A R N N i Prf.hyp0
    have selection : (GaussianRationalPivotSearch.available H N i ≐ zero) :: Γ ⊢[PRAAx]
        recode (entry (weights A R N v) i) ≐ recode (entry v p) :=
      recode_congr (weights_lookup A R N v i hi.wk)
    have coefficient := selection.eqTrans ((value_at E R N C v p h.wk (.andE₁ hit)).eqTrans
      (marked_column_combination A R N C p i hA.wk (.andE₁ hit) hi.wk (.andE₁ (.andE₂ hit))))
    exact (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((qmul_right_recode_equal _ _ _ coefficient).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  · have unmarked := GaussianRationalPivotSearch.available_unmarked
      (Γ := (GaussianRationalPivotSearch.available H N i ≐ one) :: Γ) H N i Prf.hyp0
    have z := field_zero_at E N i j
      (GaussianRationalAnnihilatorVector.reduced_unmarked_row A R N i hA.wk hi.wk unmarked) hj.wk
    have productZero (w : PTm n) : (GaussianRationalPivotSearch.available H N i ≐ one) :: Γ ⊢[PRAAx]
        qmul w (cell E i j) ≐ qzero :=
      (qmul_recode_right _ _).eqSymm.eqTrans ((qmul_congr (.eqRefl _) z).eqTrans (qmul_zero_right _))
    exact (productZero _).eqTrans (productZero _).eqSymm

theorem candidate_coordinate (A R N C v j : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (h : Γ ⊢[PRAAx] membership (finalMatrix A R N) R N C v) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] combinationAt (finalMatrix A R N) R (weights A R N v) j ≐
      combinationAt (finalMatrix A R N) R C j := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hA.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] membership (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift R) (Syn.shift N) (Syn.shift C) (Syn.shift v) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  have hjs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  let E := finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N)
  let W := weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)
  have q := candidate_summand (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N)
    (Syn.shift C) (Syn.shift v) (var 0) (Syn.shift j) hAs.wk hs.wk Prf.hyp0 hjs.wk
  have lhs := column_body_at (Γ := Δ) E W (Syn.shift j) (var 0)
  have rhs := column_body_at (Γ := Δ) E (Syn.shift C) (Syn.shift j) (var 0)
  simpa only [Δ, E, W, Syn.shift, GaussianRationalRowSpan.subst_columnData,
    GaussianRationalRankNullityCriterion.subst_finalMatrix, GaussianRationalFullReducedSpan.subst_weights] using
    lhs.eqTrans (q.eqTrans rhs.eqSymm)

def checkCoordinate (E R C v j : PTm n) : PTm n :=
  eqb (recode (entry v j)) (combinationAt E R C j)

def checkData (E R C v : PTm n) : PTm n := pairT E (pairT R (pairT C v))

def checkBody : PTm 2 := checkCoordinate (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) (var 0)

def test (A R N v : PTm n) : PTm n :=
  allB checkBody N (checkData (finalMatrix A R N) R (weights A R N v) v)

@[simp] theorem subst_checkCoordinate {k : ℕ} (σ : Fin n → PTm k) (E R C v j : PTm n) :
    Syn.subst σ (checkCoordinate E R C v j) = checkCoordinate (Syn.subst σ E) (Syn.subst σ R)
      (Syn.subst σ C) (Syn.subst σ v) (Syn.subst σ j) := by simp [checkCoordinate]

@[simp] theorem subst_checkData {k : ℕ} (σ : Fin n → PTm k) (E R C v : PTm n) :
    Syn.subst σ (checkData E R C v) =
      checkData (Syn.subst σ E) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ v) := by simp [checkData]

@[simp] theorem subst_test {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (test A R N v) = test (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by
  simp [test]

theorem check_body_at (E R C v j : PTm n) :
    Γ ⊢[PRAAx] inst2 checkBody j (checkData E R C v) ≐ checkCoordinate E R C v j := by
  have tail := snd_pair (Γ := Γ) E (pairT R (pairT C v))
  have last := (congrSnd tail).eqTrans (snd_pair R (pairT C v))
  simp only [checkBody, inst2, subst_checkCoordinate, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  simpa only [subst_checkCoordinate, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (checkCoordinate (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![fstT (checkData E R C v), fstT (sndT (checkData E R C v)),
        fstT (sndT (sndT (checkData E R C v))), sndT (sndT (sndT (checkData E R C v))), j])
      (σ' := ![E, R, C, v, j]) (fun i => by
        fin_cases i
        · exact fst_pair _ _
        · exact (congrFst tail).eqTrans (fst_pair _ _)
        · exact (congrFst last).eqTrans (fst_pair _ _)
        · exact (congrSnd last).eqTrans (snd_pair _ _)
        · exact .eqRefl _)

theorem test_cases (A R N v : PTm n) :
    Γ ⊢[PRAAx] (test A R N v ≐ zero) ⋎ (test A R N v ≐ one) := all_cases checkBody _ _

theorem test_coordinate (A R N v j : PTm n) (h : Γ ⊢[PRAAx] test A R N v ≐ one)
    (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] recode (entry v j) ≐ combinationAt (finalMatrix A R N) R (weights A R N v) j := by
  let E := finalMatrix A R N
  let C := weights A R N v
  let d := checkData E R C v
  have pass := all_elim checkBody (x := d) h hj
  have eval := check_body_at (Γ := Γ) E R C v j
  have bit : Γ ⊢[PRAAx] checkCoordinate E R C v j ≐ one := by
    refine .orE (eqb_cases (recode (entry v j)) (combinationAt E R C j)) ?_ Prf.hyp0
    exact .botE _ (.impE pass.wk (eval.wk.eqTrans Prf.hyp0))
  exact eq_of_eqb bit

theorem test_sound (A R N v : PTm n) (h : Γ ⊢[PRAAx] test A R N v ≐ one) :
    Γ ⊢[PRAAx] membership (finalMatrix A R N) R N (weights A R N v) v := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] test (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v) ≐ one := by
    simpa [Fm.shift, Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let E := finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N)
  let C := weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)
  let B := rowCombination E (Syn.shift R) (Syn.shift N) C
  have eq := test_coordinate (Γ := Δ) (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)
    (var 0) hs.wk Prf.hyp0
  have canon := combination_canonical (Γ := Δ) E (Syn.shift R) (Syn.shift N) C (var 0) Prf.hyp0
  have read := combination_lookup (Γ := Δ) E (Syn.shift R) (Syn.shift N) C (var 0) Prf.hyp0
  have related := equal_values_of_recode_equal (entry (Syn.shift v) (var 0)) (entry B (var 0))
    (eq.eqTrans ((recode_eq _ canon).eqTrans read).eqSymm)
  simpa only [Δ, B, C, E, Syn.shift, GaussianRationalRankNullityCriterion.subst_finalMatrix,
    GaussianRationalFullReducedSpan.subst_weights] using related

theorem test_complete (A R N C v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (h : Γ ⊢[PRAAx] membership (finalMatrix A R N) R N C v) :
    Γ ⊢[PRAAx] test A R N v ≐ one := by
  have hAs : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hA.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] membership (finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N))
      (Syn.shift R) (Syn.shift N) (Syn.shift C) (Syn.shift v) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  refine all_intro checkBody (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let E := finalMatrix (Syn.shift A) (Syn.shift R) (Syn.shift N)
  let W := weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift v)
  let d := checkData E (Syn.shift R) W (Syn.shift v)
  have eq := (value_at (Γ := Δ) E (Syn.shift R) (Syn.shift N) (Syn.shift C) (Syn.shift v) (var 0)
    hs.wk Prf.hyp0).eqTrans (candidate_coordinate (Syn.shift A) (Syn.shift R) (Syn.shift N)
      (Syn.shift C) (Syn.shift v) (var 0) hAs.wk hs.wk Prf.hyp0).eqSymm
  have mark : Δ ⊢[PRAAx] inst2 checkBody (var 0) d ≐ one :=
    (check_body_at E (Syn.shift R) W (Syn.shift v) (var 0)).eqTrans (eqb_of_eq eq)
  have nonzero : Δ ⊢[PRAAx] neg (inst2 checkBody (var 0) d ≐ zero) :=
    .impI (one_ne_zero _ (mark.wk.eqSymm.eqTrans Prf.hyp0))
  simpa only [Δ, d, E, W, Syn.shift, subst_checkData, GaussianRationalRankNullityCriterion.subst_finalMatrix,
    GaussianRationalFullReducedSpan.subst_weights] using nonzero

theorem actual_reduced_test_sound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (test (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      membership (finalMatrix (var 0) (var 1) (var 2)) (var 1) (var 2)
        (weights (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (test_sound _ _ _ _ Prf.hyp0))

theorem actual_reduced_test_complete_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (shape (var 0) (var 1) (var 2) ⟶
      membership (finalMatrix (var 0) (var 1) (var 2)) (var 1) (var 2) (var 3) (var 4) ⟶
      test (var 0) (var 1) (var 2) (var 4) ≐ one) :=
  closeUniv 5 (.impI (.impI (test_complete _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalReducedSpanMembership

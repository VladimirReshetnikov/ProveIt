import IPRADerivations.Analysis.Polynomials.Elimination.RowReduction.GaussianRationalRowElimination

/-!
# An actual finite vector from one free column

History entry zero denotes a skipped column; a positive entry is one
plus its pivot row. The selected free coordinate is one, other free
coordinates are zero, and a pivot coordinate is the negative entry in
the selected column of its own pivot row. All entries are actual
canonical Gaussian-rational codes. The basic constructor and its
nonzero witness need no presumed null-vector or elimination profile.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFreeColumnVector

open_ipra
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical canonical_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_eq recode_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReconstruction (spike spikeBody spikeData spikeSum spike_hit spike_miss)
open LeanProofs.IPRA.Analysis.GaussianRationalRowElimination (rowDot dotBody dotData)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pivotRow (H j : PTm n) : PTm n := monus (entry H j) one
def value (E H s j : PTm n) : PTm n := sel (eqb j s) qone
  (sel (eqb (entry H j) zero) qzero (qnegative (cell E (pivotRow H j) s)))
def data (E H s : PTm n) : PTm n := pairT E (pairT H s)
def body : PTm 2 := value (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def vector (E H N s : PTm n) : PTm n := sequence body N (data E H s)
def freeInput (H N s : PTm n) : Fm PTm n := lt s N ⋏ (entry H s ≐ zero)
def nonzeroVector (v N : PTm n) : Fm PTm n := .ex
  (lt (var 0) (Syn.shift N) ⋏ neg (recode (entry (Syn.shift v) (var 0)) ≐ qzero))

ipra_subst pivotRow
ipra_subst value [sel]
ipra_subst data
ipra_subst vector
ipra_subst freeInput
ipra_subst nonzeroVector [Syn.subst_shift, Syn.shift_subst]

theorem value_congr {E E' H H' s s' j j' : PTm n} (hE : Γ ⊢[PRAAx] E ≐ E')
    (hH : Γ ⊢[PRAAx] H ≐ H') (hs : Γ ⊢[PRAAx] s ≐ s') (hj : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] value E H s j ≐ value E' H' s' j' := by
  ipra_congr (value (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hE, hH, hs, hj]

theorem body_at (E H s j : PTm n) : Γ ⊢[PRAAx] inst2 body j (data E H s) ≐ value E H s j := by
  simp only [body,inst2,subst_value,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact value_congr (fst_pair _ _) (snd_pair _ _).fstE
    (snd_pair _ _).sndE (.eqRefl _)
theorem vector_length (E H N s : PTm n) : Γ ⊢[PRAAx] length (vector E H N s) ≐ N := sequence_length _ _ _
theorem vector_lookup (E H N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] entry (vector E H N s) j ≐ value E H s j :=
  (sequence_decode body (x := data E H s) hj).eqTrans (body_at E H s j)

theorem selected_value (E H s j : PTm n) (h : Γ ⊢[PRAAx] j ≐ s) : Γ ⊢[PRAAx] value E H s j ≐ qone :=
  sel_one (eqb_of_eq h)
theorem other_free_value (E H s j : PTm n) (hne : Γ ⊢[PRAAx] neg (j ≐ s))
    (hTag : Γ ⊢[PRAAx] entry H j ≐ zero) : Γ ⊢[PRAAx] value E H s j ≐ qzero :=
  (sel_zero (eqb_of_ne hne)).eqTrans (sel_one (eqb_of_eq hTag))
theorem pivot_value (E H s j : PTm n) (hne : Γ ⊢[PRAAx] neg (j ≐ s))
    (hTag : Γ ⊢[PRAAx] neg (entry H j ≐ zero)) : Γ ⊢[PRAAx]
    value E H s j ≐ qnegative (cell E (pivotRow H j) s) :=
  (sel_zero (eqb_of_ne hne)).eqTrans (sel_zero (eqb_of_ne hTag))
theorem value_canonical (E H s j : PTm n) : Γ ⊢[PRAAx] canonical (value E H s j) := by
  refine .orE (eq_or_ne j s) ?_ ?_
  · exact canonical_congr (selected_value _ _ _ _ Prf.hyp0) qone_canonical
  · refine .orE (eq_or_ne (entry H j) zero) ?_ ?_
    · exact canonical_congr (other_free_value _ _ _ _ Prf.hyp1 Prf.hyp0) qzero_canonical
    · exact canonical_congr (pivot_value _ _ _ _ Prf.hyp1 Prf.hyp0) (qnegative_canonical _)
theorem vector_canonical (E H N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] canonical (entry (vector E H N s) j) :=
  canonical_congr (vector_lookup _ _ _ _ _ hj) (value_canonical _ _ _ _)
theorem selected_entry (E H N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) :
    Γ ⊢[PRAAx] entry (vector E H N s) s ≐ qone :=
  (vector_lookup _ _ _ _ _ hs).eqTrans (selected_value _ _ _ _ (.eqRefl _))
theorem free_entry (E H N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hne : Γ ⊢[PRAAx] neg (j ≐ s)) (hTag : Γ ⊢[PRAAx] entry H j ≐ zero) :
    Γ ⊢[PRAAx] entry (vector E H N s) j ≐ qzero :=
  (vector_lookup _ _ _ _ _ hj).eqTrans (other_free_value _ _ _ _ hne hTag)
theorem pivot_entry (E H N s j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hne : Γ ⊢[PRAAx] neg (j ≐ s)) (hTag : Γ ⊢[PRAAx] neg (entry H j ≐ zero)) :
    Γ ⊢[PRAAx] entry (vector E H N s) j ≐ qnegative (cell E (pivotRow H j) s) :=
  (vector_lookup _ _ _ _ _ hj).eqTrans (pivot_value _ _ _ _ hne hTag)

theorem nonzero_entry (E H N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx]
    neg (recode (entry (vector E H N s) s) ≐ qzero) := by
  have e := (recode_congr (selected_entry E H N s hs)).eqTrans (recode_eq _ qone_canonical)
  exact .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero (e.wk.eqSymm.eqTrans Prf.hyp0))
theorem vector_nonzero (E H N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx]
    nonzeroVector (vector E H N s) N := by
  refine .exI s ?_
  simpa only [nonzeroVector,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,
    GaussianTranslatedNonconstant.subst_recode,Foundations.MasterCertificate.subst_entry,
    GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.andI hs (nonzero_entry E H N s hs)

/-! The following local profile consists only of individual tag/cell facts.
A genuine reduced-history profile can discharge it; no row-dot equation is
part of the profile. Other free columns need no matrix restriction. -/
def pivotProfile (E H N r p : PTm n) : Fm PTm n :=
  (lt p N ⋏ (entry H p ≐ succ r)) ⋏ ((recode (cell E r p) ≐ qone) ⋏ .all
    (lt (var 0) (Syn.shift N) ⟶ neg (var 0 ≐ Syn.shift p) ⟶
      neg (entry (Syn.shift H) (var 0) ≐ zero) ⟶ recode (cell (Syn.shift E) (Syn.shift r) (var 0)) ≐ qzero))
ipra_subst pivotProfile [Syn.subst_shift, Syn.shift_subst]

theorem profile_off (E H N r p j : PTm n) (h : Γ ⊢[PRAAx] pivotProfile E H N r p)
    (hj : Γ ⊢[PRAAx] lt j N) (hne : Γ ⊢[PRAAx] neg (j ≐ p))
    (hTag : Γ ⊢[PRAAx] neg (entry H j ≐ zero)) : Γ ⊢[PRAAx] recode (cell E r j) ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ neg (j ≐ p) ⟶ neg (entry H j ≐ zero) ⟶ recode (cell E r j) ≐ qzero := by
    simpa [pivotProfile] using (Prf.andE₂ (Prf.andE₂ h)).allE j
  exact .impE (.impE (.impE rule hj) hne) hTag
theorem pivot_row_at (H p r : PTm n) (h : Γ ⊢[PRAAx] entry H p ≐ succ r) :
    Γ ⊢[PRAAx] pivotRow H p ≐ r :=
  (congrMonus h (.eqRefl one)).eqTrans ((succ_monus_succ r zero).eqTrans (monus_zero r))
theorem pivot_ne_free (H r p s : PTm n) (hp : Γ ⊢[PRAAx] entry H p ≐ succ r)
    (hs : Γ ⊢[PRAAx] entry H s ≐ zero) : Γ ⊢[PRAAx] neg (p ≐ s) :=
  .impI (succ_ne_zero (hp.wk.eqSymm.eqTrans ((entry_congr (.eqRefl H) Prf.hyp0).eqTrans hs.wk)))

def twoData (s p a : PTm n) : PTm n := pairT s (pairT p a)
def leftBody : PTm 2 := spike (fstT (var 1)) (recode (sndT (sndT (var 1)))) (var 0)
def rightBody : PTm 2 := spike (fstT (sndT (var 1))) (qnegative (sndT (sndT (var 1)))) (var 0)
def twoBody : PTm 2 := GaussianRationalFiniteSum.addBody leftBody rightBody
ipra_subst twoData
theorem left_body_at (s p a j : PTm n) : Γ ⊢[PRAAx]
    inst2 leftBody j (twoData s p a) ≐ spike s (recode a) j := by
  simp only [leftBody,inst2,GaussianRationalMonicReconstruction.subst_spike,
    GaussianTranslatedNonconstant.subst_recode,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalMonicReconstruction.spike_congr (fst_pair _ _)
    (recode_congr (snd_pair _ _).sndE) (.eqRefl _)
theorem right_body_at (s p a j : PTm n) : Γ ⊢[PRAAx]
    inst2 rightBody j (twoData s p a) ≐ spike p (qnegative a) j := by
  simp only [rightBody,inst2,GaussianRationalMonicReconstruction.subst_spike,
    GaussianRationalMetric.subst_qnegative,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact GaussianRationalMonicReconstruction.spike_congr (snd_pair _ _).fstE
    (GaussianInverseBinomialRows.negative_congr (snd_pair _ _).sndE) (.eqRefl _)
theorem two_body_at (s p a j : PTm n) : Γ ⊢[PRAAx]
    inst2 twoBody j (twoData s p a) ≐ qadd (spike s (recode a) j) (spike p (qnegative a) j) := by
  simpa only [twoBody,GaussianRationalFiniteSum.inst2_addBody] using
    qadd_congr (left_body_at (Γ := Γ) s p a j) (right_body_at s p a j)

theorem left_sum (N s p a : PTm n) : Γ ⊢[PRAAx] sum leftBody N (twoData s p a) ≐ spikeSum s (recode a) N := by
  refine GaussianRationalFiniteSum.sum_congr_bounded leftBody spikeBody N (twoData s p a) (spikeData s (recode a)) ?_
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_twoData,GaussianRationalMonicReconstruction.subst_spikeData,
    GaussianTranslatedNonconstant.subst_recode] using
    (left_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift s) (Syn.shift p) (Syn.shift a) (var 0)).eqTrans
      (GaussianRationalMonicReconstruction.spike_body_at (Syn.shift s) (recode (Syn.shift a)) (var 0)).eqSymm
theorem right_sum (N s p a : PTm n) : Γ ⊢[PRAAx] sum rightBody N (twoData s p a) ≐ spikeSum p (qnegative a) N := by
  refine GaussianRationalFiniteSum.sum_congr_bounded rightBody spikeBody N (twoData s p a) (spikeData p (qnegative a)) ?_
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_twoData,GaussianRationalMonicReconstruction.subst_spikeData,
    GaussianRationalMetric.subst_qnegative] using
    (right_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift s) (Syn.shift p) (Syn.shift a) (var 0)).eqTrans
      (GaussianRationalMonicReconstruction.spike_body_at (Syn.shift p) (qnegative (Syn.shift a)) (var 0)).eqSymm
theorem two_sum_zero (N s p a : PTm n) (hs : Γ ⊢[PRAAx] lt s N) (hp : Γ ⊢[PRAAx] lt p N) :
    Γ ⊢[PRAAx] sum twoBody N (twoData s p a) ≐ qzero :=
  (GaussianRationalFiniteSum.sum_add leftBody rightBody N (twoData s p a)).eqTrans
    ((qadd_congr ((left_sum N s p a).eqTrans ((GaussianRationalMonicReconstruction.spike_sum _ _ _
        (GaussianTranslatedNonconstant.recode_canonical a)).eqTrans (GaussianRationalMonicReconstruction.active_on _ _ _ hs)))
      ((right_sum N s p a).eqTrans ((GaussianRationalMonicReconstruction.spike_sum _ _ _ (qnegative_canonical a)).eqTrans
        (GaussianRationalMonicReconstruction.active_on _ _ _ hp)))).eqTrans
          ((GaussianRationalSyntheticCoefficientValues.qadd_recode_left _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self a)))

theorem dot_term_two_spikes (E H N s r p j : PTm n) (hF : Γ ⊢[PRAAx] freeInput H N s)
    (hP : Γ ⊢[PRAAx] pivotProfile E H N r p) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    qmul (cell E r j) (entry (vector E H N s) j) ≐
      qadd (spike s (recode (cell E r s)) j) (spike p (qnegative (cell E r s)) j) := by
  have tag := Prf.andE₂ (Prf.andE₁ hP)
  have distinct := pivot_ne_free H r p s tag (.andE₂ hF)
  refine .orE (eq_or_ne j s) ?_ ?_
  · have other : (j ≐ s) :: Γ ⊢[PRAAx] neg (j ≐ p) :=
      .impI (.impE distinct.wk.wk (Prf.hyp0.eqSymm.eqTrans Prf.hyp1))
    have cellEq : (j ≐ s) :: Γ ⊢[PRAAx] cell E r j ≐ cell E r s :=
      entry_congr (entry_congr (.eqRefl E) (.eqRefl r)) Prf.hyp0
    have left := (qmul_congr cellEq ((vector_lookup E H N s j hj.wk).eqTrans (selected_value E H s j Prf.hyp0))).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianRationalFiniteProduct.raw_one_left _))
    have right : (j ≐ s) :: Γ ⊢[PRAAx]
        qadd (spike s (recode (cell E r s)) j) (spike p (qnegative (cell E r s)) j) ≐ recode (cell E r s) :=
      (qadd_congr (spike_hit _ _ _ Prf.hyp0) (spike_miss _ _ _ other)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (GaussianTranslatedNonconstant.recode_canonical _))
    exact left.eqTrans right.eqSymm
  · refine .orE (eq_or_ne j p) ?_ ?_
    · have jNotS : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx] neg (j ≐ s) := Prf.hyp1
      have tagNonzero : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx] neg (entry H j ≐ zero) :=
        .impI (succ_ne_zero (tag.wk.wk.wk.eqSymm.eqTrans
          ((entry_congr (.eqRefl H) Prf.hyp1).eqSymm.eqTrans Prf.hyp0)))
      have cellEq : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx] recode (cell E r j) ≐ qone :=
        (recode_congr (entry_congr (entry_congr (.eqRefl E) (.eqRefl r)) Prf.hyp0)).eqTrans (.andE₁ (.andE₂ hP.wk.wk))
      have rowEq : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx] pivotRow H j ≐ r :=
        pivot_row_at H j r ((entry_congr (.eqRefl H) Prf.hyp0).eqTrans tag.wk.wk)
      have lambdaEq : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx]
          entry (vector E H N s) j ≐ qnegative (cell E r s) :=
        (pivot_entry E H N s j hj.wk.wk jNotS tagNonzero).eqTrans
        (GaussianInverseBinomialRows.negative_congr (entry_congr (entry_congr (.eqRefl E) rowEq) (.eqRefl s)))
      have left := (GaussianRationalSyntheticCoefficientValues.qmul_recode_left
          (cell E r j) (entry (vector E H N s) j)).eqSymm.eqTrans
        ((qmul_congr cellEq lambdaEq).eqTrans
          ((GaussianRationalFiniteProduct.raw_one_left _).eqTrans (recode_eq _ (qnegative_canonical _))))
      have right : (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx]
          qadd (spike s (recode (cell E r s)) j) (spike p (qnegative (cell E r s)) j) ≐ qnegative (cell E r s) :=
        (qadd_congr (spike_miss _ _ _ jNotS) (spike_hit _ _ _ Prf.hyp0)).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ (qnegative_canonical _))
      exact left.eqTrans right.eqSymm
    · have left : neg (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx]
          qmul (cell E r j) (entry (vector E H N s) j) ≐ qzero := by
        refine .orE (eq_or_ne (entry H j) zero) ?_ ?_
        · exact (qmul_congr (.eqRefl _) (free_entry _ _ _ _ _ hj.wk.wk.wk Prf.hyp1.wk Prf.hyp0)).eqTrans
            (GaussianRationalSyntheticDivision.qmul_zero_right _)
        · exact (GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _).eqSymm.eqTrans
            ((qmul_congr (profile_off _ _ _ _ _ _ hP.wk.wk.wk hj.wk.wk.wk Prf.hyp1 Prf.hyp0) (.eqRefl _)).eqTrans
              (GaussianRationalSyntheticDivision.qmul_zero_left _))
      have right : neg (j ≐ p) :: neg (j ≐ s) :: Γ ⊢[PRAAx]
          qadd (spike s (recode (cell E r s)) j) (spike p (qnegative (cell E r s)) j) ≐ qzero :=
        (qadd_congr (spike_miss _ _ _ Prf.hyp1) (spike_miss _ _ _ Prf.hyp0)).eqTrans
          GaussianRationalMonicReconstruction.zero_add_zero
      exact left.eqTrans right.eqSymm

theorem pivot_row_dot_zero (E H N s r p : PTm n) (hF : Γ ⊢[PRAAx] freeInput H N s)
    (hP : Γ ⊢[PRAAx] pivotProfile E H N r p) : Γ ⊢[PRAAx] rowDot E N (vector E H N s) r ≐ qzero := by
  have fs : Γ.map Fm.shift ⊢[PRAAx] freeInput (Syn.shift H) (Syn.shift N) (Syn.shift s) := by
    simpa only [Fm.shift,subst_freeInput,Syn.shift] using hF.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] pivotProfile (Syn.shift E) (Syn.shift H) (Syn.shift N) (Syn.shift r) (Syn.shift p) := by
    simpa only [Fm.shift,subst_pivotProfile,Syn.shift] using hP.shift
  have same : Γ ⊢[PRAAx] rowDot E N (vector E H N s) r ≐ sum twoBody N (twoData s p (cell E r s)) := by
    refine GaussianRationalFiniteSum.sum_congr_bounded dotBody twoBody N (dotData E (vector E H N s) r) (twoData s p (cell E r s)) ?_
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,subst_vector,subst_twoData,
      GaussianPolynomialDeterminantTerms.subst_cell] using
      (GaussianRationalRowElimination.dot_body_at (Γ := Δ) (Syn.shift E)
        (vector (Syn.shift E) (Syn.shift H) (Syn.shift N) (Syn.shift s)) (Syn.shift r) (var 0)).eqTrans
        ((dot_term_two_spikes _ _ _ _ _ _ _ fs.wk ps.wk Prf.hyp0).eqTrans
          (two_body_at (Syn.shift s) (Syn.shift p) (cell (Syn.shift E) (Syn.shift r) (Syn.shift s)) (var 0)).eqSymm)
  exact same.eqTrans (two_sum_zero _ _ _ _ (.andE₁ hF) (.andE₁ (.andE₁ hP)))

/-- Field zero is tested after genuine canonical recoding, not by raw-code equality. -/
def fieldZeroRow (E N r : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ recode (cell (Syn.shift E) (Syn.shift r) (var 0)) ≐ qzero)
ipra_subst fieldZeroRow [Syn.subst_shift, Syn.shift_subst]
theorem field_zero_at (E N r j : PTm n) (h : Γ ⊢[PRAAx] fieldZeroRow E N r)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] recode (cell E r j) ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt j N ⟶ recode (cell E r j) ≐ qzero := by simpa [fieldZeroRow] using h.allE j
  exact .impE rule hj
theorem field_zero_row_dot (E N v r : PTm n) (h : Γ ⊢[PRAAx] fieldZeroRow E N r) :
    Γ ⊢[PRAAx] rowDot E N v r ≐ qzero := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] fieldZeroRow (Syn.shift E) (Syn.shift N) (Syn.shift r) := by
    simpa only [Fm.shift,subst_fieldZeroRow,Syn.shift] using h.shift
  refine GaussianRationalMatrixFiniteSums.sum_zero_of_terms dotBody N (dotData E v r) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have term := (GaussianRationalRowElimination.dot_body_at (Γ := Δ) (Syn.shift E) (Syn.shift v) (Syn.shift r) (var 0)).eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _).eqSymm.eqTrans
      ((qmul_congr (field_zero_at _ _ _ _ hs.wk Prf.hyp0) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_left _)))
  simpa only [Δ,Syn.shift,GaussianRationalRowElimination.subst_dotData,GaussianRationalHorner.subst_qzero] using term

def outputF : PR 4 := PTm.toPR (vector (var 0) (var 1) (var 2) (var 3))
def run (E H N s : PTm n) : PTm n := app outputF ![E,H,N,s]
ipra_subst run
theorem program_at (E H N s : PTm n) : Γ ⊢[PRAAx] run E H N s ≐ vector E H N s := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (vector (var 0) (var 1) (var 2) (var 3) : PTm 4) ![E,H,N,s]
theorem returned_length (E H N s : PTm n) : Γ ⊢[PRAAx] length (run E H N s) ≐ N :=
  (congrFst (program_at _ _ _ _)).eqTrans (vector_length _ _ _ _)
theorem returned_selected (E H N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx]
    entry (run E H N s) s ≐ qone :=
  (entry_congr (program_at _ _ _ _) (.eqRefl _)).eqTrans (selected_entry E H N s hs)

theorem returned_nonzero (E H N s : PTm n) (hs : Γ ⊢[PRAAx] lt s N) : Γ ⊢[PRAAx]
    nonzeroVector (run E H N s) N := by
  have e := (recode_congr (returned_selected E H N s hs)).eqTrans (recode_eq _ qone_canonical)
  have ne : Γ ⊢[PRAAx] neg (recode (entry (run E H N s) s) ≐ qzero) :=
    .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero (e.wk.eqSymm.eqTrans Prf.hyp0))
  refine .exI s ?_
  simpa only [nonzeroVector,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,
    GaussianTranslatedNonconstant.subst_recode,Foundations.MasterCertificate.subst_entry,
    GaussianRationalHorner.subst_qzero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hs ne
theorem returned_pivot_null (E H N s r p : PTm n) (hF : Γ ⊢[PRAAx] freeInput H N s)
    (hP : Γ ⊢[PRAAx] pivotProfile E H N r p) : Γ ⊢[PRAAx] rowDot E N (run E H N s) r ≐ qzero :=
  (GaussianRationalRowElimination.row_dot_congr (.eqRefl E) (.eqRefl N) (program_at E H N s) (.eqRefl r)).eqTrans
    (pivot_row_dot_zero E H N s r p hF hP)

theorem actual_vector_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (vector (var 0) (var 1) (var 2) (var 3)) ≐ var 2) := closeUniv 4 (vector_length _ _ _ _)
theorem actual_vector_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ entry (vector (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ value (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (vector_lookup _ _ _ _ _ Prf.hyp0))
theorem actual_vector_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ canonical (entry (vector (var 0) (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (vector_canonical _ _ _ _ _ Prf.hyp0))
theorem actual_selected_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ entry (vector (var 0) (var 1) (var 2) (var 3)) (var 3) ≐ qone) :=
  closeUniv 4 (.impI (selected_entry _ _ _ _ Prf.hyp0))
theorem actual_other_free_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ neg (var 4 ≐ var 3) ⟶ entry (var 1) (var 4) ≐ zero ⟶
      entry (vector (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (free_entry _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_pivot_coordinate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 2) ⟶ neg (var 4 ≐ var 3) ⟶ neg (entry (var 1) (var 4) ≐ zero) ⟶
      entry (vector (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qnegative (cell (var 0) (pivotRow (var 1) (var 4)) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (pivot_entry _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_nonzero_vector_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ nonzeroVector (vector (var 0) (var 1) (var 2) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (vector_nonzero _ _ _ _ Prf.hyp0))
theorem actual_pivot_row_null_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (freeInput (var 1) (var 2) (var 3) ⟶ pivotProfile (var 0) (var 1) (var 2) (var 4) (var 5) ⟶
      rowDot (var 0) (var 2) (vector (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (pivot_row_dot_zero _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_field_zero_row_null_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (fieldZeroRow (var 0) (var 1) (var 3) ⟶ rowDot (var 0) (var 1) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (field_zero_row_dot _ _ _ _ Prf.hyp0))
theorem actual_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ vector (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 2) ⟶ nonzeroVector (run (var 0) (var 1) (var 2) (var 3)) (var 2)) :=
  closeUniv 4 (.impI (returned_nonzero _ _ _ _ Prf.hyp0))
theorem actual_returned_pivot_null_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (freeInput (var 1) (var 2) (var 3) ⟶ pivotProfile (var 0) (var 1) (var 2) (var 4) (var 5) ⟶
      rowDot (var 0) (var 2) (run (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 6 (.impI (.impI (returned_pivot_null _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalFreeColumnVector

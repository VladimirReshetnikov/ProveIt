import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalLagrangeCardinals
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFubini
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows

/-!
# Actual full right inverse of the completed numerical fiber power table

The actual cardinal coefficients form N. A single actual finite sum NC
supplies the whole upper-right block -NC; the lower rows retain their
original standard coordinate indices. Every table dimension and original
ordinate code is numerical. The full right-inverse law is derived from
cardinal evaluation and genuine Gaussian finite-sum exchange. Determinant
laws and norm multiplicity are separate source obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiberRightInverse

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalLagrangeCardinals (inverseCoefficient)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (table scalarShape delta)
open LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums (scalarBody scalarData scalarDot matrixProduct deltaBody deltaSum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseBody : PTm 3 := inverseCoefficient (var 2) (var 0) (var 1)
def N (R : PTm n) : PTm n := table inverseBody (length R) (length R) R
def crossBody : PTm 3 := power (entry (fstT (var 2)) (var 0)) (sndT (var 2)+var 1)
def C (R m : PTm n) : PTm n := table crossBody (length R) (monus m (length R)) (pairT R (length R))
def data (R r j : PTm n) : PTm n := pairT R (pairT r j)
def ncTerm (R r j s : PTm n) : PTm n := qmul (inverseCoefficient R r s) (power (entry R s) j)
def ncBody : PTm 2 := ncTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def NC (R r j : PTm n) : PTm n := GaussianRationalFiniteSum.sum ncBody (length R) (data R r j)
def upperEntry (R r j : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus (length R) j))
  (qnegative (NC R r j)) (inverseCoefficient R r j)
def zEntry (R r j : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus (length R) r))
  (delta r j) (upperEntry R r j)
def zBody : PTm 3 := zEntry (var 2) (var 0) (var 1)
def Z (R m : PTm n) : PTm n := table zBody m m R

ipra_subst N
ipra_subst C
ipra_subst data
ipra_subst ncTerm
ipra_subst NC
ipra_subst upperEntry
ipra_subst zEntry
ipra_subst Z

theorem N_lookup (R r s : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    cell (N R) r s ≐ inverseCoefficient R r s := by
  simpa [N,inverseBody] using GaussianRationalFiberVandermonde.table_lookup inverseBody (length R) (length R) R r s hr hs
theorem inverse_coefficient_canonical (R r s : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R))
    (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx] canonical (inverseCoefficient R r s) :=
  canonical_coefficient_at _ _ (GaussianRationalLagrangeCardinals.cardinal_canonical _ _)
    (lt_congr (.eqRefl _) (GaussianRationalLagrangeCardinals.cardinal_length _ _ hs).eqSymm
      (GaussianRationalLagrangeCardinals.reverse_position_bound _ _ hr))
theorem N_canonical (R r s : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    canonical (cell (N R) r s) := GaussianRationalHorner.canonical_congr (N_lookup _ _ _ hr hs) (inverse_coefficient_canonical _ _ _ hr hs)
theorem N_shape (R : PTm n) : Γ ⊢[PRAAx] scalarShape (N R) (length R) (length R) := by
  refine .andI (GaussianRationalFiberVandermonde.table_length _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_N,N,GaussianRationalFiberVandermonde.subst_table,subst_length] using
    GaussianRationalFiberVandermonde.table_row_length inverseBody (length (Syn.shift R)) (length (Syn.shift R)) (Syn.shift R) (var 0) Prf.hyp0
theorem C_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (monus m (length R))) : Γ ⊢[PRAAx]
    cell (C R m) r j ≐ power (entry R r) (length R+j) := by
  have e : Γ ⊢[PRAAx] cell (C R m) r j ≐ power (entry (fstT (pairT R (length R))) r) (sndT (pairT R (length R))+j) := by
    simpa [C,crossBody] using GaussianRationalFiberVandermonde.table_lookup crossBody (length R) (monus m (length R)) (pairT R (length R)) r j hr hj
  exact e.eqTrans (congrAp2 GaussianRationalReciprocal.powerF (congrAdd (snd_pair _ _) (.eqRefl _)) (entry_congr (fst_pair _ _) (.eqRefl _)))
theorem C_shape (R m : PTm n) : Γ ⊢[PRAAx] scalarShape (C R m) (length R) (monus m (length R)) := by
  refine .andI (GaussianRationalFiberVandermonde.table_length _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_C,C,GaussianRationalFiberVandermonde.subst_table,subst_length,subst_pairT,PTm.subst_monus] using
    GaussianRationalFiberVandermonde.table_row_length crossBody (length (Syn.shift R)) (monus (Syn.shift m) (length (Syn.shift R)))
      (pairT (Syn.shift R) (length (Syn.shift R))) (var 0) Prf.hyp0
theorem C_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (monus m (length R))) : Γ ⊢[PRAAx]
    canonical (cell (C R m) r j) := GaussianRationalHorner.canonical_congr (C_lookup _ _ _ _ hr hj) (power_canonical _ _)

theorem nc_body_at (R r j s : PTm n) : Γ ⊢[PRAAx] inst2 ncBody s (data R r j) ≐ ncTerm R r j s := by
  simp only [ncBody,inst2,subst_ncTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) R (pairT r j)
  exact qmul_congr (GaussianRationalLagrangeCardinals.inverse_coefficient_congr (fst_pair _ _) e.fstE (.eqRefl _))
    (congrAp2 GaussianRationalReciprocal.powerF e.sndE (entry_congr (fst_pair _ _) (.eqRefl _)))
theorem NC_canonical (R r j : PTm n) : Γ ⊢[PRAAx] canonical (NC R r j) := GaussianRationalFiniteSum.sum_canonical _ _ _
theorem z_upper_left (R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    zEntry R r j ≐ inverseCoefficient R r j :=
  (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)).eqTrans
    (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hj))
theorem z_upper_right (R r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    zEntry R r j ≐ qnegative (NC R r j) :=
  (RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hr)).eqTrans
    (RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hj))
theorem z_lower (R r j : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    zEntry R r j ≐ delta r j := RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le hr)
theorem z_entry_canonical (R r j : PTm n) : Γ ⊢[PRAAx] canonical (zEntry R r j) := by
  refine .orE (lt_or_le r (length R)) ?_ ?_
  · refine .orE (lt_or_le j (length R)) ?_ ?_
    · exact GaussianRationalHorner.canonical_congr (z_upper_left _ _ _ Prf.hyp1 Prf.hyp0) (inverse_coefficient_canonical _ _ _ Prf.hyp1 Prf.hyp0)
    · exact GaussianRationalHorner.canonical_congr (z_upper_right _ _ _ Prf.hyp1 Prf.hyp0) (qnegative_canonical _)
  · exact GaussianRationalHorner.canonical_congr (z_lower _ _ _ Prf.hyp0) (GaussianRationalFiberVandermonde.delta_canonical _ _)
theorem Z_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (Z R m) r j ≐ zEntry R r j := by simpa [Z,zBody] using GaussianRationalFiberVandermonde.table_lookup zBody m m R r j hr hj
theorem Z_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (Z R m) r j) := GaussianRationalHorner.canonical_congr (Z_lookup _ _ _ _ hr hj) (z_entry_canonical _ _ _)
theorem Z_shape (R m : PTm n) : Γ ⊢[PRAAx] scalarShape (Z R m) m m := by
  refine .andI (GaussianRationalFiberVandermonde.table_length _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_Z,Z,GaussianRationalFiberVandermonde.subst_table] using
    GaussianRationalFiberVandermonde.table_row_length zBody (Syn.shift m) (Syn.shift m) (Syn.shift R) (var 0) Prf.hyp0

/-- One shared body, with numerical k then s, for the actual Fubini step. -/
def tripleTerm (R r j k s : PTm n) : PTm n := qmul
  (qmul (power (entry R r) k) (inverseCoefficient R k s)) (power (entry R s) j)
def tripleBody : PTm 3 := tripleTerm (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
ipra_subst tripleTerm
theorem triple_body_at (R r j k s : PTm n) : Γ ⊢[PRAAx]
    inst3 tripleBody k s (data R r j) ≐ tripleTerm R r j k s := by
  simp only [tripleBody,inst3,subst_tripleTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  have e := snd_pair (Γ := Γ) R (pairT r j)
  exact qmul_congr (qmul_congr (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (entry_congr (fst_pair _ _) e.fstE))
      (GaussianRationalLagrangeCardinals.inverse_coefficient_congr (fst_pair _ _) (.eqRefl _) (.eqRefl _)))
    (congrAp2 GaussianRationalReciprocal.powerF e.sndE (entry_congr (fst_pair _ _) (.eqRefl _)))


theorem triple_row (R r j k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row tripleBody k (length R) (data R r j) ≐ qmul (power (entry R r) k) (NC R k j) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.rowBody tripleBody)
      (GaussianRationalFiniteSum.multiplyBody ncBody) (length R) (pairT k (data R r j))
      (pairT (power (entry R r) k) (data R k j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (GaussianRationalFubini.rowBody tripleBody) (var 0) (pairT (Syn.shift k) (data (Syn.shift R) (Syn.shift r) (Syn.shift j))) ≐
        inst2 (GaussianRationalFiniteSum.multiplyBody ncBody) (var 0) (pairT (power (entry (Syn.shift R) (Syn.shift r)) (Syn.shift k)) (data (Syn.shift R) (Syn.shift k) (Syn.shift j))) :=
      (GaussianRationalFubini.row_entry tripleBody _ _ _).eqTrans ((triple_body_at _ _ _ _ _).eqTrans
        ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
          ((GaussianRationalFiniteSum.multiply_body_at ncBody _ _ _).eqTrans (qmul_congr (.eqRefl _) (nc_body_at _ _ _ _))).eqSymm))
    simpa only [Δ,Syn.shift,subst_data,subst_entry,GaussianRationalReciprocal.subst_power,subst_pairT] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalFiniteSum.sum_multiply _ _ _ _)
theorem triple_column (R r j s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column tripleBody s (length R) (data R r j) ≐
      qmul (GaussianRationalLagrangeCardinals.dot R r s) (power (entry R s) j) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.columnBody tripleBody)
      (GaussianRationalFiniteSum.multiplyBody GaussianRationalLagrangeCardinals.evaluationBody) (length R) (pairT s (data R r j))
      (pairT (power (entry R s) j) (GaussianRationalLagrangeCardinals.evaluationData R s (entry R r))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (GaussianRationalFubini.columnBody tripleBody) (var 0) (pairT (Syn.shift s) (data (Syn.shift R) (Syn.shift r) (Syn.shift j))) ≐
        inst2 (GaussianRationalFiniteSum.multiplyBody GaussianRationalLagrangeCardinals.evaluationBody) (var 0)
          (pairT (power (entry (Syn.shift R) (Syn.shift s)) (Syn.shift j))
            (GaussianRationalLagrangeCardinals.evaluationData (Syn.shift R) (Syn.shift s) (entry (Syn.shift R) (Syn.shift r)))) :=
      (GaussianRationalFubini.column_entry tripleBody _ _ _).eqTrans ((triple_body_at _ _ _ _ _).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          ((GaussianRationalFiniteSum.multiply_body_at GaussianRationalLagrangeCardinals.evaluationBody _ _ _).eqTrans
            (qmul_congr (.eqRefl _) (GaussianRationalLagrangeCardinals.evaluation_body_at _ _ _ _))).eqSymm))
    simpa only [Δ,Syn.shift,subst_data,subst_entry,GaussianRationalReciprocal.subst_power,subst_pairT,
      GaussianRationalLagrangeCardinals.subst_evaluationData] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply _ _ _ _).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _))
theorem triple_column_cardinal (R r j s : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hs : Γ ⊢[PRAAx] lt s (length R)) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column tripleBody s (length R) (data R r j) ≐ qmul (delta r s) (power (entry R s) j) :=
  (triple_column _ _ _ _).eqTrans (qmul_congr (GaussianRationalLagrangeCardinals.cardinal_dot _ _ _ h hr hs) (.eqRefl _))

theorem multiply_negative_right (a b : PTm n) : Γ ⊢[PRAAx]
    qmul a (qnegative b) ≐ qnegative (qmul a b) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianInverseBinomialRows.negative_product _ _).eqSymm.eqTrans
      (GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)))
theorem natural_neq_symm (a b : PTm n) (h : Γ ⊢[PRAAx] neg (a ≐ b)) : Γ ⊢[PRAAx] neg (b ≐ a) :=
  .impI (.impE h.wk Prf.hyp0.eqSymm)
theorem delta_shift (t j i : PTm n) (hj : Γ ⊢[PRAAx] le t j) : Γ ⊢[PRAAx]
    delta (t+i) j ≐ delta (monus j t) i := by
  refine .orE (eq_or_ne i (monus j t)) ?_ ?_
  · have e : (i ≐ monus j t) :: Γ ⊢[PRAAx] t+i ≐ j :=
      (congrAdd (.eqRefl _) Prf.hyp0).eqTrans (eq_add_of_le hj.wk).eqSymm
    exact (GaussianRationalLagrangeCardinals.delta_equal _ _ e).eqTrans
      (GaussianRationalLagrangeCardinals.delta_equal _ _ Prf.hyp0.eqSymm).eqSymm
  · have ne : neg (i ≐ monus j t) :: Γ ⊢[PRAAx] neg (t+i ≐ j) :=
      .impI (.impE Prf.hyp1 (add_left_cancel (Prf.hyp0.eqTrans (eq_add_of_le hj.wk.wk))))
    exact (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne).eqTrans
      (GaussianRationalLagrangeCardinals.delta_unequal _ _ (natural_neq_symm _ _ Prf.hyp0)).eqSymm
theorem offset_bound (m t i : PTm n) (ht : Γ ⊢[PRAAx] le t m) (hi : Γ ⊢[PRAAx] lt i (monus m t)) : Γ ⊢[PRAAx]
    lt (t+i) m :=
  le_congr (by ipra_ring) ((add_comm _ _).eqTrans (eq_add_of_le ht).eqSymm) (add_le_add_right t hi)
theorem tail_index_bound (m t j : PTm n) (htj : Γ ⊢[PRAAx] le t j) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    lt (monus j t) (monus m t) := by
  have e : Γ ⊢[PRAAx] m ≐ t+(succ (monus j t)+monus m (succ j)) :=
    (eq_add_of_le hj).eqTrans ((congrAdd (congrSucc (eq_add_of_le htj)) (.eqRefl _)).eqTrans (by ipra_ring))
  exact le_of_eq_add (d := monus m (succ j)) ((congrMonus e (.eqRefl _)).eqTrans (add_monus' _ _))


def powerData (R j : PTm n) : PTm n := pairT R j
def powerBody : PTm 2 := power (entry (fstT (var 1)) (var 0)) (sndT (var 1))
def positiveTerm (R r j k : PTm n) : PTm n := qmul (power (entry R r) k) (NC R k j)
def positiveBody : PTm 2 := positiveTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def shiftPowerTerm (R r t i : PTm n) : PTm n := power (entry R r) (t+i)
def shiftPowerBody : PTm 2 := shiftPowerTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def zColumnBody : PTm 2 := cell (Z (fstT (var 1)) (fstT (sndT (var 1)))) (var 0) (sndT (sndT (var 1)))
ipra_subst powerData
ipra_subst positiveTerm
ipra_subst shiftPowerTerm
theorem NC_congr {R S r r' j j' : PTm n} (hR : Γ ⊢[PRAAx] R ≐ S) (hr : Γ ⊢[PRAAx] r ≐ r') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    NC R r j ≐ NC S r' j' := by
  ipra_congr (NC (var 0) (var 1) (var 2) : PTm 3) with [hR, hr, hj]
theorem power_body_at (R j i : PTm n) : Γ ⊢[PRAAx] inst2 powerBody i (powerData R j) ≐ power (entry R i) j := by
  simp only [powerBody,inst2,GaussianRationalReciprocal.subst_power,subst_entry,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp2 GaussianRationalReciprocal.powerF (snd_pair _ _) (entry_congr (fst_pair _ _) (.eqRefl _))
theorem positive_body_at (R r j k : PTm n) : Γ ⊢[PRAAx] inst2 positiveBody k (data R r j) ≐ positiveTerm R r j k := by
  simp only [positiveBody,inst2,subst_positiveTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) R (pairT r j)
  exact qmul_congr (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (entry_congr (fst_pair _ _) e.fstE))
    (NC_congr (fst_pair _ _) (.eqRefl _) e.sndE)
theorem shift_power_body_at (R r t i : PTm n) : Γ ⊢[PRAAx] inst2 shiftPowerBody i (data R r t) ≐ power (entry R r) (t+i) := by
  simp only [shiftPowerBody,inst2,subst_shiftPowerTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) R (pairT r t)
  exact congrAp2 GaussianRationalReciprocal.powerF (congrAdd e.sndE (.eqRefl _))
    (entry_congr (fst_pair _ _) e.fstE)
theorem z_column_body_at (R m j k : PTm n) : Γ ⊢[PRAAx] inst2 zColumnBody k (data R m j) ≐ cell (Z R m) k j := by
  simp only [zColumnBody,inst2,GaussianPolynomialDeterminantTerms.subst_cell,subst_Z,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have e := snd_pair (Γ := Γ) R (pairT m j)
  apply entry_congr
  · apply entry_congr
    · ipra_congr (Z (var 0) (var 1) : PTm 2) with
        [(show _ ⊢[PRAAx] fstT (data R m j) ≐ R from fst_pair _ _),
          (show _ ⊢[PRAAx] fstT (sndT (data R m j)) ≐ m from e.fstE)]
    · exact .eqRefl _
  · exact e.sndE

theorem positive_sum_as_rows (R r j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum positiveBody (length R) (data R r j) ≐
      GaussianRationalFubini.rowFirst tripleBody (length R) (length R) (data R r j) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] inst2 positiveBody (var 0) (data (Syn.shift R) (Syn.shift r) (Syn.shift j)) ≐
      inst2 (GaussianRationalFubini.rowSumBody tripleBody) (var 0) (pairT (length (Syn.shift R)) (data (Syn.shift R) (Syn.shift r) (Syn.shift j))) :=
    (positive_body_at _ _ _ _).eqTrans ((triple_row _ _ _ _).eqSymm.eqTrans (GaussianRationalFubini.row_sum_at tripleBody _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,subst_data,subst_length,subst_pairT] using e


theorem triple_total (R r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    GaussianRationalFubini.rowFirst tripleBody (length R) (length R) (data R r j) ≐ power (entry R r) j := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (Syn.shift R) := by simpa only [Fm.shift,GaussianRationalFiniteRoots.subst_distinct,Syn.shift] using h.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (GaussianRationalFubini.columnSumBody tripleBody) (GaussianRationalMatrixFiniteSums.deltaBody powerBody) (length R)
      (pairT (length R) (data R r j)) (pairT r (powerData R j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (GaussianRationalFubini.columnSumBody tripleBody) (var 0) (pairT (length (Syn.shift R)) (data (Syn.shift R) (Syn.shift r) (Syn.shift j))) ≐
        inst2 (GaussianRationalMatrixFiniteSums.deltaBody powerBody) (var 0) (pairT (Syn.shift r) (powerData (Syn.shift R) (Syn.shift j))) :=
      (GaussianRationalFubini.column_sum_at tripleBody _ _ _).eqTrans
        ((triple_column_cardinal _ _ _ _ hs.wk rs.wk (by simpa only [Syn.shift,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))).eqTrans
          ((GaussianRationalMatrixFiniteSums.delta_body_at powerBody _ _ _).eqTrans (qmul_congr (.eqRefl _) (power_body_at _ _ _))).eqSymm)
    simpa only [Δ,Syn.shift,subst_data,subst_length,subst_powerData,subst_pairT] using e
  exact (GaussianRationalFubini.fubini tripleBody _ _ _).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      ((GaussianRationalMatrixFiniteSums.sum_delta_canonical powerBody _ _ _ hr
        (GaussianRationalHorner.canonical_congr (power_body_at _ _ _) (power_canonical _ _))).eqTrans (power_body_at _ _ _)))
theorem positive_total (R r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hr : Γ ⊢[PRAAx] lt r (length R)) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum positiveBody (length R) (data R r j) ≐ power (entry R r) j :=
  (positive_sum_as_rows _ _ _).eqTrans (triple_total _ _ _ h hr)

def dotData (R m r j : PTm n) : PTm n := scalarData (GaussianRationalFiberVandermonde.W R m) (Z R m) r j
def leadingSum (R m r j : PTm n) : PTm n := GaussianRationalFiniteSum.sum scalarBody (length R) (dotData R m r j)
def tail (R m r j : PTm n) : PTm n := GaussianRationalFiniteSum.sum (offB scalarBody) (monus m (length R)) (pairT (length R) (dotData R m r j))
ipra_subst dotData
ipra_subst leadingSum
ipra_subst tail
theorem scalar_dot_split (R m r j : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    scalarDot (GaussianRationalFiberVandermonde.W R m) (Z R m) m r j ≐ qadd (leadingSum R m r j) (tail R m r j) :=
  (GaussianRationalFiniteSum.sum_index_congr scalarBody (eq_add_of_le ht) (.eqRefl (dotData R m r j))).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split scalarBody _ _ _)
theorem term_upper_left (R m r j k : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) (hk : Γ ⊢[PRAAx] lt k (length R)) : Γ ⊢[PRAAx]
    inst2 scalarBody k (dotData R m r j) ≐ GaussianRationalLagrangeCardinals.coefficientTerm R j (entry R r) k :=
  (GaussianRationalMatrixFiniteSums.scalar_body_at _ _ _ _ _).eqTrans
    (qmul_congr (GaussianRationalFiberVandermonde.W_upper _ _ _ _ (le_trans hr ht) hr (le_trans hk ht))
      ((Z_lookup _ _ _ _ (le_trans hk ht) (le_trans hj ht)).eqTrans (z_upper_left _ _ _ hk hj)))
theorem term_upper_right (R m r j k : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) (hjm : Γ ⊢[PRAAx] lt j m)
    (hk : Γ ⊢[PRAAx] lt k (length R)) : Γ ⊢[PRAAx]
    inst2 scalarBody k (dotData R m r j) ≐ qnegative (positiveTerm R r j k) :=
  (GaussianRationalMatrixFiniteSums.scalar_body_at _ _ _ _ _).eqTrans
    ((qmul_congr (GaussianRationalFiberVandermonde.W_upper _ _ _ _ (le_trans hr ht) hr (le_trans hk ht))
      ((Z_lookup _ _ _ _ (le_trans hk ht) hjm).eqTrans (z_upper_right _ _ _ hk hj))).eqTrans (multiply_negative_right _ _))
theorem term_tail (R m r j i : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) (hi : Γ ⊢[PRAAx] lt i (monus m (length R))) : Γ ⊢[PRAAx]
    inst2 (offB scalarBody) i (pairT (length R) (dotData R m r j)) ≐ qmul (power (entry R r) (length R+i)) (delta (length R+i) j) :=
  (GaussianRationalFiniteProduct.offset_at scalarBody _ _ _).eqTrans
    ((GaussianRationalMatrixFiniteSums.scalar_body_at _ _ _ _ _).eqTrans
      (qmul_congr (GaussianRationalFiberVandermonde.W_upper _ _ _ _ (le_trans hr ht) hr (offset_bound _ _ _ ht hi))
        ((Z_lookup _ _ _ _ (offset_bound _ _ _ ht hi) hj).eqTrans (z_lower _ _ _ (le_add_right _ _)))))

theorem prefix_left (R m r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    leadingSum R m r j ≐ delta r j := by
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using ht.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hj.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody GaussianRationalLagrangeCardinals.evaluationBody (length R)
      (dotData R m r j) (GaussianRationalLagrangeCardinals.evaluationData R j (entry R r)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 scalarBody (var 0) (dotData (Syn.shift R) (Syn.shift m) (Syn.shift r) (Syn.shift j)) ≐
        inst2 GaussianRationalLagrangeCardinals.evaluationBody (var 0) (GaussianRationalLagrangeCardinals.evaluationData (Syn.shift R) (Syn.shift j) (entry (Syn.shift R) (Syn.shift r))) :=
      (term_upper_left _ _ _ _ _ ts.wk rs.wk js.wk (by simpa only [Syn.shift,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))).eqTrans
        (GaussianRationalLagrangeCardinals.evaluation_body_at _ _ _ _).eqSymm
    simpa only [Δ,Syn.shift,subst_dotData,subst_length,subst_entry,GaussianRationalLagrangeCardinals.subst_evaluationData] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalLagrangeCardinals.cardinal_dot _ _ _ h hr hj)
theorem prefix_right (R m r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) (hjm : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    leadingSum R m r j ≐ qnegative (power (entry R r) j) := by
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using ht.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift j) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using hj.shift
  have jms : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hjm.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody (GaussianRationalMatrixFiniteSums.negativeBody positiveBody) (length R)
      (dotData R m r j) (data R r j) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 scalarBody (var 0) (dotData (Syn.shift R) (Syn.shift m) (Syn.shift r) (Syn.shift j)) ≐
        qnegative (inst2 positiveBody (var 0) (data (Syn.shift R) (Syn.shift r) (Syn.shift j))) :=
      (term_upper_right _ _ _ _ _ ts.wk rs.wk js.wk jms.wk (by simpa only [Syn.shift,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))).eqTrans
        (GaussianInverseBinomialRows.negative_congr (positive_body_at _ _ _ _)).eqSymm
    simpa only [Δ,GaussianRationalMatrixFiniteSums.negative_body_at,Syn.shift,subst_dotData,subst_data] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_negative _ _ _).eqTrans (GaussianInverseBinomialRows.negative_congr (positive_total _ _ _ h hr)))


theorem tail_delta_zero (t j i : PTm n) (hj : Γ ⊢[PRAAx] lt j t) : Γ ⊢[PRAAx] delta (t+i) j ≐ qzero :=
  GaussianRationalLagrangeCardinals.delta_unequal _ _
    (natural_neq_symm _ _ (GaussianRationalLagrangeCardinals.natural_neq_of_lt _ _ (lt_of_lt_of_le hj (le_add_right _ _))))
theorem tail_left (R m r j : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx] tail R m r j ≐ qzero := by
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using ht.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hj.shift
  apply GaussianRationalMatrixFiniteSums.sum_zero_of_terms
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (monus m (length R))) :: Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] inst2 (offB scalarBody) (var 0) (pairT (length (Syn.shift R)) (dotData (Syn.shift R) (Syn.shift m) (Syn.shift r) (Syn.shift j))) ≐ qzero :=
    (term_tail _ _ _ _ _ ts.wk rs.wk (le_trans js.wk ts.wk) (by simpa only [Syn.shift,PTm.subst_monus,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))).eqTrans
      ((qmul_congr (.eqRefl _) (tail_delta_zero _ _ _ js.wk)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))
  simpa only [Δ,Syn.shift,subst_dotData,subst_length,subst_pairT] using e

theorem tail_right (R m r j : PTm n) (ht : Γ ⊢[PRAAx] le (length R) m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) (hjm : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    tail R m r j ≐ power (entry R r) j := by
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using ht.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift j) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using hj.shift
  have jms : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hjm.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (offB scalarBody) (GaussianRationalMatrixFiniteSums.deltaBody shiftPowerBody)
      (monus m (length R)) (pairT (length R) (dotData R m r j)) (pairT (monus j (length R)) (data R r (length R))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (monus m (length R))) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 (offB scalarBody) (var 0) (pairT (length (Syn.shift R)) (dotData (Syn.shift R) (Syn.shift m) (Syn.shift r) (Syn.shift j))) ≐
        inst2 (GaussianRationalMatrixFiniteSums.deltaBody shiftPowerBody) (var 0) (pairT (monus (Syn.shift j) (length (Syn.shift R))) (data (Syn.shift R) (Syn.shift r) (length (Syn.shift R)))) :=
      (term_tail _ _ _ _ _ ts.wk rs.wk jms.wk (by simpa only [Syn.shift,PTm.subst_monus,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _))).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          ((qmul_congr (delta_shift _ _ _ js.wk) (.eqRefl _)).eqTrans
            ((GaussianRationalMatrixFiniteSums.delta_body_at shiftPowerBody _ _ _).eqTrans
              (qmul_congr (.eqRefl _) (shift_power_body_at _ _ _ _))).eqSymm))
    simpa only [Δ,Syn.shift,subst_dotData,subst_data,subst_length,subst_pairT,PTm.subst_monus] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta_canonical shiftPowerBody _ _ _ (tail_index_bound _ _ _ hj hjm)
      (GaussianRationalHorner.canonical_congr (shift_power_body_at _ _ _ _) (power_canonical _ _))).eqTrans
        ((shift_power_body_at _ _ _ _).eqTrans (congrAp2 GaussianRationalReciprocal.powerF (eq_add_of_le hj).eqSymm (.eqRefl _))))

theorem lower_dot (R m r j : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r)
    (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    scalarDot (GaussianRationalFiberVandermonde.W R m) (Z R m) m r j ≐ delta r j := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift r) := by simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using hr.shift
  have rms : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hrm.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody (GaussianRationalMatrixFiniteSums.deltaBody zColumnBody) m
      (dotData R m r j) (pairT r (data R m j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 scalarBody (var 0) (dotData (Syn.shift R) (Syn.shift m) (Syn.shift r) (Syn.shift j)) ≐
        inst2 (GaussianRationalMatrixFiniteSums.deltaBody zColumnBody) (var 0) (pairT (Syn.shift r) (data (Syn.shift R) (Syn.shift m) (Syn.shift j))) :=
      (GaussianRationalMatrixFiniteSums.scalar_body_at _ _ _ _ _).eqTrans
        ((qmul_congr (GaussianRationalFiberVandermonde.W_lower _ _ _ _ rms.wk rs.wk Prf.hyp0) (.eqRefl _)).eqTrans
          ((GaussianRationalMatrixFiniteSums.delta_body_at zColumnBody _ _ _).eqTrans (qmul_congr (.eqRefl _) (z_column_body_at _ _ _ _))).eqSymm)
    simpa only [Δ,Syn.shift,subst_dotData,subst_data,subst_pairT] using e
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta_canonical zColumnBody _ _ _ hrm
      (GaussianRationalHorner.canonical_congr (z_column_body_at _ _ _ _) (Z_canonical _ _ _ _ hrm hjm))).eqTrans
        ((z_column_body_at _ _ _ _).eqTrans ((Z_lookup _ _ _ _ hrm hjm).eqTrans (z_lower _ _ _ hr))))

theorem whole_dot (R m r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    scalarDot (GaussianRationalFiberVandermonde.W R m) (Z R m) m r j ≐ delta r j := by
  refine .orE (lt_or_le r (length R)) ?_ ?_
  · refine .orE (lt_or_le j (length R)) ?_ ?_
    · exact (scalar_dot_split _ _ _ _ ht.wk.wk).eqTrans
        ((qadd_congr (prefix_left _ _ _ _ h.wk.wk ht.wk.wk Prf.hyp1 Prf.hyp0)
          (tail_left _ _ _ _ ht.wk.wk Prf.hyp1 Prf.hyp0)).eqTrans
            (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiberVandermonde.delta_canonical _ _)))
    · exact (scalar_dot_split _ _ _ _ ht.wk.wk).eqTrans
        ((qadd_congr (prefix_right _ _ _ _ h.wk.wk ht.wk.wk Prf.hyp1 Prf.hyp0 hj.wk.wk)
          (tail_right _ _ _ _ ht.wk.wk Prf.hyp1 Prf.hyp0 hj.wk.wk)).eqTrans
            ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
              ((GaussianCoefficientNormOrder.qsub_self _).eqTrans
                (GaussianRationalLagrangeCardinals.delta_unequal _ _
                  (GaussianRationalLagrangeCardinals.natural_neq_of_lt _ _ (lt_of_lt_of_le Prf.hyp1 Prf.hyp0))).eqSymm)))
  · exact lower_dot _ _ _ _ Prf.hyp0 hr.wk hj.wk
theorem right_inverse_at (R m r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m) r j ≐ delta r j :=
  (GaussianRationalMatrixFiniteSums.product_lookup _ _ _ _ _ hr hj).eqTrans (whole_dot _ _ _ _ h ht hr hj)


theorem small_inverse_at (R r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    cell (matrixProduct (GaussianRationalFiberVandermonde.U R (length R)) (N R) (length R)) r j ≐ delta r j := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hr.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift R)) := by simpa only [Fm.shift,subst_lt,subst_length,Syn.shift] using hj.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody GaussianRationalLagrangeCardinals.evaluationBody (length R)
      (scalarData (GaussianRationalFiberVandermonde.U R (length R)) (N R) r j) (GaussianRationalLagrangeCardinals.evaluationData R j (entry R r)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
    have kk : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift R)) := by simpa only [Δ,Syn.shift,subst_length] using (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have e : Δ ⊢[PRAAx] inst2 scalarBody (var 0) (scalarData (GaussianRationalFiberVandermonde.U (Syn.shift R) (length (Syn.shift R))) (N (Syn.shift R)) (Syn.shift r) (Syn.shift j)) ≐
        inst2 GaussianRationalLagrangeCardinals.evaluationBody (var 0) (GaussianRationalLagrangeCardinals.evaluationData (Syn.shift R) (Syn.shift j) (entry (Syn.shift R) (Syn.shift r))) :=
      (GaussianRationalMatrixFiniteSums.scalar_body_at _ _ _ _ _).eqTrans
        ((qmul_congr (GaussianRationalFiberVandermonde.U_lookup _ _ _ _ rs.wk kk) (N_lookup _ _ _ kk js.wk)).eqTrans
          (GaussianRationalLagrangeCardinals.evaluation_body_at _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalMatrixFiniteSums.subst_scalarData,GaussianRationalFiberVandermonde.subst_U,subst_N,subst_length,subst_entry,GaussianRationalLagrangeCardinals.subst_evaluationData] using e
  exact (GaussianRationalMatrixFiniteSums.product_lookup _ _ _ _ _ hr hj).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalLagrangeCardinals.cardinal_dot _ _ _ h hr hj))

def identityTable (P m : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶ .all
  (lt (var 0) (Syn.shift (Syn.shift m)) ⟶ cell (Syn.shift (Syn.shift P)) (var 1) (var 0) ≐ delta (var 1) (var 0)))
ipra_subst identityTable [cell, Syn.subst_shift, Syn.shift_subst]
theorem right_inverse (R m : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    identityTable (matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have hd : Δ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (Syn.shift (Syn.shift R)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianRationalFiniteRoots.subst_distinct,Syn.shift] using h.shift.shift.wk.wk
  have tt : Δ ⊢[PRAAx] le (length (Syn.shift (Syn.shift R))) (Syn.shift (Syn.shift m)) := by
    simpa only [Δ,List.map_cons,Fm.shift,subst_le,subst_length,Syn.shift] using ht.shift.shift.wk.wk
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have e := right_inverse_at (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m)) (var 1) (var 0) hd tt rr (Prf.hyp0 : Δ ⊢[PRAAx] _)
  simpa only [Δ,Syn.shift,GaussianRationalMatrixFiniteSums.subst_matrixProduct,GaussianRationalFiberVandermonde.subst_W,subst_Z] using e
theorem empty_fiber_dot (R m r j : PTm n) (h0 : Γ ⊢[PRAAx] length R ≐ zero)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    scalarDot (GaussianRationalFiberVandermonde.W R m) (Z R m) m r j ≐ delta r j :=
  lower_dot _ _ _ _ (le_congr h0.eqSymm (.eqRefl _) (zero_le _)) hr hj

def certificate (R m : PTm n) : Fm PTm n := scalarShape (N R) (length R) (length R) ⋏
  (scalarShape (C R m) (length R) (monus m (length R)) ⋏ (scalarShape (Z R m) m m ⋏
    identityTable (matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m) m))
ipra_subst certificate
theorem inverse_correct (R m : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] certificate R m :=
  .andI (N_shape _) (.andI (C_shape _ _) (.andI (Z_shape _ _) (right_inverse _ _ h ht)))

def output (R m : PTm n) : PTm n := pairT
  (GaussianRationalFiberVandermonde.productData (N R) (C R m) (GaussianRationalFiberVandermonde.W R m) (Z R m)
    (matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m)) (pairT R (pairT (length R) m))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (R m : PTm n) : PTm n := ap2 outputF R m
def productField (q : PTm n) : PTm n := GaussianRationalFiberVandermonde.fields (fstT q) 4
ipra_subst output
ipra_subst run
ipra_subst productField
theorem program_at (R m : PTm n) : Γ ⊢[PRAAx] run R m ≐ output R m := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![R,m]
theorem returned_field (R m : PTm n) (i : Fin 5) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.fields (fstT (run R m)) i ≐ ![N R,C R m,GaussianRationalFiberVandermonde.W R m,Z R m,
      matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m] i :=
  (GaussianRationalLagrangeCardinals.fields_congr (program_at _ _).fstE i).eqTrans
    (GaussianRationalFiberVandermonde.field_at _ _ _ _ _ i)
theorem returned_N (R m : PTm n) : Γ ⊢[PRAAx] fstT (fstT (run R m)) ≐ N R := returned_field _ _ 0
theorem returned_C (R m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (fstT (run R m))) ≐ C R m := returned_field _ _ 1
theorem returned_W (R m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (fstT (run R m)))) ≐ GaussianRationalFiberVandermonde.W R m := returned_field _ _ 2
theorem returned_Z (R m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (fstT (run R m))))) ≐ Z R m := returned_field _ _ 3
theorem returned_product (R m : PTm n) : Γ ⊢[PRAAx] productField (run R m) ≐ matrixProduct (GaussianRationalFiberVandermonde.W R m) (Z R m) m := returned_field _ _ 4
theorem returned_data (R m : PTm n) : Γ ⊢[PRAAx] sndT (run R m) ≐ pairT R (pairT (length R) m) :=
  (program_at _ _).sndE
theorem returned_roots (R m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run R m)) ≐ R := (returned_data _ _).fstE
theorem returned_t (R m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run R m))) ≐ length R :=
  (returned_data _ _).sndE.fstE
theorem returned_m (R m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run R m))) ≐ m :=
  (returned_data _ _).sndE.sndE
theorem identity_table_congr {P Q m : PTm n} (e : Γ ⊢[PRAAx] P ≐ Q) (h : Γ ⊢[PRAAx] identityTable P m) : Γ ⊢[PRAAx] identityTable Q m := by
  simpa only [subst_identityTable,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (identityTable (var 0) (var 1) : Fm PTm 2) ![P,m] ![Q,m]
      (fun i => by fin_cases i; exact e; exact .eqRefl _) (by simpa only [subst_identityTable,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h)
theorem returned_right_inverse (R m : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] identityTable (productField (run R m)) m :=
  identity_table_congr (returned_product _ _).eqSymm (right_inverse _ _ h ht)

def sourceOutput (L p g m : PTm n) : PTm n := pairT (run (GaussianRationalCurveFibers.yList L p g) m)
  (pairT (GaussianRationalCurveFibers.selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p))
def sourceF : PR 4 := PTm.toPR (sourceOutput (var 0) (var 1) (var 2) (var 3))
def sourceRun (L p g m : PTm n) : PTm n := app sourceF ![L,p,g,m]
ipra_subst sourceOutput
ipra_subst sourceRun
theorem source_program_at (L p g m : PTm n) : Γ ⊢[PRAAx] sourceRun L p g m ≐ sourceOutput L p g m := by
  simpa [sourceRun,sourceF] using toPR_eq (Γ := Γ) (sourceOutput (var 0) (var 1) (var 2) (var 3) : PTm 4) ![L,p,g,m]
theorem source_returned_generic (L p g m : PTm n) : Γ ⊢[PRAAx] fstT (sourceRun L p g m) ≐ run (GaussianRationalCurveFibers.yList L p g) m :=
  (source_program_at _ _ _ _).fstE
theorem source_returned_product (L p g m : PTm n) : Γ ⊢[PRAAx]
    productField (fstT (sourceRun L p g m)) ≐ matrixProduct (GaussianRationalFiberVandermonde.W (GaussianRationalCurveFibers.yList L p g) m) (Z (GaussianRationalCurveFibers.yList L p g) m) m :=
  (GaussianRationalLagrangeCardinals.fields_congr (congrFst (source_returned_generic _ _ _ _)) 4).eqTrans (returned_product _ _)
theorem source_returned_roots (L p g m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (fstT (sourceRun L p g m))) ≐ GaussianRationalCurveFibers.yList L p g :=
  (congrFst (congrSnd (source_returned_generic _ _ _ _))).eqTrans (returned_roots _ _)
theorem source_returned_x (L p g m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sourceRun L p g m)) ≐ GaussianRationalCurveFibers.selectedX L p g :=
  (source_program_at _ _ _ _).sndE.fstE
theorem source_returned_partition (L p g m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sourceRun L p g m)) ≐ length L :=
  (source_program_at _ _ _ _).sndE.sndE.eqTrans (GaussianRationalFiberGrouping.cardinal_partition _ _)
theorem source_size_bound (F m L p g : PTm n) (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx] le (length (GaussianRationalCurveFibers.yList L p g)) m :=
  le_congr (GaussianRationalCurveFibers.y_length _ _ _).eqSymm (.eqRefl _) (GaussianRationalCurveFibers.fiber_size_bound _ _ _ _ _ hCurve hDistinct)
theorem source_correct (F m L p g : PTm n) (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx] certificate (GaussianRationalCurveFibers.yList L p g) m :=
  inverse_correct _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct) (source_size_bound _ _ _ _ _ hCurve hDistinct)
theorem source_right_inverse (F m L p g : PTm n) (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx] identityTable (productField (fstT (sourceRun L p g m))) m :=
  identity_table_congr (source_returned_product _ _ _ _).eqSymm
    (right_inverse _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct) (source_size_bound _ _ _ _ _ hCurve hDistinct))


theorem full_size_dot (R m r j : PTm n) (h : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (ht : Γ ⊢[PRAAx] length R ≐ m) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    scalarDot (GaussianRationalFiberVandermonde.W R m) (Z R m) m r j ≐ delta r j :=
  whole_dot _ _ _ _ h (le_congr (.eqRefl _) ht (le_refl _)) hr hj

/-! All list codes, dimensions, coordinates and source parameters are
bound in ordinary PRA endpoints. F occurs only in the original curve
hypothesis; the actual source program reads the original fiber and m. -/
theorem scalar_right_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶ lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶
      scalarDot (GaussianRationalFiberVandermonde.W (var 0) (var 1)) (Z (var 0) (var 1)) (var 1) (var 2) (var 3) ≐ delta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (whole_dot _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem small_cardinal_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ lt (var 1) (length (var 0)) ⟶ lt (var 2) (length (var 0)) ⟶
      cell (matrixProduct (GaussianRationalFiberVandermonde.U (var 0) (length (var 0))) (N (var 0)) (length (var 0))) (var 1) (var 2) ≐ delta (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (small_inverse_at _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem whole_matrix_right_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶
      identityTable (matrixProduct (GaussianRationalFiberVandermonde.W (var 0) (var 1)) (Z (var 0) (var 1)) (var 1)) (var 1)) :=
  closeUniv 2 (.impI (.impI (right_inverse _ _ Prf.hyp1 Prf.hyp0)))
theorem empty_fiber_right_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (var 0) ≐ zero) ⟶ lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶
      scalarDot (GaussianRationalFiberVandermonde.W (var 0) (var 1)) (Z (var 0) (var 1)) (var 1) (var 2) (var 3) ≐ delta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (empty_fiber_dot _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem full_fiber_right_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ (length (var 0) ≐ var 1) ⟶ lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶
      scalarDot (GaussianRationalFiberVandermonde.W (var 0) (var 1)) (Z (var 0) (var 1)) (var 1) (var 2) (var 3) ≐ delta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (full_size_dot _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem inverse_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏ (fstT (sndT (run (var 0) (var 1))) ≐ var 0)) :=
  closeUniv 2 (.andI (program_at _ _) (returned_roots _ _))
theorem returned_right_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶ identityTable (productField (run (var 0) (var 1))) (var 1)) :=
  closeUniv 2 (.impI (.impI (returned_right_inverse _ _ Prf.hyp1 Prf.hyp0)))
theorem original_fiber_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalCurveFibers.curveZeros (var 0) (var 1) (var 2) ⟶ GaussianRationalCurveFibers.pointDistinct (var 2) ⟶
      certificate (GaussianRationalCurveFibers.yList (var 2) (var 3) (var 4)) (var 1)) :=
  closeUniv 5 (.impI (.impI (source_correct _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem returned_source_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalCurveFibers.curveZeros (var 0) (var 1) (var 2) ⟶ GaussianRationalCurveFibers.pointDistinct (var 2) ⟶
      identityTable (productField (fstT (sourceRun (var 2) (var 3) (var 4) (var 1)))) (var 1)) :=
  closeUniv 5 (.impI (.impI (source_right_inverse _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem source_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (sndT (fstT (sourceRun (var 0) (var 1) (var 2) (var 3)))) ≐ GaussianRationalCurveFibers.yList (var 0) (var 1) (var 2)) ⋏
      ((fstT (sndT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ GaussianRationalCurveFibers.selectedX (var 0) (var 1) (var 2)) ⋏
        (sndT (sndT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ length (var 0)))) :=
  closeUniv 4 (.andI (source_returned_roots _ _ _ _) (.andI (source_returned_x _ _ _ _) (source_returned_partition _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiberRightInverse

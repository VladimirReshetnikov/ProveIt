import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Core.SumSplit

/-!
# Actual finite Gaussian-rational products

A fixed entry syntax supplies arbitrary original raw factors at numerical
positions and data. The actual rec2 fold starts at canonical qone and
appends factors with qmul. Genuine QF inductions prove bounded original
entry congruence, a numerical prefix/suffix split, and invariance under
entry recoding. The singleton result is the canonical recode of its raw
factor, not an incorrect equality with an arbitrary original code.

All counts, cuts and persistent data remain internal. The product program
and its actual PR3 split payload are bound literally. Adjacent-swap readers,
permutation products and the existing determinant scalar fold are separate
downstream adapters; no desired product law is supplied here as input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stepBody (t : PTm 2) : PTm 3 := qmul (var 1) (inst2 t (var 0) (var 2))
def productF (t : PTm 2) : PR 2 := rec2 (qone : PTm 1) (stepBody t)
def qprod (t : PTm 2) (N x : PTm n) : PTm n := ap2 (productF t) N x

ipra_subst qprod

theorem product_zero (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] qprod t zero x ≐ qone := by
  simpa only [qprod,productF,GaussianRationalSyntheticDivision.subst_qone] using
    rec2_zero (Γ := Γ) (qone : PTm 1) (stepBody t) x

theorem product_succ (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    qprod t (succ N) x ≐ qmul (qprod t N x) (inst2 t N x) := by
  simpa only [qprod,productF,stepBody,GaussianRationalHorner.subst_qmul,subst_inst2,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      rec2_succ (Γ := Γ) (qone : PTm 1) (stepBody t) N x

theorem product_index_congr (t : PTm 2) {N M x y : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ M) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] qprod t N x ≐ qprod t M y :=
  congrAp2 (productF t) hN hx

/-- Canonicality is derived from the actual base or last multiplication. -/
theorem product_canonical (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] canonical (qprod t N x) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((product_index_congr t Prf.hyp0 (.eqRefl _)).eqTrans (product_zero t x)) qone_canonical
  · exact GaussianRationalHorner.canonical_congr
      ((product_index_congr t Prf.hyp0 (.eqRefl _)).eqTrans (product_succ t _ x))
      (GaussianRationalHorner.qmul_canonical _ _)

def prefixLaw (t u : PTm 2) (N x y k : PTm n) : Fm PTm n :=
  le k N ⟶ qprod t k x ≐ qprod u k y

ipra_subst prefixLaw

theorem prefix_step (t u : PTm 2) (N x y k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual t u N x y)
    (hk : Γ ⊢[PRAAx] lt k N) (ih : Γ ⊢[PRAAx] qprod t k x ≐ qprod u k y) : Γ ⊢[PRAAx]
    qprod t (succ k) x ≐ qprod u (succ k) y :=
  (product_succ t k x).eqTrans ((qmul_congr ih
    (GaussianRationalFiniteSum.term_equal_at t u N x y k h hk)).eqTrans (product_succ u k y).eqSymm)

/-- The original bounded entry equations remain context hypotheses;
the induction formula is only a guarded equality of actual products. -/
theorem product_prefix_congr (t u : PTm 2) (N x y k : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual t u N x y)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] qprod t k x ≐ qprod u k y := by
  let invariant := qprod t (var 0) (Syn.shift x) ≐ qprod u (var 0) (Syn.shift y)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      GaussianRationalFiniteSum.termsEqual t u (Syn.shift N) (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift, GaussianRationalFiniteSum.subst_termsEqual, Syn.shift] using h.shift
  suffices result : Γ ⊢[PRAAx] invariant.subst (Syn.inst k) by simpa [invariant] using result
  refine qfIndAtMost hk trivial ?_ ?_
  · simpa [invariant] using (product_zero (Γ := Γ) t x).eqTrans (product_zero u y).eqSymm
  · simp [invariant]
    exact .impI (prefix_step t u _ _ _ _ shifted.wk.wk Prf.hyp0 Prf.hyp1)

theorem product_congr_bounded (t u : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual t u N x y) : Γ ⊢[PRAAx]
    qprod t N x ≐ qprod u N y := product_prefix_congr t u N x y N h (le_refl _)

theorem offset_at (t : PTm 2) (N i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB t) i (pairT N x) ≐ inst2 t (N+i) x := by
  rw [inst2_offB]
  exact congrInst2 t (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

def splitLaw (t : PTm 2) (N M x : PTm n) : Fm PTm n :=
  qprod t (N+M) x ≐ qmul (qprod t N x) (qprod (offB t) M (pairT N x))
ipra_subst splitLaw

theorem split_zero (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] splitLaw t N zero x :=
  (product_index_congr t (add_zero N) (.eqRefl _)).eqTrans
    ((qmul_congr (.eqRefl _) (product_zero (offB t) (pairT N x))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (product_canonical t N x))).eqSymm

theorem split_step (t : PTm 2) (N M x : PTm n) (ih : Γ ⊢[PRAAx] splitLaw t N M x) : Γ ⊢[PRAAx]
    splitLaw t N (succ M) x :=
  ((product_index_congr t (add_succ N M) (.eqRefl _)).eqTrans (product_succ t (N+M) x)).eqTrans
    ((qmul_congr ih (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
        (qmul_congr (.eqRefl _) ((product_succ (offB t) M (pairT N x)).eqTrans
          (qmul_congr (.eqRefl _) (offset_at t N M x))).eqSymm)))

/-- A true numerical cut of the same original factor stream. -/
theorem product_split (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx]
    qprod t (N+M) x ≐ qmul (qprod t N x) (qprod (offB t) M (pairT N x)) := by
  have all : Γ ⊢[PRAAx] .all (splitLaw t (Syn.shift N) (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_splitLaw]
    · exact split_zero t N x
    · exact split_step t _ _ _ Prf.hyp0
  have actual : Γ ⊢[PRAAx] splitLaw t N M x := by
    simpa only [subst_splitLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE M
  exact actual

def recodeBody (t : PTm 2) : PTm 2 := recode t
@[simp] theorem recode_body_at (t : PTm 2) (i x : PTm n) :
    inst2 (recodeBody t) i x = recode (inst2 t i x) := by simp only [inst2,recodeBody,GaussianTranslatedNonconstant.subst_recode]

def recodeLaw (t : PTm 2) (N x : PTm n) : Fm PTm n := qprod (recodeBody t) N x ≐ qprod t N x
ipra_subst recodeLaw

theorem recode_step (t : PTm 2) (N x : PTm n) (ih : Γ ⊢[PRAAx] recodeLaw t N x) : Γ ⊢[PRAAx]
    recodeLaw t (succ N) x := by
  have actual := product_succ (Γ := Γ) (recodeBody t) N x
  rw [recode_body_at] at actual
  exact actual.eqTrans ((qmul_congr ih (.eqRefl _)).eqTrans
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqTrans (product_succ t N x).eqSymm))

theorem product_recode (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] qprod (recodeBody t) N x ≐ qprod t N x := by
  have all : Γ ⊢[PRAAx] .all (recodeLaw t (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_recodeLaw]
    · exact (product_zero _ _).eqTrans (product_zero _ _).eqSymm
    · exact recode_step t _ _ Prf.hyp0
  have actual : Γ ⊢[PRAAx] recodeLaw t N x := by
    simpa only [subst_recodeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact actual

theorem raw_one_left (q : PTm n) : Γ ⊢[PRAAx] qmul qone q ≐ recode q :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_right qone q).eqSymm.eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (recode_canonical q)))

/-- A raw singleton is normalized by the genuine operation, not returned unchanged. -/
theorem product_singleton (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] qprod t one x ≐ recode (inst2 t zero x) :=
  (product_succ t zero x).eqTrans ((qmul_congr (product_zero t x) (.eqRefl _)).eqTrans (raw_one_left _))

/-- The actual payload retains whole, prefix and independently folded suffix. -/
def output (t : PTm 2) (N M x : PTm n) : PTm n :=
  pairT (qprod t (N+M) x) (pairT (qprod t N x) (qprod (offB t) M (pairT N x)))
def outputF (t : PTm 2) : PR 3 := PTm.toPR (output t (var 0) (var 1) (var 2))
def run (t : PTm 2) (N M x : PTm n) : PTm n := ap3 (outputF t) N M x
ipra_subst output
ipra_subst run

theorem program_at (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] run t N M x ≐ output t N M x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output t (var 0) (var 1) (var 2) : PTm 3) ![N,M,x]
theorem returned_whole (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] fstT (run t N M x) ≐ qprod t (N+M) x :=
  (program_at t N M x).fstE
theorem returned_prefix (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run t N M x)) ≐ qprod t N x :=
  (program_at t N M x).sndE.fstE
theorem returned_suffix (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run t N M x)) ≐ qprod (offB t) M (pairT N x) :=
  (program_at t N M x).sndE.sndE
theorem returned_split (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx]
    fstT (run t N M x) ≐ qmul (fstT (sndT (run t N M x))) (sndT (sndT (run t N M x))) :=
  (returned_whole t N M x).eqTrans ((product_split t N M x).eqTrans
    (qmul_congr (returned_prefix t N M x) (returned_suffix t N M x)).eqSymm)
theorem returned_whole_canonical (t : PTm 2) (N M x : PTm n) : Γ ⊢[PRAAx] canonical (fstT (run t N M x)) :=
  GaussianRationalHorner.canonical_congr (returned_whole t N M x) (product_canonical t (N+M) x)

theorem product_recurrence_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((qprod t zero (var 1) ≐ qone) ⋏
      qprod t (succ (var 0)) (var 1) ≐ qmul (qprod t (var 0) (var 1)) (inst2 t (var 0) (var 1))) :=
  closeUniv 2 (.andI (product_zero _ _) (product_succ _ _ _))
theorem product_congruence_closed (t u : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalFiniteSum.termsEqual t u (var 0) (var 1) (var 2) ⟶ qprod t (var 0) (var 1) ≐ qprod u (var 0) (var 2)) :=
  closeUniv 3 (.impI (product_congr_bounded _ _ _ _ _ Prf.hyp0))
theorem product_split_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qprod t (var 0+var 1) (var 2) ≐ qmul (qprod t (var 0) (var 2)) (qprod (offB t) (var 1) (pairT (var 0) (var 2)))) :=
  closeUniv 3 (product_split _ _ _ _)
theorem product_recode_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qprod (recodeBody t) (var 0) (var 1) ≐ qprod t (var 0) (var 1)) := closeUniv 2 (product_recode _ _ _)
theorem product_singleton_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qprod t one (var 0) ≐ recode (inst2 t zero (var 0))) := closeUniv 1 (product_singleton _ _)
theorem product_canonical_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (qprod t (var 0) (var 1))) := closeUniv 2 (product_canonical _ _ _)
theorem actual_product_program_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run t (var 0) (var 1) (var 2) ≐ output t (var 0) (var 1) (var 2)) ⋏
      ((fstT (run t (var 0) (var 1) (var 2)) ≐ qprod t (var 0+var 1) (var 2)) ⋏
        ((fstT (sndT (run t (var 0) (var 1) (var 2))) ≐ qprod t (var 0) (var 2)) ⋏
          sndT (sndT (run t (var 0) (var 1) (var 2))) ≐ qprod (offB t) (var 1) (pairT (var 0) (var 2))))) :=
  closeUniv 3 (.andI (program_at _ _ _ _) (.andI (returned_whole _ _ _ _)
    (.andI (returned_prefix _ _ _ _) (returned_suffix _ _ _ _))))
theorem returned_product_split_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((fstT (run t (var 0) (var 1) (var 2)) ≐
      qmul (fstT (sndT (run t (var 0) (var 1) (var 2)))) (sndT (sndT (run t (var 0) (var 1) (var 2))))) ⋏
      canonical (fstT (run t (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (returned_split _ _ _ _) (returned_whole_canonical _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct

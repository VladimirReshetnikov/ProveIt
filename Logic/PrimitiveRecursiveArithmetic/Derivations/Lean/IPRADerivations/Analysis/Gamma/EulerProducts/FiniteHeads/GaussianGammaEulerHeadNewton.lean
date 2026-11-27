import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadGeometricStep
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Newton identity for the unchanged original Euler-head program

For the actual zero-extended original coefficient A_N(e), the genuine
double finite sum over k<N and j<=s of
(-1/(k+1))^j /(k+1) A_N(s-j) is exactly s A_N(s+1).
The proof inducts on the actual original head stage. Its independently
proved reader step and genuine finite geometric cancellation discharge
every term equation. Bounded-formula induction is compiled to genuine
quantifier-free PRA induction. All numerical indices remain internal;
no Newton identity, differentiation law or output relation is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadNewton

open_ipra
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalNaturalScale (natScale natScale_congr)
open GaussianGammaEulerHeadExponentStep (reader reader_congr reader_zero)
open GaussianGammaEulerHeadGeometricStep (value)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N s : PTm n) : PTm n := pairT N s
def body : PTm 2 := value (reciprocalPoint (var 0)) (fstT (var 1)) (sndT (var 1))
def newtonSum (N s : PTm n) : PTm n := sum body N (data N s)
ipra_subst data
ipra_subst newtonSum

theorem value_congr {a b N M s t : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hs : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx] value a N s ≐ value b M t := by
  ipra_congr (value (var 0) (var 1) (var 2) : PTm 3) with [ha, hN, hs]

theorem term_at (N s k : PTm n) : Γ ⊢[PRAAx] inst2 body k (data N s) ≐ value (reciprocalPoint k) N s := by
  simp only [body,inst2,GaussianGammaEulerHeadGeometricStep.subst_value,
    GaussianGammaHarmonicIncrement.subst_reciprocalPoint,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact value_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem newton_congr {N M s t : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M) (hs : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] newtonSum N s ≐ newtonSum M t :=
  GaussianRationalFiniteSum.sum_index_congr body hN (congrPairT hN hs)

theorem zero_stage (s : PTm n) : Γ ⊢[PRAAx] newtonSum zero s ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem zero_degree (N : PTm n) : Γ ⊢[PRAAx] newtonSum N zero ≐ qzero := by
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual body (qzero : PTm 2) N (data N zero) zero := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_data,PTm.subst_zero,inst2,GaussianRationalHorner.subst_qzero] using
      (term_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift N) zero (var 0)).eqTrans
        (GaussianGammaEulerHeadGeometricStep.value_zero _ _)
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans
    (GaussianRationalPolynomialProduct.constant_zero_sum _ _)

theorem linear_terms (N s : PTm n) : Γ ⊢[PRAAx] GaussianInverseBinomialRows.linearTerms body body body
    N (data (succ N) (succ s)) (data N (succ s)) (data N s) (reciprocalPoint N) := by
  refine .allI (.impI ?_)
  have h := (term_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    (succ (Syn.shift N)) (succ (Syn.shift s)) (var 0)).eqTrans
      ((GaussianGammaEulerHeadGeometricStep.original_geometric_step _ _ _).eqTrans
        (qadd_congr (term_at _ _ _).eqSymm (qmul_congr (.eqRefl _) (term_at _ _ _).eqSymm)))
  simpa only [Syn.shift,subst_data,PTm.subst_succ,GaussianGammaHarmonicIncrement.subst_reciprocalPoint] using h

theorem original_sum_successor (N s : PTm n) : Γ ⊢[PRAAx]
    newtonSum (succ N) (succ s) ≐
      qadd (qadd (newtonSum N (succ s)) (qmul (reciprocalPoint N) (newtonSum N s)))
        (qmul (reciprocalPoint N) (reader N (succ s))) :=
  (GaussianRationalFiniteSum.sum_succ body N (data (succ N) (succ s))).eqTrans
    (qadd_congr (GaussianInverseBinomialRows.linear_sum body body body _ _ _ _ _ (linear_terms N s))
      ((term_at _ _ _).eqTrans (GaussianGammaEulerHeadGeometricStep.original_new_factor_cancellation N s)))

alias scale_zero := GaussianRationalFactorialEulerSums.scale_zero_value

theorem scale_succ (t q : PTm n) : Γ ⊢[PRAAx] natScale (succ t) q ≐ qadd (natScale t q) q :=
  (natScale_congr (show Γ ⊢[PRAAx] succ t ≐ t+one by ipra_ring) (.eqRefl _)).eqTrans
    ((GaussianRationalNaturalScale.natScale_add _ _ _).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_one q)).eqTrans
        (GaussianRationalSyntheticCoefficientValues.qadd_recode_right _ _)))

theorem scale_sum (t x y : PTm n) : Γ ⊢[PRAAx]
    natScale t (qadd x y) ≐ qadd (natScale t x) (natScale t y) :=
  (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
      (qadd_congr (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm
        (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

def law (N s : PTm n) : Fm PTm n := newtonSum N s ≐ natScale s (reader N (succ s))
ipra_subst law

theorem law_transport (N s t : PTm n) (hst : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] law N t) :
    Γ ⊢[PRAAx] law N s :=
  (newton_congr (.eqRefl N) hst).eqTrans
    (h.eqTrans (natScale_congr hst.eqSymm (reader_congr (.eqRefl N) (congrSucc hst.eqSymm))))

theorem zero_law (N : PTm n) : Γ ⊢[PRAAx] law N zero :=
  (zero_degree N).eqTrans (GaussianRationalNaturalScale.natScale_zero _).eqSymm

theorem base_high (s : PTm n) : Γ ⊢[PRAAx] reader zero (succ (succ s)) ≐ qzero :=
  GaussianRationalLowCoefficientConvolution.exponent_outside _ _ _ ((succ_monus_succ _ _).eqTrans (zero_lt_succ s))

theorem base_law (s : PTm n) : Γ ⊢[PRAAx] law zero s := by
  have rhs : Γ ⊢[PRAAx] natScale s (reader zero (succ s)) ≐ qzero := by
    refine .orE (zero_or_succ s) ?_ ?_
    · exact (natScale_congr Prf.hyp0 (.eqRefl _)).eqTrans (GaussianRationalNaturalScale.natScale_zero _)
    · exact (natScale_congr (.eqRefl _) ((reader_congr (.eqRefl zero) (congrSucc Prf.hyp0)).eqTrans (base_high (pred s)))).eqTrans
        (scale_zero s)
  exact (zero_stage s).eqTrans rhs.eqSymm

theorem positive_step (N s : PTm n) (ihNext : Γ ⊢[PRAAx] law N (succ s)) (ihPrev : Γ ⊢[PRAAx] law N s) :
    Γ ⊢[PRAAx] law (succ N) (succ s) :=
  (original_sum_successor N s).eqTrans
    ((qadd_congr (qadd_congr ihNext (qmul_congr (.eqRefl _) ihPrev)) (.eqRefl _)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans
        ((qadd_congr (.eqRefl _)
          ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
            ((qmul_congr (.eqRefl _) (scale_succ s (reader N (succ s))).eqSymm).eqTrans
              (GaussianRationalNaturalScale.natScale_product _ _ _)))).eqTrans
          ((scale_sum (succ s) _ _).eqSymm.eqTrans
            (natScale_congr (.eqRefl _) (GaussianGammaEulerHeadExponentStep.original_reader_step N (succ s)).eqSymm)))))

def newtonPrefix (N E : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift E)) ⟶ law (Syn.shift N) (var 0))
def prefixSyntax (N E : PTm n) : BFm n := .all (succ E) (.eq
  (newtonSum (Syn.shift N) (var 0)) (natScale (var 0) (reader (Syn.shift N) (succ (var 0)))))
@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (N E : PTm n) :
    (newtonPrefix N E).subst σ = newtonPrefix (Syn.subst σ N) (Syn.subst σ E) := by
  simp [newtonPrefix,Syn.subst_shift,Syn.shift_subst]
theorem prefix_formula (N E : PTm n) : formula (prefixSyntax N E) = newtonPrefix N E := by
  simp [prefixSyntax,newtonPrefix,law,formula]

theorem prefix_at (N E s : PTm n) (h : Γ ⊢[PRAAx] newtonPrefix N E) (hs : Γ ⊢[PRAAx] le s E) :
    Γ ⊢[PRAAx] law N s := by
  have rule : Γ ⊢[PRAAx] lt s (succ E) ⟶ law N s := by simpa [newtonPrefix] using h.allE s
  exact .impE rule ((succ_monus_succ _ _).eqTrans hs)

theorem prefix_base (E : PTm n) : Γ ⊢[PRAAx] newtonPrefix zero E := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,PTm.subst_zero] using
    base_law (Γ := lt (var 0) (succ (Syn.shift E)) :: Γ.map Fm.shift) (var 0)

theorem prefix_step (N E : PTm n) (h : Γ ⊢[PRAAx] newtonPrefix N E) : Γ ⊢[PRAAx] newtonPrefix (succ N) E := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] newtonPrefix (Syn.shift N) (Syn.shift E) := by
    simpa only [Fm.shift,subst_prefix,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift E)) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift E) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  refine .orE (zero_or_succ (var 0)) ?_ ?_
  · have z := law_transport (Γ := (var 0 ≐ zero) :: Δ) (succ (Syn.shift N)) (var 0) zero Prf.hyp0 (zero_law _)
    simpa only [Δ,Syn.shift,PTm.subst_succ] using z
  · have nextBound : ((var 0 ≐ succ (pred (var 0))) :: Δ) ⊢[PRAAx] le (succ (pred (var 0))) (Syn.shift E) :=
      le_congr Prf.hyp0 (.eqRefl _) bound.wk
    have oldNext := prefix_at (Syn.shift N) (Syn.shift E) (succ (pred (var 0))) hs.wk.wk nextBound
    have oldPrev := prefix_at (Syn.shift N) (Syn.shift E) (pred (var 0)) hs.wk.wk
      (le_trans (le_succ_self _) nextBound)
    have z := law_transport (succ (Syn.shift N)) (var 0) (succ (pred (var 0))) Prf.hyp0
      (positive_step _ _ oldNext oldPrev)
    simpa only [Δ,Syn.shift,PTm.subst_succ] using z

theorem original_finite_head_Newton (N s : PTm n) : Γ ⊢[PRAAx] law N s := by
  have all : Γ ⊢[PRAAx] .all (formula (prefixSyntax (var 0) (Syn.shift s))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [prefix_formula,subst_prefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_base (Γ := Γ) s
    · simpa only [prefix_formula,subst_prefix,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_step (Γ := formula (prefixSyntax (var 0) (Syn.shift s)) :: Γ.map Fm.shift)
          (var 0) (Syn.shift s) (by simpa only [prefix_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have result : Γ ⊢[PRAAx] newtonPrefix N s := by
    simpa only [prefix_formula,subst_prefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact prefix_at N s s result (le_refl s)

theorem original_Euler_head_actual_double_finite_convolution_Newton_identity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (newtonSum (var 0) (var 1) ≐ natScale (var 1) (reader (var 0) (succ (var 1)))) :=
  closeUniv 2 (original_finite_head_Newton _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadNewton

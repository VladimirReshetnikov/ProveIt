import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusHeight
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Actual bounded balanced-radius search

Each radius exponent runs an actual bounded coefficient search. Its
Boolean output is true exactly when all positive-degree coefficients fit.
An outer bounded first-failure search returns the preceding fitting
exponent and a literal failed coefficient from that same inner scan.
The endpoint success conditions are derived from the computed input
height, not included in the final source input contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSearch

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax
  (score cap fitAt numerator denominator input nonconstant)
open LeanProofs.IPRA.Foundations.BoundedSyntax

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fits (C N E j : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  fitAt (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j) (succ (var 0)))
def atomSyntax (C N E j h : PTm n) : BFm n := .le (score C N E j (succ h)) (cap C N E (succ h))
def atomF : PR 5 := bitF (atomSyntax (var 0) (var 1) (var 2) (var 3) (var 4))
def atom (C N E j h : PTm n) : PTm n := PTm.app atomF ![C,N,E,j,h]
def data (C N E : PTm n) : PTm n := pairT C (pairT N E)
def atomData (C N E j : PTm n) : PTm n := pairT (data C N E) j
def atomBody : PTm 2 := atom (fstT (fstT (var 1))) (fstT (sndT (fstT (var 1))))
  (sndT (sndT (fstT (var 1)))) (sndT (var 1)) (var 0)
def coefficientMu (C N E j : PTm n) : PTm n := Search.mu atomBody N (atomData C N E j)
def failedIndex (C N E j : PTm n) : PTm n := succ (coefficientMu C N E j)
def check (C N E j : PTm n) : PTm n := eqb (coefficientMu C N E j) N

ipra_subst fits [Syn.subst_shift, Syn.shift_subst]
ipra_subst atom
ipra_subst data
ipra_subst atomData
ipra_subst coefficientMu
ipra_subst failedIndex
ipra_subst check

theorem atom_program (C N E j h : PTm n) : Γ ⊢[PRAAx]
    atom C N E j h ≐ bit (atomSyntax (var 0) (var 1) (var 2) (var 3) (var 4) : BFm 5) ![C,N,E,j,h] :=
  program_correct _ _

theorem atom_reflection (C N E j h : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (atom C N E j h ≐ one) (fitAt C N E j (succ h)) := by
  have logical : Γ ⊢[PRAAx] Fm.iff
      (bit (atomSyntax (var 0) (var 1) (var 2) (var 3) (var 4) : BFm 5) ![C,N,E,j,h] ≐ one)
      (fitAt C N E j (succ h)) := by
    simpa only [atomSyntax,formula,BFm.le,Fm.subst_eq,PTm.subst_monus,ConciseIPRA.PTm.subst_zero,
      GaussianBalancedRadiusSyntax.fitAt,le,GaussianBalancedRadiusSyntax.subst_score,
      GaussianBalancedRadiusSyntax.subst_cap,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      bounded_reflection (Γ := Γ) (atomSyntax (var 0) (var 1) (var 2) (var 3) (var 4) : BFm 5) ![C,N,E,j,h]
  have program := atom_program (Γ := Γ) C N E j h
  exact .iffI (.impI (logical.wk.iffMp (program.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (program.wk.eqTrans (logical.wk.iffMpr Prf.hyp0)))

theorem atom_boolean (C N E j h : PTm n) : Γ ⊢[PRAAx] (atom C N E j h ≐ zero) ⋎ (atom C N E j h ≐ one) :=
  .orE (bit_cases (atomSyntax (var 0) (var 1) (var 2) (var 3) (var 4) : BFm 5) ![C,N,E,j,h])
    (.orI₁ ((atom_program C N E j h).wk.eqTrans Prf.hyp0))
    (.orI₂ ((atom_program C N E j h).wk.eqTrans Prf.hyp0))

theorem atom_congr {C C' N N' E E' j j' h h' : PTm n}
    (hc : Γ ⊢[PRAAx] C ≐ C') (hn : Γ ⊢[PRAAx] N ≐ N') (he : Γ ⊢[PRAAx] E ≐ E')
    (hj : Γ ⊢[PRAAx] j ≐ j') (hh : Γ ⊢[PRAAx] h ≐ h') : Γ ⊢[PRAAx]
    atom C N E j h ≐ atom C' N' E' j' h' := by
  ipra_congr (atom (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hc, hn, he, hj, hh]

theorem atom_body_at (C N E j h : PTm n) : Γ ⊢[PRAAx]
    inst2 atomBody h (atomData C N E j) ≐ atom C N E j h := by
  have head := fst_pair (Γ := Γ) (data C N E) j
  have c := (congrFst head).eqTrans (fst_pair C (pairT N E))
  have tail := (congrSnd head).eqTrans (snd_pair C (pairT N E))
  have nu := (congrFst tail).eqTrans (fst_pair N E)
  have ee := (congrSnd tail).eqTrans (snd_pair N E)
  simpa only [atomBody,atomData,inst2,subst_atom,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using atom_congr c nu ee (snd_pair _ _) (.eqRefl h)

theorem fits_at (C N E j h : PTm n) (hFits : Γ ⊢[PRAAx] fits C N E j) (hh : Γ ⊢[PRAAx] lt h N) : Γ ⊢[PRAAx]
    fitAt C N E j (succ h) := by
  have rule : Γ ⊢[PRAAx] lt h N ⟶ fitAt C N E j (succ h) := by
    simpa [fits] using hFits.allE h
  exact .impE rule hh

theorem coefficient_mu_bound (C N E j : PTm n) : Γ ⊢[PRAAx] le (coefficientMu C N E j) N :=
  Prf.andE₁ (Search.search_spec N zero (atomData C N E j))

theorem coefficient_mu_zero (C N E j : PTm n) (h : Γ ⊢[PRAAx] lt (coefficientMu C N E j) N) : Γ ⊢[PRAAx]
    atom C N E j (coefficientMu C N E j) ≐ zero :=
  (atom_body_at C N E j _).eqSymm.eqTrans (.impE (Prf.andE₁ (Prf.andE₂ (Search.search_spec N zero (atomData C N E j)))) h)

theorem fits_mu_limit (C N E j : PTm n) (h : Γ ⊢[PRAAx] fits C N E j) : Γ ⊢[PRAAx]
    coefficientMu C N E j ≐ N := by
  refine .orE (lt_or_eq_of_le (coefficient_mu_bound C N E j)) ?_ Prf.hyp0
  have yes : (lt (coefficientMu C N E j) N :: Γ) ⊢[PRAAx] atom C N E j (coefficientMu C N E j) ≐ one :=
    (atom_reflection C N E j (coefficientMu C N E j)).iffMpr
      (fits_at C N E j (coefficientMu C N E j) h.wk Prf.hyp0)
  exact .botE _ (succ_ne_zero (a := zero) (yes.eqSymm.eqTrans (coefficient_mu_zero C N E j Prf.hyp0)))

theorem mu_limit_fits (C N E j : PTm n) (h : Γ ⊢[PRAAx] coefficientMu C N E j ≐ N) : Γ ⊢[PRAAx] fits C N E j := by
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] coefficientMu (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j) ≐ Syn.shift N := by
    simpa only [Fm.shift,Fm.subst_eq,subst_coefficientMu,Syn.shift] using h.shift
  have earlier : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (coefficientMu (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j)) :=
    lt_congr (.eqRefl _) hs.wk.eqSymm Prf.hyp0
  have nonzero := Search.search_minimal (f := atomBody) (N := Syn.shift N)
    (x := atomData (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j)) earlier
  have result := Prf.orE (atom_boolean (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j) (var 0))
    (.botE _ (.impE nonzero.wk ((atom_body_at _ _ _ _ _).wk.eqTrans Prf.hyp0)))
    ((atom_reflection _ _ _ _ _).wk.wk.iffMp Prf.hyp0)
  simpa only [Syn.shift,GaussianBalancedRadiusSyntax.subst_fitAt] using result

theorem check_boolean (C N E j : PTm n) : Γ ⊢[PRAAx] (check C N E j ≐ zero) ⋎ (check C N E j ≐ one) :=
  .orE (eq_or_ne (coefficientMu C N E j) N) (.orI₂ (eqb_of_eq Prf.hyp0)) (.orI₁ (eqb_of_ne Prf.hyp0))

theorem check_reflection (C N E j : PTm n) : Γ ⊢[PRAAx] Fm.iff (check C N E j ≐ one) (fits C N E j) := by
  refine .iffI (.impI ?_) (.impI (eqb_of_eq (fits_mu_limit C N E j Prf.hyp0)))
  have equality : ((check C N E j ≐ one) :: Γ) ⊢[PRAAx] coefficientMu C N E j ≐ N := by
    refine .orE (eq_or_ne (coefficientMu C N E j) N) Prf.hyp0 ?_
    exact .botE _ (succ_ne_zero (a := zero) (Prf.hyp1.eqSymm.eqTrans (eqb_of_ne Prf.hyp0)))
  exact mu_limit_fits C N E j equality

theorem check_congr {C C' N N' E E' j j' : PTm n}
    (hc : Γ ⊢[PRAAx] C ≐ C') (hn : Γ ⊢[PRAAx] N ≐ N') (he : Γ ⊢[PRAAx] E ≐ E')
    (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] check C N E j ≐ check C' N' E' j' := by
  ipra_congr (check (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hc, hn, he, hj]

theorem atom_failed (C N E j h : PTm n) (hz : Γ ⊢[PRAAx] atom C N E j h ≐ zero) : Γ ⊢[PRAAx]
    lt (cap C N E (succ h)) (score C N E j (succ h)) := by
  refine .orE (lt_or_le (cap C N E (succ h)) (score C N E j (succ h))) Prf.hyp0 ?_
  have yes : (le (score C N E j (succ h)) (cap C N E (succ h)) :: Γ) ⊢[PRAAx] atom C N E j h ≐ one :=
    (atom_reflection C N E j h).iffMpr Prf.hyp0
  exact .botE _ (succ_ne_zero (a := zero) (yes.eqSymm.eqTrans hz.wk))

theorem coefficient_failure (C N E j : PTm n) (hz : Γ ⊢[PRAAx] check C N E j ≐ zero) : Γ ⊢[PRAAx]
    lt (coefficientMu C N E j) N ⋏ lt (cap C N E (failedIndex C N E j)) (score C N E j (failedIndex C N E j)) := by
  have range : Γ ⊢[PRAAx] lt (coefficientMu C N E j) N := by
    refine .orE (lt_or_eq_of_le (coefficient_mu_bound C N E j)) Prf.hyp0 ?_
    exact .botE _ (succ_ne_zero (a := zero) ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans hz.wk))
  exact .andI range (atom_failed C N E j _ (coefficient_mu_zero C N E j range))

theorem failed_numerator_positive (C N E j i : PTm n)
    (hf : Γ ⊢[PRAAx] lt (cap C N E i) (score C N E j i)) : Γ ⊢[PRAAx] le one (numerator C N i) := by
  refine .orE (zero_or_succ (numerator C N i)) ?_ ?_
  · have scoreZero : ((numerator C N i ≐ zero) :: Γ) ⊢[PRAAx] score C N E j i ≐ zero :=
      (congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)
    exact lt_zero_absurd _ (lt_congr (.eqRefl _) scoreZero hf.wk)
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

def firstBody : PTm 2 := check (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def first (C N E : PTm n) : PTm n := Search.mu firstBody (succ (two*E)) (data C N E)
def selected (C N E : PTm n) : PTm n := PTm.pred (first C N E)

ipra_subst first
ipra_subst selected

theorem first_body_at (C N E j : PTm n) : Γ ⊢[PRAAx] inst2 firstBody j (data C N E) ≐ check C N E j := by
  have tail := snd_pair (Γ := Γ) C (pairT N E)
  simpa only [firstBody,data,inst2,subst_check,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using check_congr (fst_pair _ _)
      tail.fstE tail.sndE (.eqRefl j)

theorem first_found (C N E : PTm n) (hHigh : Γ ⊢[PRAAx] check C N E (two*E) ≐ zero) : Γ ⊢[PRAAx]
    le (first C N E) (two*E) ⋏ check C N E (first C N E) ≐ zero := by
  have found := Search.search_found (N := succ (two*E)) ((first_body_at C N E (two*E)).eqTrans hHigh) (le_refl _)
  exact .andI (Prf.andE₂ (Prf.andE₂ found))
    ((first_body_at C N E _).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ found)))

theorem first_successor (C N E : PTm n) (hLow : Γ ⊢[PRAAx] check C N E zero ≐ one)
    (hHigh : Γ ⊢[PRAAx] check C N E (two*E) ≐ zero) : Γ ⊢[PRAAx] first C N E ≐ succ (selected C N E) := by
  have bad := Prf.andE₂ (first_found C N E hHigh)
  refine .orE (zero_or_succ (first C N E)) ?_ Prf.hyp0
  have atZero : ((first C N E ≐ zero) :: Γ) ⊢[PRAAx] check C N E zero ≐ zero :=
    (check_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (Prf.hyp0 : ((first C N E ≐ zero) :: Γ) ⊢[PRAAx] first C N E ≐ zero)).eqSymm.eqTrans bad.wk
  exact .botE _ (succ_ne_zero (a := zero) (hLow.wk.eqSymm.eqTrans atZero))

theorem before_first (C N E j : PTm n) (hj : Γ ⊢[PRAAx] lt j (first C N E)) : Γ ⊢[PRAAx] check C N E j ≐ one := by
  have minimal := Search.search_minimal (f := firstBody) (N := succ (two*E)) (x := data C N E) hj
  refine .orE (check_boolean C N E j) ?_ Prf.hyp0
  exact .botE _ (.impE minimal.wk ((first_body_at C N E j).wk.eqTrans Prf.hyp0))

theorem adjacent_checks (C N E : PTm n) (hLow : Γ ⊢[PRAAx] check C N E zero ≐ one)
    (hHigh : Γ ⊢[PRAAx] check C N E (two*E) ≐ zero) : Γ ⊢[PRAAx]
    lt (selected C N E) (two*E) ⋏ (check C N E (selected C N E) ≐ one ⋏ check C N E (succ (selected C N E)) ≐ zero) := by
  have found := first_found C N E hHigh
  have shape := first_successor C N E hLow hHigh
  have before : Γ ⊢[PRAAx] lt (selected C N E) (first C N E) :=
    lt_congr (.eqRefl _) shape.eqSymm (le_refl _)
  exact .andI (le_congr shape (.eqRefl _) (Prf.andE₁ found))
    (.andI (before_first C N E _ before)
      ((check_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) shape).eqSymm.eqTrans (Prf.andE₂ found)))

theorem fits_degree_at (C N E j i : PTm n) (hFits : Γ ⊢[PRAAx] fits C N E j)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] fitAt C N E j i := by
  have shape := RationalIntegerNormalization.positive_form hi
  have inside : Γ ⊢[PRAAx] lt (PTm.pred i) N := le_congr shape (.eqRefl _) hiN
  have result := fits_at C N E j (PTm.pred i) hFits inside
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (fitAt (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![C,N,E,j,succ (PTm.pred i)] ![C,N,E,j,i]
    (fun q => by fin_cases q; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact shape.eqSymm)
    (by simpa using result)
  simpa using p

theorem fits_monotone (C N E j k : PTm n) (hjk : Γ ⊢[PRAAx] le j k)
    (hk : Γ ⊢[PRAAx] fits C N E k) : Γ ⊢[PRAAx] fits C N E j := by
  refine .allI (.impI ?_)
  have order : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift j) (Syn.shift k) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hjk.shift
  have all : Γ.map Fm.shift ⊢[PRAAx] fits (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift k) := by
    simpa only [Fm.shift,subst_fits,Syn.shift] using hk.shift
  simpa only [Syn.shift,GaussianBalancedRadiusSyntax.subst_fitAt] using
    GaussianBalancedRadiusArithmetic.fitAt_monotone (Syn.shift C) (Syn.shift N) (Syn.shift E) (Syn.shift j) (Syn.shift k) (succ (var 0))
      order.wk (fits_at _ _ _ _ (var 0) all.wk Prf.hyp0)

def greatest (C N E j : PTm n) : Fm PTm n := .all (fits (Syn.shift C) (Syn.shift N) (Syn.shift E) (var 0) ⟶ le (var 0) (Syn.shift j))
ipra_subst greatest [Syn.subst_shift, Syn.shift_subst]

theorem fits_upper_bound (C N E k : PTm n) (hLow : Γ ⊢[PRAAx] check C N E zero ≐ one)
    (hHigh : Γ ⊢[PRAAx] check C N E (two*E) ≐ zero) (hk : Γ ⊢[PRAAx] fits C N E k) : Γ ⊢[PRAAx]
    le k (selected C N E) := by
  have bad := Prf.andE₂ (Prf.andE₂ (adjacent_checks C N E hLow hHigh))
  refine .orE (lt_or_le (selected C N E) k) ?_ Prf.hyp0
  have yes : ((lt (selected C N E) k) :: Γ) ⊢[PRAAx] check C N E (succ (selected C N E)) ≐ one :=
    (check_reflection _ _ _ _).iffMpr (fits_monotone C N E _ _ Prf.hyp0 hk.wk)
  exact .botE _ (succ_ne_zero (a := zero) (yes.eqSymm.eqTrans bad.wk))

theorem greatest_from_endpoints (C N E : PTm n) (hLow : Γ ⊢[PRAAx] check C N E zero ≐ one)
    (hHigh : Γ ⊢[PRAAx] check C N E (two*E) ≐ zero) : Γ ⊢[PRAAx] greatest C N E (selected C N E) := by
  refine .allI (.impI ?_)
  have low : Γ.map Fm.shift ⊢[PRAAx] check (Syn.shift C) (Syn.shift N) (Syn.shift E) zero ≐ one := by
    simpa only [Fm.shift,Fm.subst_eq,subst_check,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hLow.shift
  have high : Γ.map Fm.shift ⊢[PRAAx] check (Syn.shift C) (Syn.shift N) (Syn.shift E) (two*Syn.shift E) ≐ zero := by
    simpa only [Fm.shift,Fm.subst_eq,subst_check,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hHigh.shift
  simpa only [Syn.shift,subst_selected] using fits_upper_bound (Syn.shift C) (Syn.shift N) (Syn.shift E) (var 0) low.wk high.wk Prf.hyp0

/-! The final input producer derives its scan endpoints from the actual
finite input height. No endpoint or successful search is a source premise. -/
def radiusIndex (C N : PTm n) : PTm n := selected C N (GaussianBalancedRadiusHeight.E C N)
def witness (C N : PTm n) : PTm n := failedIndex C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N))

ipra_subst radiusIndex
ipra_subst witness

theorem initial_fits (C N : PTm n) (hn0 : Γ ⊢[PRAAx] le one (numerator C N zero)) : Γ ⊢[PRAAx]
    fits C N (GaussianBalancedRadiusHeight.E C N) zero := by
  refine .allI (.impI ?_)
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (numerator (Syn.shift C) (Syn.shift N) zero) := by
    simpa only [Fm.shift,subst_le,GaussianBalancedRadiusSyntax.subst_numerator,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hn0.shift
  have actual := GaussianBalancedRadiusArithmetic.low_fit (Syn.shift C) (Syn.shift N)
    (GaussianBalancedRadiusHeight.b (Syn.shift C) (Syn.shift N)) (succ (var 0))
    (GaussianBalancedRadiusHeight.numerator_bound _ _ _ Prf.hyp0)
    (GaussianBalancedRadiusHeight.denominator_bound _ _ zero (zero_le _)) positive.wk (zero_lt_succ (var 0))
  simpa only [Syn.shift,GaussianBalancedRadiusHeight.subst_E,ConciseIPRA.PTm.subst_zero,
    GaussianBalancedRadiusHeight.E,GaussianBalancedRadiusArithmetic.exponent,PTm.subst_add,PTm.subst_mul,
    GaussianBalancedRadiusHeight.subst_b,GaussianBalancedRadiusSyntax.subst_three,ConciseIPRA.PTm.subst_succ,
    lt,two,one] using actual

theorem terminal_not_fits (C N : PTm n) (hNonconstant : Γ ⊢[PRAAx] nonconstant C N) : Γ ⊢[PRAAx]
    neg (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N)) := by
  refine .impI (.exE hNonconstant.wk ?_)
  let P : Fm PTm (n+1) := le one (var 0) ⋏ (le (var 0) (Syn.shift N) ⋏ le one (numerator (Syn.shift C) (Syn.shift N) (var 0)))
  have hi : P :: (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) :: Γ).map Fm.shift ⊢[PRAAx]
      le one (var 0) := Prf.andE₁ Prf.hyp0
  have hiN := Prf.andE₁ (Prf.andE₂ (Prf.hyp0 : P :: (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) :: Γ).map Fm.shift ⊢[PRAAx] P))
  have hni := Prf.andE₂ (Prf.andE₂ (Prf.hyp0 : P :: (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) :: Γ).map Fm.shift ⊢[PRAAx] P))
  have bad := GaussianBalancedRadiusArithmetic.high_fail (Syn.shift C) (Syn.shift N)
    (GaussianBalancedRadiusHeight.b (Syn.shift C) (Syn.shift N)) (var 0)
    (GaussianBalancedRadiusHeight.numerator_bound _ _ zero (zero_le _))
    (GaussianBalancedRadiusHeight.denominator_bound _ _ _ hiN) hni hi
  have all : P :: (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) :: Γ).map Fm.shift ⊢[PRAAx]
      fits (Syn.shift C) (Syn.shift N) (GaussianBalancedRadiusHeight.E (Syn.shift C) (Syn.shift N))
        (two*GaussianBalancedRadiusHeight.E (Syn.shift C) (Syn.shift N)) := by
    simpa only [P,List.map_cons,Fm.shift,subst_fits,GaussianBalancedRadiusHeight.subst_E,PTm.subst_mul,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using (Prf.hyp1 : P ::
      (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) :: Γ).map Fm.shift ⊢[PRAAx]
        Fm.shift (fits C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N)))
  have yes := fits_degree_at _ _ _ _ (var 0) all hi hiN
  exact lt_irrefl _ _ (lt_of_lt_of_le bad yes)

theorem endpoint_checks (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    check C N (GaussianBalancedRadiusHeight.E C N) zero ≐ one ⋏
      check C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N) ≐ zero := by
  have hn0 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have nc := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  refine .andI ((check_reflection _ _ _ _).iffMpr (initial_fits C N hn0)) ?_
  refine .orE (check_boolean C N (GaussianBalancedRadiusHeight.E C N) (two*GaussianBalancedRadiusHeight.E C N)) Prf.hyp0 ?_
  exact .botE _ (.impE (terminal_not_fits C N nc).wk ((check_reflection _ _ _ _).wk.iffMp Prf.hyp0))

theorem selected_fits (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    fits C N (GaussianBalancedRadiusHeight.E C N) (radiusIndex C N) := by
  have ends := endpoint_checks C N h
  exact (check_reflection _ _ _ _).iffMp (Prf.andE₁ (Prf.andE₂ (adjacent_checks C N _ (Prf.andE₁ ends) (Prf.andE₂ ends))))

theorem next_not_fits (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    neg (fits C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N))) := by
  have ends := endpoint_checks C N h
  have bad := Prf.andE₂ (Prf.andE₂ (adjacent_checks C N _ (Prf.andE₁ ends) (Prf.andE₂ ends)))
  refine .impI ?_
  have yes : (fits C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N)) :: Γ) ⊢[PRAAx]
      check C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N)) ≐ one :=
    (check_reflection C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N))).iffMpr Prf.hyp0
  exact succ_ne_zero (a := zero) (yes.eqSymm.eqTrans bad.wk)

theorem witness_spec (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    le one (witness C N) ⋏ (le (witness C N) N ⋏ (le one (numerator C N (witness C N)) ⋏
      lt (cap C N (GaussianBalancedRadiusHeight.E C N) (witness C N))
        (score C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N)) (witness C N)))) := by
  have ends := endpoint_checks C N h
  have bad := Prf.andE₂ (Prf.andE₂ (adjacent_checks C N _ (Prf.andE₁ ends) (Prf.andE₂ ends)))
  have actual := coefficient_failure C N (GaussianBalancedRadiusHeight.E C N) (succ (radiusIndex C N)) bad
  exact .andI (zero_lt_succ _) (.andI (Prf.andE₁ actual)
    (.andI (failed_numerator_positive _ _ _ _ _ (Prf.andE₂ actual)) (Prf.andE₂ actual)))

theorem greatest_fitting (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    greatest C N (GaussianBalancedRadiusHeight.E C N) (radiusIndex C N) :=
  greatest_from_endpoints C N _ (Prf.andE₁ (endpoint_checks C N h)) (Prf.andE₂ (endpoint_checks C N h))

def certificate (C N j i : PTm n) : Fm PTm n :=
  lt j (two*GaussianBalancedRadiusHeight.E C N) ⋏
    (fits C N (GaussianBalancedRadiusHeight.E C N) j ⋏
      ((le one i ⋏ (le i N ⋏ (le one (numerator C N i) ⋏
          lt (cap C N (GaussianBalancedRadiusHeight.E C N) i) (score C N (GaussianBalancedRadiusHeight.E C N) (succ j) i)))) ⋏
        greatest C N (GaussianBalancedRadiusHeight.E C N) j))
ipra_subst certificate

theorem search_correct (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    certificate C N (radiusIndex C N) (witness C N) := by
  have ends := endpoint_checks C N h
  exact .andI (Prf.andE₁ (adjacent_checks C N _ (Prf.andE₁ ends) (Prf.andE₂ ends)))
    (.andI (selected_fits C N h) (.andI (witness_spec C N h) (greatest_fitting C N h)))

theorem greatest_at (C N E j k : PTm n) (hg : Γ ⊢[PRAAx] greatest C N E j)
    (hk : Γ ⊢[PRAAx] fits C N E k) : Γ ⊢[PRAAx] le k j := by
  have rule : Γ ⊢[PRAAx] fits C N E k ⟶ le k j := by simpa [greatest] using hg.allE k
  exact .impE rule hk

def checkF : PR 4 := PTm.toPR (check (var 0) (var 1) (var 2) (var 3))
def output (C N : PTm n) : PTm n := pairT (radiusIndex C N) (pairT (witness C N) (GaussianBalancedRadiusHeight.E C N))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

ipra_subst output
ipra_subst run

theorem check_program (C N E j : PTm n) : Γ ⊢[PRAAx]
    PTm.app checkF ![C,N,E,j] ≐ check C N E j := by
  simpa only [checkF,subst_check,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (check (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,N,E,j]

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_index (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ radiusIndex C N :=
  (program_at C N).fstE
theorem returned_witness (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ witness C N :=
  (program_at C N).sndE.fstE
theorem returned_exponent (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run C N)) ≐ GaussianBalancedRadiusHeight.E C N :=
  (program_at C N).sndE.sndE

theorem returned_certificate (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    certificate C N (fstT (run C N)) (fstT (sndT (run C N))) := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (certificate (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![C,N,radiusIndex C N,witness C N] ![C,N,fstT (run C N),fstT (sndT (run C N))]
    (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact (returned_index C N).eqSymm; exact (returned_witness C N).eqSymm)
    (by simpa using search_correct C N h)
  simpa using p

theorem positive_degree_scan_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (check (var 0) (var 1) (var 2) (var 3) ≐ one) (fits (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (check_reflection _ _ _ _)

theorem fit_degree_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (fits (var 0) (var 1) (var 2) (var 3) ⟶ le one (var 4) ⟶ le (var 4) (var 1) ⟶
      fitAt (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (fits_degree_at _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem balanced_radius_search_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ certificate (var 0) (var 1) (radiusIndex (var 0) (var 1)) (witness (var 0) (var 1))) :=
  closeUniv 2 (.impI (search_correct _ _ Prf.hyp0))

theorem returned_balanced_radius_search_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ certificate (var 0) (var 1) (fstT (run (var 0) (var 1))) (fstT (sndT (run (var 0) (var 1))))) :=
  closeUniv 2 (.impI (returned_certificate _ _ Prf.hyp0))

theorem balanced_scan_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app checkF ![var 0,var 1,var 2,var 3] ≐ check (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (check_program _ _ _ _)

theorem balanced_search_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem balanced_search_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sndT (sndT (run (var 0) (var 1))) ≐ GaussianBalancedRadiusHeight.E (var 0) (var 1)) :=
  closeUniv 2 (returned_exponent _ _)

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSearch

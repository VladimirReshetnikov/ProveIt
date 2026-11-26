import IPRADerivations.Analysis.Exponential.GaussianRationalFiniteExponentialEuler
import IPRADerivations.Foundations.BoundedSyntaxInduction

/-!
# Uniqueness for an actual finite coefficient recursion

The recursion reads the original stored coefficient buffers and sums only
previous coefficients. Positive numerical Euler multipliers cancel by a
constructed rational inverse. A compiled bounded prefix invariant proves
uniqueness; no ambient formal-power-series or host recursion theorem is
used. All coefficient widths, horizons, data and indices are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCoefficientRecursion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul canonical ofGaussian represents canonical_unique)
open GaussianRationalSyntheticDivision (qone qmul_congr canonicalCoefficients rescale_to)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient getP getQ getN getM getE data)
open GaussianRationalFiniteSum (sum)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inversePoint (t : PTm n) : PTm n := ofGaussian ComplexLogarithmRemainder.oneCode t
@[simp] theorem subst_inversePoint {l : ℕ} (σ : Fin n → PTm l) (t : PTm n) :
    Syn.subst σ (inversePoint t) = inversePoint (Syn.subst σ t) := by simp [inversePoint]

theorem inverse_multiplier (t : PTm n) (ht : Γ ⊢[PRAAx] le one t) : Γ ⊢[PRAAx]
    qmul (inversePoint t) (naturalPoint t) ≐ qone := by
  have left := GaussianRationalHorner.qmul_represents (Γ := Γ) _ _ _ _ _ _ ht (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents ComplexLogarithmRemainder.oneCode t ht)
    (GaussianRationalNaturalScale.natural_point_represents t)
  have right : Γ ⊢[PRAAx] represents qone (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode) t :=
    rescale_to _ _ one t t (GaussianRationalHorner.ofGaussian_represents _ one (le_refl one)) (one_mul t)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul ComplexLogarithmRemainder.oneCode
        (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode))
      (ComplexLogarithmRemainder.scale t ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    GaussianRationalSyntheticDivision.qone_canonical ht
    (GaussianRationalHorner.represents_congr (.eqRefl _) native (by ipra_ring) left) right

theorem scale_recovery (t q : PTm n) (ht : Γ ⊢[PRAAx] le one t) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    qmul (inversePoint t) (natScale t q) ≐ q :=
  (qmul_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_as_product t q)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (inverse_multiplier t ht) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right q hq))))

theorem scale_cancel (t q r : PTm n) (ht : Γ ⊢[PRAAx] le one t) (hq : Γ ⊢[PRAAx] canonical q)
    (hr : Γ ⊢[PRAAx] canonical r) (h : Γ ⊢[PRAAx] natScale t q ≐ natScale t r) : Γ ⊢[PRAAx] q ≐ r :=
  (scale_recovery t q ht hq).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans (scale_recovery t r ht hr))

def priorTerm (P D C B e j : PTm n) : PTm n :=
  qmul (exponentCoefficient C B j) (exponentCoefficient P D (monus e j))
def priorBody : PTm 2 := priorTerm (getP (var 1)) (getN (var 1)) (getQ (var 1)) (getM (var 1)) (getE (var 1)) (var 0)
def priorSum (P D C B e : PTm n) : PTm n := sum priorBody e (data P C D B e)
@[simp] theorem subst_priorTerm {l : ℕ} (σ : Fin n → PTm l) (P D C B e j : PTm n) :
    Syn.subst σ (priorTerm P D C B e j) = priorTerm (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ C)
      (Syn.subst σ B) (Syn.subst σ e) (Syn.subst σ j) := by simp [priorTerm]
@[simp] theorem subst_priorSum {l : ℕ} (σ : Fin n → PTm l) (P D C B e : PTm n) :
    Syn.subst σ (priorSum P D C B e) = priorSum (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ e) := by simp [priorSum]
theorem prior_at (P D C B e j : PTm n) : Γ ⊢[PRAAx]
    inst2 priorBody j (data P C D B e) ≐ priorTerm P D C B e j := by
  simp only [priorBody,inst2,subst_priorTerm,GaussianRationalLowCoefficientConvolution.getP,
    GaussianRationalLowCoefficientConvolution.getQ,GaussianRationalLowCoefficientConvolution.getN,
    GaussianRationalLowCoefficientConvolution.getM,GaussianRationalLowCoefficientConvolution.getE,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact qmul_congr
    (GaussianRationalPolynomialExponentialStability.exponent_congr
      (GaussianRationalLowCoefficientConvolution.get_q _ _ _ _ _) (GaussianRationalLowCoefficientConvolution.get_m _ _ _ _ _) (.eqRefl _))
    (GaussianRationalPolynomialExponentialStability.exponent_congr
      (GaussianRationalLowCoefficientConvolution.get_p _ _ _ _ _) (GaussianRationalLowCoefficientConvolution.get_n _ _ _ _ _)
      (congrMonus (GaussianRationalLowCoefficientConvolution.get_e _ _ _ _ _) (.eqRefl _)))

def recursion (P D C B R : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift R)) ⟶ natScale (var 0) (exponentCoefficient (Syn.shift C) (Syn.shift B) (var 0)) ≐
    priorSum (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B) (var 0))
def prefixEqual (C B F E r : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift r)) ⟶ exponentCoefficient (Syn.shift C) (Syn.shift B) (var 0) ≐
    exponentCoefficient (Syn.shift F) (Syn.shift E) (var 0))
@[simp] theorem subst_recursion {l : ℕ} (σ : Fin n → PTm l) (P D C B R : PTm n) :
    (recursion P D C B R).subst σ = recursion (Syn.subst σ P) (Syn.subst σ D)
      (Syn.subst σ C) (Syn.subst σ B) (Syn.subst σ R) := by simp [recursion,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_prefixEqual {l : ℕ} (σ : Fin n → PTm l) (C B F E r : PTm n) :
    (prefixEqual C B F E r).subst σ = prefixEqual (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ F) (Syn.subst σ E) (Syn.subst σ r) := by simp [prefixEqual,Syn.subst_shift,Syn.shift_subst]

theorem recursion_at (P D C B R e : PTm n) (h : Γ ⊢[PRAAx] recursion P D C B R)
    (he : Γ ⊢[PRAAx] le e R) : Γ ⊢[PRAAx]
    natScale e (exponentCoefficient C B e) ≐ priorSum P D C B e := by
  have gate : Γ ⊢[PRAAx] lt e (succ R) ⟶ natScale e (exponentCoefficient C B e) ≐ priorSum P D C B e := by
    simpa [recursion] using h.allE e
  exact .impE gate ((succ_monus_succ _ _).eqTrans he)
theorem prefix_at (C B F E r i : PTm n) (h : Γ ⊢[PRAAx] prefixEqual C B F E r)
    (hi : Γ ⊢[PRAAx] le i r) : Γ ⊢[PRAAx] exponentCoefficient C B i ≐ exponentCoefficient F E i := by
  have gate : Γ ⊢[PRAAx] lt i (succ r) ⟶ exponentCoefficient C B i ≐ exponentCoefficient F E i := by
    simpa [prefixEqual] using h.allE i
  exact .impE gate ((succ_monus_succ _ _).eqTrans hi)

theorem prefix_zero (C B F E : PTm n) (h0 : Γ ⊢[PRAAx]
    exponentCoefficient C B zero ≐ exponentCoefficient F E zero) : Γ ⊢[PRAAx] prefixEqual C B F E zero := by
  have hs : Γ.map Fm.shift ⊢[PRAAx]
      exponentCoefficient (Syn.shift C) (Syn.shift B) zero ≐ exponentCoefficient (Syn.shift F) (Syn.shift E) zero := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,ConciseIPRA.PTm.subst_zero,Syn.shift] using h0.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (zero : PTm (n+1))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) zero := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have iz : Δ ⊢[PRAAx] (var 0) ≐ zero := le_antisymm hi (zero_le _)
  have result := (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) iz).eqTrans
    (hs.wk.eqTrans (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) iz.eqSymm))
  simpa only [Δ,Syn.shift,ConciseIPRA.PTm.subst_zero] using result

theorem prior_sum_congr (P D C B F E r : PTm n) (h : Γ ⊢[PRAAx] prefixEqual C B F E r) : Γ ⊢[PRAAx]
    priorSum P D C B (succ r) ≐ priorSum P D F E (succ r) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] prefixEqual (Syn.shift C) (Syn.shift B) (Syn.shift F) (Syn.shift E) (Syn.shift r) := by
    simpa only [Fm.shift,subst_prefixEqual,Syn.shift] using h.shift
  refine GaussianRationalFiniteSum.sum_congr_bounded priorBody priorBody (succ r)
    (data P C D B (succ r)) (data P F D E (succ r)) (.allI (.impI ?_))
  let Δ := lt (var 0) (succ (Syn.shift r)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift r) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have termEq : Δ ⊢[PRAAx] priorTerm (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B) (succ (Syn.shift r)) (var 0) ≐
      priorTerm (Syn.shift P) (Syn.shift D) (Syn.shift F) (Syn.shift E) (succ (Syn.shift r)) (var 0) :=
    qmul_congr (prefix_at _ _ _ _ _ _ hs.wk hi) (.eqRefl _)
  have result := (prior_at (Γ := Δ) (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B) (succ (Syn.shift r)) (var 0)).eqTrans
    (termEq.eqTrans (prior_at (Syn.shift P) (Syn.shift D) (Syn.shift F) (Syn.shift E) (succ (Syn.shift r)) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalLowCoefficientConvolution.subst_data,ConciseIPRA.PTm.subst_succ] using result

theorem next_coefficient (P D C B F E R r : PTm n)
    (hLC : Γ ⊢[PRAAx] length C ≐ succ B) (hC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hLF : Γ ⊢[PRAAx] length F ≐ succ E) (hF : Γ ⊢[PRAAx] canonicalCoefficients F)
    (hRecC : Γ ⊢[PRAAx] recursion P D C B R) (hRecF : Γ ⊢[PRAAx] recursion P D F E R)
    (hOld : Γ ⊢[PRAAx] prefixEqual C B F E r) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    exponentCoefficient C B (succ r) ≐ exponentCoefficient F E (succ r) :=
  scale_cancel (succ r) _ _ (zero_lt_succ r)
    (GaussianRationalPolynomialExponentialCoefficients.exponent_canonical _ _ _ hC hLC)
    (GaussianRationalPolynomialExponentialCoefficients.exponent_canonical _ _ _ hF hLF)
    ((recursion_at P D C B R (succ r) hRecC hr).eqTrans
      ((prior_sum_congr P D C B F E r hOld).eqTrans (recursion_at P D F E R (succ r) hRecF hr).eqSymm))

theorem prefix_extend (C B F E r : PTm n) (hOld : Γ ⊢[PRAAx] prefixEqual C B F E r)
    (hNew : Γ ⊢[PRAAx] exponentCoefficient C B (succ r) ≐ exponentCoefficient F E (succ r)) :
    Γ ⊢[PRAAx] prefixEqual C B F E (succ r) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] prefixEqual (Syn.shift C) (Syn.shift B) (Syn.shift F) (Syn.shift E) (Syn.shift r) := by
    simpa only [Fm.shift,subst_prefixEqual,Syn.shift] using hOld.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] exponentCoefficient (Syn.shift C) (Syn.shift B) (succ (Syn.shift r)) ≐
      exponentCoefficient (Syn.shift F) (Syn.shift E) (succ (Syn.shift r)) := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalLowCoefficientConvolution.subst_exponentCoefficient,ConciseIPRA.PTm.subst_succ,Syn.shift] using hNew.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (succ (Syn.shift r))) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (succ (Syn.shift r)) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  refine .orE (lt_or_eq_of_le hi) ?_ ?_
  · exact prefix_at _ _ _ _ _ _ hs.wk.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  · exact (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqTrans
      (hn.wk.wk.eqTrans (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) Prf.hyp0.eqSymm))

def uniqueLaw (_P _D C B F E R r : PTm n) : Fm PTm n := le r R ⟶ prefixEqual C B F E r
def prefixSyntax (C B F E r : PTm n) : BFm n := .all (succ r) (.eq
  (exponentCoefficient (Syn.shift C) (Syn.shift B) (var 0)) (exponentCoefficient (Syn.shift F) (Syn.shift E) (var 0)))
def uniqueSyntax (_P _D C B F E R r : PTm n) : BFm n := .imp (.le r R) (prefixSyntax C B F E r)
@[simp] theorem subst_uniqueLaw {l : ℕ} (σ : Fin n → PTm l) (P D C B F E R r : PTm n) :
    (uniqueLaw P D C B F E R r).subst σ = uniqueLaw (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ F) (Syn.subst σ E) (Syn.subst σ R) (Syn.subst σ r) := by simp [uniqueLaw]
theorem prefix_formula (C B F E r : PTm n) : formula (prefixSyntax C B F E r) = prefixEqual C B F E r := by
  simp [prefixSyntax,prefixEqual,formula]
theorem unique_formula (P D C B F E R r : PTm n) : formula (uniqueSyntax P D C B F E R r) = uniqueLaw P D C B F E R r := by
  simp [uniqueSyntax,uniqueLaw,prefix_formula,formula,BFm.le,le]

theorem unique_base (P D C B F E R : PTm n)
    (h0 : Γ ⊢[PRAAx] exponentCoefficient C B zero ≐ exponentCoefficient F E zero) :
    Γ ⊢[PRAAx] uniqueLaw P D C B F E R zero := .impI (prefix_zero C B F E h0.wk)
theorem unique_step (P D C B F E R r : PTm n)
    (hLC : Γ ⊢[PRAAx] length C ≐ succ B) (hC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hLF : Γ ⊢[PRAAx] length F ≐ succ E) (hF : Γ ⊢[PRAAx] canonicalCoefficients F)
    (hRecC : Γ ⊢[PRAAx] recursion P D C B R) (hRecF : Γ ⊢[PRAAx] recursion P D F E R)
    (ih : Γ ⊢[PRAAx] uniqueLaw P D C B F E R r) : Γ ⊢[PRAAx] uniqueLaw P D C B F E R (succ r) := by
  refine .impI ?_
  have hPrev : (le (succ r) R :: Γ) ⊢[PRAAx] le r R := le_trans (le_succ_self r) Prf.hyp0
  have hOld := Prf.impE ih.wk hPrev
  exact prefix_extend C B F E r hOld
    (next_coefficient P D C B F E R r hLC.wk hC.wk hLF.wk hF.wk hRecC.wk hRecF.wk hOld Prf.hyp0)

theorem uniqueness (P D C B F E R : PTm n)
    (hLC : Γ ⊢[PRAAx] length C ≐ succ B) (hC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hLF : Γ ⊢[PRAAx] length F ≐ succ E) (hF : Γ ⊢[PRAAx] canonicalCoefficients F)
    (hRecC : Γ ⊢[PRAAx] recursion P D C B R) (hRecF : Γ ⊢[PRAAx] recursion P D F E R)
    (h0 : Γ ⊢[PRAAx] exponentCoefficient C B zero ≐ exponentCoefficient F E zero) :
    Γ ⊢[PRAAx] prefixEqual C B F E R := by
  have lc := GaussianRationalPolynomialPowerEuler.shift_length C B hLC
  have lf := GaussianRationalPolynomialPowerEuler.shift_length F E hLF
  have cc : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hC.shift
  have cf : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift F) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hF.shift
  have rc : Γ.map Fm.shift ⊢[PRAAx] recursion (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B) (Syn.shift R) := by
    simpa only [Fm.shift,subst_recursion,Syn.shift] using hRecC.shift
  have rf : Γ.map Fm.shift ⊢[PRAAx] recursion (Syn.shift P) (Syn.shift D) (Syn.shift F) (Syn.shift E) (Syn.shift R) := by
    simpa only [Fm.shift,subst_recursion,Syn.shift] using hRecF.shift
  have all : Γ ⊢[PRAAx] .all (formula (uniqueSyntax (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B)
      (Syn.shift F) (Syn.shift E) (Syn.shift R) (var 0))) := by
    refine Foundations.BoundedSyntaxInduction.induction _ ?_ ?_
    · simpa only [unique_formula,subst_uniqueLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        unique_base (Γ := Γ) P D C B F E R h0
    · simpa only [unique_formula,subst_uniqueLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        unique_step (Γ := formula (uniqueSyntax (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B)
          (Syn.shift F) (Syn.shift E) (Syn.shift R) (var 0)) :: Γ.map Fm.shift)
          (Syn.shift P) (Syn.shift D) (Syn.shift C) (Syn.shift B) (Syn.shift F) (Syn.shift E) (Syn.shift R) (var 0)
          lc.wk cc.wk lf.wk cf.wk rc.wk rf.wk (by simpa only [unique_formula] using (Prf.hyp0 (Ax := PRAAx)))
  have gate : Γ ⊢[PRAAx] uniqueLaw P D C B F E R R := by
    simpa only [unique_formula,subst_uniqueLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE R
  exact .impE gate (le_refl R)

def input (P D C B F E R : PTm n) : Fm PTm n :=
  (length C ≐ succ B ⋏ canonicalCoefficients C) ⋏
  ((length F ≐ succ E ⋏ canonicalCoefficients F) ⋏
    (recursion P D C B R ⋏ (recursion P D F E R ⋏ exponentCoefficient C B zero ≐ exponentCoefficient F E zero)))
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (P D C B F E R : PTm n) :
    (input P D C B F E R).subst σ = input (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ F) (Syn.subst σ E) (Syn.subst σ R) := by simp [input]
theorem unique_of_input (P D C B F E R : PTm n) (h : Γ ⊢[PRAAx] input P D C B F E R) :
    Γ ⊢[PRAAx] prefixEqual C B F E R :=
  uniqueness P D C B F E R (Prf.andE₁ (Prf.andE₁ h)) (Prf.andE₂ (Prf.andE₁ h))
    (Prf.andE₁ (Prf.andE₁ (Prf.andE₂ h))) (Prf.andE₂ (Prf.andE₁ (Prf.andE₂ h)))
    (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))
theorem coefficient_unique (P D C B F E R i : PTm n) (h : Γ ⊢[PRAAx] input P D C B F E R)
    (hi : Γ ⊢[PRAAx] le i R) : Γ ⊢[PRAAx] exponentCoefficient C B i ≐ exponentCoefficient F E i :=
  prefix_at C B F E R i (unique_of_input P D C B F E R h) hi

def inverseF : PR 1 := PTm.toPR (inversePoint (var 0))
def priorF : PR 5 := PTm.toPR (priorSum (var 0) (var 1) (var 2) (var 3) (var 4))
def comparison (C B F E i : PTm n) : PTm n := pairT (exponentCoefficient C B i) (exponentCoefficient F E i)
def comparisonF : PR 5 := PTm.toPR (comparison (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C B F E i : PTm n) : PTm n := PTm.app comparisonF ![C,B,F,E,i]
@[simp] theorem subst_comparison {l : ℕ} (σ : Fin n → PTm l) (C B F E i : PTm n) :
    Syn.subst σ (comparison C B F E i) = comparison (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ F) (Syn.subst σ E) (Syn.subst σ i) := by simp [comparison]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (C B F E i : PTm n) :
    Syn.subst σ (run C B F E i) = run (Syn.subst σ C) (Syn.subst σ B)
      (Syn.subst σ F) (Syn.subst σ E) (Syn.subst σ i) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem inverse_program_at (t : PTm n) : Γ ⊢[PRAAx] ap1 inverseF t ≐ inversePoint t := by
  simpa [inverseF,ap1] using toPR_eq (Γ := Γ) (inversePoint (var 0) : PTm 1) ![t]
theorem prior_program_at (P D C B e : PTm n) : Γ ⊢[PRAAx] PTm.app priorF ![P,D,C,B,e] ≐ priorSum P D C B e := by
  simpa [priorF] using toPR_eq (Γ := Γ) (priorSum (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,D,C,B,e]
theorem program_at (C B F E i : PTm n) : Γ ⊢[PRAAx] run C B F E i ≐ comparison C B F E i := by
  simpa [run,comparisonF] using toPR_eq (Γ := Γ) (comparison (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,B,F,E,i]
theorem returned_left (C B F E i : PTm n) : Γ ⊢[PRAAx] fstT (run C B F E i) ≐ exponentCoefficient C B i :=
  (congrFst (program_at C B F E i)).eqTrans (fst_pair _ _)
theorem returned_right (C B F E i : PTm n) : Γ ⊢[PRAAx] sndT (run C B F E i) ≐ exponentCoefficient F E i :=
  (congrSnd (program_at C B F E i)).eqTrans (snd_pair _ _)
theorem returned_agreement (P D C B F E R i : PTm n) (h : Γ ⊢[PRAAx] input P D C B F E R)
    (hi : Γ ⊢[PRAAx] le i R) : Γ ⊢[PRAAx] fstT (run C B F E i) ≐ sndT (run C B F E i) :=
  (returned_left C B F E i).eqTrans ((coefficient_unique P D C B F E R i h hi).eqTrans (returned_right C B F E i).eqSymm)

theorem actual_positive_scale_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ qmul (inversePoint (var 0)) (naturalPoint (var 0)) ≐ qone) :=
  closeUniv 1 (.impI (inverse_multiplier _ Prf.hyp0))
theorem actual_positive_scale_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ canonical (var 1) ⟶ canonical (var 2) ⟶
      natScale (var 0) (var 1) ≐ natScale (var 0) (var 2) ⟶ (var 1) ≐ (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (scale_cancel _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_prior_coefficient_sum_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (canonical (priorSum (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem actual_bounded_coefficient_recursion_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      prefixEqual (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (unique_of_input _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_coefficient_recursion_unique_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (var 7) (var 6) ⟶
      exponentCoefficient (var 2) (var 3) (var 7) ≐ exponentCoefficient (var 4) (var 5) (var 7)) :=
  closeUniv 8 (.impI (.impI (coefficient_unique _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scale_inverse_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 inverseF (var 0) ≐ inversePoint (var 0)) := closeUniv 1 (inverse_program_at _)
theorem actual_prior_coefficient_sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app priorF ![var 0,var 1,var 2,var 3,var 4] ≐ priorSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (prior_program_at _ _ _ _ _)
theorem actual_coefficient_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ comparison (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_coefficient_recursion_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ le (var 7) (var 6) ⟶
      fstT (run (var 2) (var 3) (var 4) (var 5) (var 7)) ≐ sndT (run (var 2) (var 3) (var 4) (var 5) (var 7))) :=
  closeUniv 8 (.impI (.impI (returned_agreement _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalCoefficientRecursion

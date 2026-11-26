import IPRADerivations.Analysis.Gamma.GaussianGammaPoleFiniteFactors
import IPRADerivations.Analysis.Polynomials.GaussianRationalCoefficientScaling

/-!
# A finite divided difference for the actual Gamma shift product

The original rising product is presented in reverse order, with its
last factor retained separately. The two-point fold gives the exact
difference after multiplication by the input increment. On the diagonal
the same fold is the first coefficient in the translated argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 2100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHeadShift (linear)
open GaussianGammaLocalPoleGuards (center translation_at_center)
open GaussianGammaPoleFiniteFactors (difference differenceBody differenceProduct difference_succ reverse_rising)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner
  (ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul qzero canonical_unique represents_congr)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr qmul_zero_right)
open GaussianReciprocalHorner (qmul_associative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def prefixStep : PTm 3 :=
  qadd (qmul (var 1) (difference (fstT (sndT (var 2))) (sndT (sndT (var 2))) (succ (var 0))))
    (differenceProduct (fstT (var 2)) (sndT (sndT (var 2))) (var 0))

def prefixF : PR 2 := rec2 (qzero : PTm 1) prefixStep

def prefixDifference (h w b j : PTm n) : PTm n :=
  ap2 prefixF j (pairT h (pairT w b))

def dividedDifference (h w b j : PTm n) : PTm n :=
  qadd (qmul (prefixDifference h w b j) (ofGaussian w b)) (differenceProduct h b j)

def firstCoefficient (h b j : PTm n) : PTm n := dividedDifference h h b j

@[simp] theorem subst_prefixDifference {m : ℕ} (σ : Fin n → PTm m) (h w b j : PTm n) :
    Syn.subst σ (prefixDifference h w b j) =
      prefixDifference (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [prefixDifference]
@[simp] theorem subst_dividedDifference {m : ℕ} (σ : Fin n → PTm m) (h w b j : PTm n) :
    Syn.subst σ (dividedDifference h w b j) =
      dividedDifference (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [dividedDifference]
@[simp] theorem subst_firstCoefficient {m : ℕ} (σ : Fin n → PTm m) (h b j : PTm n) :
    Syn.subst σ (firstCoefficient h b j) = firstCoefficient (Syn.subst σ h) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [firstCoefficient]

private theorem factor_congr {h w b c j : PTm n} (hh : Γ ⊢[PRAAx] h ≐ w) (hb : Γ ⊢[PRAAx] b ≐ c) :
    Γ ⊢[PRAAx] difference h b j ≐ difference w c j := by
  simpa only [GaussianGammaPoleFiniteFactors.subst_difference, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (difference (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![h,b,j]) (σ' := ![w,c,j]) (fun i => by fin_cases i; exact hh; exact hb; exact .eqRefl _)

private theorem product_congr {h w b c j : PTm n} (hh : Γ ⊢[PRAAx] h ≐ w) (hb : Γ ⊢[PRAAx] b ≐ c) :
    Γ ⊢[PRAAx] differenceProduct h b j ≐ differenceProduct w c j := by
  simpa only [GaussianGammaPoleFiniteFactors.subst_differenceProduct, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (differenceProduct (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![h,b,j]) (σ' := ![w,c,j]) (fun i => by fin_cases i; exact hh; exact hb; exact .eqRefl _)

theorem prefix_zero (h w b : PTm n) : Γ ⊢[PRAAx] prefixDifference h w b zero ≐ qzero := by
  simpa only [prefixDifference,prefixF,GaussianRationalHorner.subst_qzero] using
    rec2_zero (Γ := Γ) (qzero : PTm 1) prefixStep (pairT h (pairT w b))

theorem prefix_succ (h w b j : PTm n) : Γ ⊢[PRAAx]
    prefixDifference h w b (succ j) ≐
      qadd (qmul (prefixDifference h w b j) (difference w b (succ j))) (differenceProduct h b j) := by
  let x := pairT h (pairT w b)
  have recurrence := rec2_succ (Γ := Γ) (qzero : PTm 1) prefixStep j x
  have raw : Γ ⊢[PRAAx] prefixDifference h w b (succ j) ≐
      qadd (qmul (prefixDifference h w b j) (difference (fstT (sndT x)) (sndT (sndT x)) (succ j)))
        (differenceProduct (fstT x) (sndT (sndT x)) j) := by
    simpa only [prefixDifference,prefixF,prefixStep,x,subst_pairT,subst_fstT,subst_sndT,
      GaussianRationalHorner.subst_qadd,GaussianRationalHorner.subst_qmul,
      GaussianGammaPoleFiniteFactors.subst_difference, GaussianGammaPoleFiniteFactors.subst_differenceProduct,
      ConciseIPRA.PTm.subst_succ,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using recurrence
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT w b := snd_pair _ _
  have W := (congrFst tail).eqTrans (fst_pair w b)
  have B := (congrSnd tail).eqTrans (snd_pair w b)
  exact raw.eqTrans (qadd_congr (qmul_congr (.eqRefl _) (factor_congr W B))
    (product_congr (fst_pair h (pairT w b)) B))

theorem difference_product_zero (h b : PTm n) : Γ ⊢[PRAAx] differenceProduct h b zero ≐ qone :=
  GaussianRationalFiniteProduct.product_zero differenceBody (pairT h b)

theorem factor_gap (h w b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (difference w b j) (difference h b j) ≐ qsub (ofGaussian w b) (ofGaussian h b) := by
  let A := center w b j
  let B := center h b j
  have left := qsub_represents _ _ _ _ _ hb (ofGaussian_represents A b hb) (ofGaussian_represents B b hb)
  have right := qsub_represents _ _ _ _ _ hb (ofGaussian_represents w b hb) (ofGaussian_represents h b hb)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (GaussianRootAlgebra.sub A B) (GaussianRootAlgebra.sub w h) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [A,B,center,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_add,
        GaussianRootAlgebra.im_add] <;> ring
  exact canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hb
    (represents_congr (.eqRefl _) e (.eqRefl _) left) right

theorem product_gap_step (x y f g u D : PTm n)
    (h : Γ ⊢[PRAAx] qsub x y ≐ qmul u D) (hg : Γ ⊢[PRAAx] qsub f g ≐ u) :
    Γ ⊢[PRAAx] qsub (qmul x f) (qmul y g) ≐ qmul u (qadd (qmul D f) y) :=
  (product_difference x y f g).eqTrans
    ((qadd_congr ((qmul_congr h (.eqRefl _)).eqTrans (qmul_associative u D f))
      ((qmul_congr (.eqRefl _) hg).eqTrans (qmul_commutative y u))).eqTrans
      (qmul_add u (qmul D f) y).eqSymm)

def prefixLaw (h w b j : PTm n) : Fm PTm n :=
  qsub (differenceProduct w b j) (differenceProduct h b j) ≐
    qmul (qsub (ofGaussian w b) (ofGaussian h b)) (prefixDifference h w b j)

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (h w b j : PTm n) :
    (prefixLaw h w b j).subst σ = prefixLaw (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ b) (Syn.subst σ j) := by
  simp [prefixLaw]

private theorem gap_zero (h w b : PTm n) : Γ ⊢[PRAAx] prefixLaw h w b zero :=
  ((qsub_congr (difference_product_zero w b) (difference_product_zero h b)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self qone)).eqTrans
    ((qmul_congr (.eqRefl _) (prefix_zero h w b)).eqTrans (qmul_zero_right _)).eqSymm

private theorem gap_succ (h w b j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ih : Γ ⊢[PRAAx] prefixLaw h w b j) : Γ ⊢[PRAAx] prefixLaw h w b (succ j) :=
  (qsub_congr (difference_succ w b j) (difference_succ h b j)).eqTrans
    ((product_gap_step _ _ _ _ _ _ ih (factor_gap h w b (succ j) hb)).eqTrans
      (qmul_congr (.eqRefl _) (prefix_succ h w b j).eqSymm))

theorem prefix_gap (h w b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] prefixLaw h w b j := by
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift,one] using hb.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift h) (Syn.shift w) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using gap_zero (Γ := Γ) h w b
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        gap_succ (Syn.shift h) (Syn.shift w) (Syn.shift b) (var 0) hb'.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem rising_product (h b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    risingProduct (center h b j) b (succ j) ≐ qmul (differenceProduct h b j) (ofGaussian h b) := by
  have last : Γ ⊢[PRAAx] linear (center h b j) b j ≐ ofGaussian h b :=
    canonical_unique _ _ _ b (ofGaussian_canonical _ _ hb) (ofGaussian_canonical _ _ hb) hb
      (represents_congr (.eqRefl _) (translation_at_center h b j) (.eqRefl _) (ofGaussian_represents _ _ hb))
      (ofGaussian_represents _ _ hb)
  exact (GaussianGammaRepeatedShift.prefix_succ (center h b j) b j).eqTrans
    (qmul_congr (reverse_rising h b j hb) last)

/-- The literal original Gamma shift products differ by the original
input increment times the finite divided difference. -/
theorem original_product_gap (h w b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qsub (risingProduct (center w b j) b (succ j)) (risingProduct (center h b j) b (succ j)) ≐
      qmul (qsub (ofGaussian w b) (ofGaussian h b)) (dividedDifference h w b j) :=
  (qsub_congr (rising_product w b j hb) (rising_product h b j hb)).eqTrans
    (product_gap_step _ _ _ _ _ _ (prefix_gap h w b j hb) (.eqRefl _))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivative

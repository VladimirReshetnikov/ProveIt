import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussShiftedProduct
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerCutoff
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct

/-!
# Cofinal Euler products for the shifted Gamma name

Every row uses the same Euler cutoff. The uniform row error gives a
finite-product error at independent precisions for the Euler fold
and the original shifted Gamma name.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussEulerProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData eulerHeight)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerCutoff (commonCutoff common_guards larger_cutoff_error)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance amplification)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical canonical_congr positive_product)
open GaussianRationalLinearProduct (add_sub_right)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def rowValue (p r z R B m d N : PTm n) : PTm n :=
  ap2 eulerF (succ p) (eulerData (shiftedNumerator z B m r) (R+one) (B*m) (d*m) N)

def rowData (z R B m d N : PTm n) : PTm n :=
  pairT z (pairT R (pairT B (pairT m (pairT d N))))

def rowBody : PTm 3 :=
  let x : PTm 3 := var 2
  let tail₁ := sndT x
  let tail₂ := sndT tail₁
  let tail₃ := sndT tail₂
  let tail₄ := sndT tail₃
  rowValue (var 0) (var 1) (fstT x) (fstT tail₁) (fstT tail₂) (fstT tail₃) (fstT tail₄) (sndT tail₄)

def rowF : PR 3 := PTm.toPR rowBody

def sample (p z R B m d N : PTm n) : PTm n := GaussianNamedFiniteProduct.sample rowF p m (rowData z R B m d N)

def rowRadius (R m d : PTm n) : PTm n := GaussianGammaGaussShiftedProduct.rowRadius R m d+two

def errorBudget (R m d : PTm n) : PTm n := amplification (rowRadius R m d) m

def threshold (p R m a d : PTm n) : PTm n :=
  GaussianGammaEulerInverseApproximationName.cutoff p (R+one) a (d*m)

@[simp] theorem subst_rowValue {l : ℕ} (σ : Fin n → PTm l) (p r z R B m d N : PTm n) :
    Syn.subst σ (rowValue p r z R B m d N) = rowValue (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [rowValue,shiftedNumerator,one]

@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (z R B m d N : PTm n) :
    Syn.subst σ (rowData z R B m d N) = rowData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [rowData]

@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p z R B m d N : PTm n) :
    Syn.subst σ (sample p z R B m d N) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [sample]

@[simp] theorem subst_rowRadius {l : ℕ} (σ : Fin n → PTm l) (R m d : PTm n) :
    Syn.subst σ (rowRadius R m d) = rowRadius (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [rowRadius,two,one]

@[simp] theorem subst_errorBudget {l : ℕ} (σ : Fin n → PTm l) (R m d : PTm n) :
    Syn.subst σ (errorBudget R m d) = errorBudget (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [errorBudget]

@[simp] theorem subst_threshold {l : ℕ} (σ : Fin n → PTm l) (p R m a d : PTm n) :
    Syn.subst σ (threshold p R m a d) =
      threshold (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [threshold,one]

theorem row_at (p r z R B m d N : PTm n) :
    Γ ⊢[PRAAx] ap3 rowF p r (rowData z R B m d N) ≐ rowValue p r z R B m d N := by
  let x := rowData z R B m d N
  let tail₁ := sndT x
  let tail₂ := sndT tail₁
  let tail₃ := sndT tail₂
  let tail₄ := sndT tail₃
  have s₁ : Γ ⊢[PRAAx] tail₁ ≐ pairT R (pairT B (pairT m (pairT d N))) := snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] tail₂ ≐ pairT B (pairT m (pairT d N)) := (congrSnd s₁).eqTrans (snd_pair _ _)
  have s₃ : Γ ⊢[PRAAx] tail₃ ≐ pairT m (pairT d N) := (congrSnd s₂).eqTrans (snd_pair _ _)
  have s₄ : Γ ⊢[PRAAx] tail₄ ≐ pairT d N := (congrSnd s₃).eqTrans (snd_pair _ _)
  have hz : Γ ⊢[PRAAx] fstT x ≐ z := fst_pair _ _
  have hR : Γ ⊢[PRAAx] fstT tail₁ ≐ R := (congrFst s₁).eqTrans (fst_pair _ _)
  have hB : Γ ⊢[PRAAx] fstT tail₂ ≐ B := (congrFst s₂).eqTrans (fst_pair _ _)
  have hm : Γ ⊢[PRAAx] fstT tail₃ ≐ m := (congrFst s₃).eqTrans (fst_pair _ _)
  have hd : Γ ⊢[PRAAx] fstT tail₄ ≐ d := (congrFst s₄).eqTrans (fst_pair _ _)
  have hN : Γ ⊢[PRAAx] sndT tail₄ ≐ N := (congrSnd s₄).eqTrans (snd_pair _ _)
  have first : Γ ⊢[PRAAx] ap3 rowF p r x ≐
      rowValue p r (fstT x) (fstT tail₁) (fstT tail₂) (fstT tail₃) (fstT tail₄) (sndT tail₄) := by
    change Γ ⊢[PRAAx] ConciseIPRA.PTm.app (PTm.toPR rowBody) ![p,r,x] ≐ _
    simpa only [rowBody,subst_rowValue,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,tail₁,tail₂,tail₃,tail₄] using
      toPR_eq (Γ := Γ) rowBody ![p,r,x]
  let w := shiftedNumerator (fstT x) (fstT tail₂) (fstT tail₃) r
  let w' := shiftedNumerator z B m r
  have hw : Γ ⊢[PRAAx] w ≐ w' := by
    simpa only [w,w',shiftedNumerator,GaussianGammaEulerHeadLower.subst_translated,
      ComplexLogarithmRemainder.subst_scale,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (shiftedNumerator (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,fstT tail₂,fstT tail₃,r]) (σ' := ![z,B,m,r]) (fun i => by
        fin_cases i
        · exact hz
        · exact hB
        · exact hm
        · exact .eqRefl _)
  have hradius := congrAdd hR (.eqRefl (one : PTm n))
  have hden := congrMul hB hm
  have hmargin := congrMul hd hm
  have dataEq : Γ ⊢[PRAAx] eulerData w (fstT tail₁+one) (fstT tail₂*fstT tail₃)
      (fstT tail₄*fstT tail₃) (sndT tail₄) ≐ eulerData w' (R+one) (B*m) (d*m) N := by
    simpa only [GaussianGammaEulerInverseApproximationName.subst_eulerData,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (eulerData (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![w,fstT tail₁+one,fstT tail₂*fstT tail₃,fstT tail₄*fstT tail₃,sndT tail₄])
      (σ' := ![w',R+one,B*m,d*m,N]) (fun i => by
        fin_cases i
        · exact hw
        · exact hradius
        · exact hden
        · exact hmargin
        · exact hN)
  exact first.eqTrans (congrAp2 eulerF (.eqRefl (succ p)) dataEq)

theorem row_error_at (p q r z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) (hN : Γ ⊢[PRAAx] le (threshold p R m a d) N) :
    Γ ⊢[PRAAx] distanceBounded (ap3 rowF p r (rowData z R B m d N))
      (ap3 GaussianGammaGaussShiftedProduct.rowF q r (GaussianGammaGaussShiftedProduct.rowData z R B m d))
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (row_at p r z R B m d N).eqSymm (GaussianGammaGaussShiftedProduct.row_at q r z R B m d).eqSymm
    (.eqRefl _) (.eqRefl _)
    (larger_cutoff_error p q _ _ _ _ _ N (GaussianGammaGaussShiftedProduct.row_source z R B m r a d h hr) hN)

theorem row_bound_at (p r z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) (hN : Γ ⊢[PRAAx] le (threshold p R m a d) N) :
    Γ ⊢[PRAAx] bounded (ap3 rowF p r (rowData z R B m d N)) (rowRadius R m d) one := by
  let E := ap3 rowF p r (rowData z R B m d N)
  let G := ap3 GaussianGammaGaussShiftedProduct.rowF p r (GaussianGammaGaussShiftedProduct.rowData z R B m d)
  let U := unit p
  let w := shiftedNumerator z B m r
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have ce : Γ ⊢[PRAAx] canonical E :=
    canonical_congr (row_at p r z R B m d N)
      (GaussianNameReciprocal.name_canonical qF (eulerHeight w (R+one) (B*m) (d*m) N) (qData w (B*m) N) (succ p))
  have hb : Γ ⊢[PRAAx] bounded G (GaussianGammaGaussShiftedProduct.rowRadius R m d) one :=
    GaussianGammaGaussShiftedProduct.row_bound_at p r z R B m a d h hr
  have hd : Γ ⊢[PRAAx] distanceBounded E G two one :=
    distance_radius_mono E G (U+U) (U*U) two one (positive_product U U hU hU) (le_refl one)
      (by ipra_le 2*𝔞 U*sl hU) (row_error_at p p r z R B m a d N h hr hN)
  exact bound_congr (add_sub_right G E ce) (.eqRefl _) (.eqRefl _)
    (bounded_sum_same G (qsub E G) _ _ one (le_refl one) hb hd)

theorem row_bounds (p z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hN : Γ ⊢[PRAAx] le (threshold p R m a d) N) :
    Γ ⊢[PRAAx] rowBoundsAt rowF p m (rowRadius R m d) (rowData z R B m d N) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
  have hsN : Δ ⊢[PRAAx] le (threshold (sh p) (sh R) (sh m) (sh a) (sh d)) (sh N) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hN.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := Prf.hyp0
  simpa [rowBoundsAt,Δ,sh,Syn.shift] using
    row_bound_at (sh p) (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) (sh N) hs hr hsN

private theorem gamma_row_bounds (q z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] rowBoundsAt GaussianGammaGaussShiftedProduct.rowF q m (rowRadius R m d)
      (GaussianGammaGaussShiftedProduct.rowData z R B m d) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := Prf.hyp0
  let P := GaussianGammaGaussShiftedProduct.rowRadius (sh R) (sh m) (sh d)
  have widen : Δ ⊢[PRAAx] le (P*one) ((P+two)*one) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_add_right P two)
  have hb := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) widen
    (GaussianGammaGaussShiftedProduct.row_bound_at (sh q) (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) hs hr)
  simpa [rowBoundsAt,rowRadius,Δ,sh,P,Syn.shift,one,two] using hb

theorem row_errors (p q z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hN : Γ ⊢[PRAAx] le (threshold p R m a d) N) :
    Γ ⊢[PRAAx] rowDistance rowF GaussianGammaGaussShiftedProduct.rowF p q m (unit p+unit q) (unit p*unit q)
      (rowData z R B m d N) (GaussianGammaGaussShiftedProduct.rowData z R B m d) := by
  refine .allI (.impI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
  have hsN : Δ ⊢[PRAAx] le (threshold (sh p) (sh R) (sh m) (sh a) (sh d)) (sh N) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hN.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := Prf.hyp0
  simpa [rowDistance,Δ,sh,Syn.shift] using
    row_error_at (sh p) (sh q) (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) (sh N) hs hr hsN

theorem product_error (p q z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hN : Γ ⊢[PRAAx] le (threshold p R m a d) N) : Γ ⊢[PRAAx] distanceBounded
    (sample p z R B m d N) (ap2 GaussianGammaGaussShiftedProduct.nameF q (GaussianGammaGaussShiftedProduct.data z R B m d))
    (errorBudget R m d*(unit p+unit q)) (unit p*unit q) := by
  let s := GaussianGammaGaussShiftedProduct.clock q R m d
  let A := errorBudget R m d
  have hs : Γ ⊢[PRAAx] le (unit q) (unit s) := GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one)
    (GaussianNamedFiniteProductName.clock_later m (GaussianGammaGaussShiftedProduct.rowRadius R m d) one q)
  have hu := positive_product (unit p) (unit q) (unit_positive (Γ := Γ) p) (unit_positive q)
  have hv := positive_product (unit p) (unit s) (unit_positive (Γ := Γ) p) (unit_positive s)
  have step := GaussianNamedFiniteProduct.sample_distance rowF GaussianGammaGaussShiftedProduct.rowF p s m
    (rowRadius R m d) (unit p+unit s) (unit p*unit s) (rowData z R B m d N)
    (GaussianGammaGaussShiftedProduct.rowData z R B m d) hv (row_bounds p z R B m a d N h hN)
    (gamma_row_bounds s z R B m a d h) (row_errors p s z R B m a d N h hN)
  have hr := distance_congr (.eqRefl _) (GaussianGammaGaussShiftedProduct.name_at q z R B m d).eqSymm
    (.eqRefl _) (.eqRefl _) step
  exact distance_radius_mono _ _ (A*(unit p+unit s)) (unit p*unit s) (A*(unit p+unit q)) (unit p*unit q) hv hu
    (by ipra_le 𝔞 A*𝔞 (unit p)*𝔞 (unit p)*sl hs) hr

theorem common_product_error (p q z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (sample p z R B m d (commonCutoff p R m a d))
      (ap2 GaussianGammaGaussShiftedProduct.nameF q (GaussianGammaGaussShiftedProduct.data z R B m d))
      (errorBudget R m d*(unit p+unit q)) (unit p*unit q) :=
  product_error p q z R B m a d _ h (common_guards p R m a d h.andE₁.andE₁).andE₂.andE₁

theorem actual_Gauss_Euler_product_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      le (threshold (var 0) (var 3) (var 5) (var 6) (var 7)) (var 8) ⟶
      distanceBounded (sample (var 0) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8))
        (ap2 GaussianGammaGaussShiftedProduct.nameF (var 1)
          (GaussianGammaGaussShiftedProduct.data (var 2) (var 3) (var 4) (var 5) (var 7)))
        (errorBudget (var 3) (var 5) (var 7)*(unit (var 0)+unit (var 1))) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (.impI (product_error _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussEulerProduct

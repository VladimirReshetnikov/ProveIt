import IPRADerivations.Analysis.GaussianGammaGaussReferenceProduct
import IPRADerivations.Analysis.GaussianGaussEulerCutoff
import IPRADerivations.Analysis.GaussianRationalLinearProduct

/-!
# Cofinal Euler samples of the reference Gamma product

Every row uses the radius-one Euler reciprocal for ((r+1)/m).
The common Gauss cutoff controls the finite fold and the original
reference Gamma product at independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceEulerProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData eulerHeight)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaGaussReferenceProduct (argument row_source)
open GaussianGaussEulerCutoff (commonCutoff common_guards larger_cutoff_error)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance amplification radius)
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

def rowValue (p r m N : PTm n) : PTm n := ap2 eulerF (succ p) (eulerData (argument r) one m m N)
def rowData (m N : PTm n) : PTm n := pairT m N
def rowBody : PTm 3 := rowValue (var 0) (var 1) (fstT (var 2)) (sndT (var 2))
def rowF : PR 3 := PTm.toPR rowBody
def sample (p m N : PTm n) : PTm n := GaussianNamedFiniteProduct.sample rowF p m (rowData m N)
def rowRadius (m : PTm n) : PTm n := GaussianGammaGaussReferenceProduct.rowRadius m+two
def errorBudget (m : PTm n) : PTm n := amplification (rowRadius m) m
def threshold (p m : PTm n) : PTm n := GaussianGammaEulerInverseApproximationName.cutoff p one one m

@[simp] theorem subst_rowValue {l : ℕ} (σ : Fin n → PTm l) (p r m N : PTm n) :
    Syn.subst σ (rowValue p r m N) = rowValue (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [rowValue,one]

@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (m N : PTm n) :
    Syn.subst σ (rowData m N) = rowData (Syn.subst σ m) (Syn.subst σ N) := by simp [rowData]

@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p m N : PTm n) :
    Syn.subst σ (sample p m N) = sample (Syn.subst σ p) (Syn.subst σ m) (Syn.subst σ N) := by simp [sample]

@[simp] theorem subst_rowRadius {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (rowRadius m) = rowRadius (Syn.subst σ m) := by simp [rowRadius,two,one]

@[simp] theorem subst_errorBudget {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (errorBudget m) = errorBudget (Syn.subst σ m) := by simp [errorBudget]

@[simp] theorem subst_threshold {l : ℕ} (σ : Fin n → PTm l) (p m : PTm n) :
    Syn.subst σ (threshold p m) = threshold (Syn.subst σ p) (Syn.subst σ m) := by simp [threshold,one]

theorem row_at (p r m N : PTm n) : Γ ⊢[PRAAx] ap3 rowF p r (rowData m N) ≐ rowValue p r m N := by
  let x := rowData m N
  have first : Γ ⊢[PRAAx] ap3 rowF p r x ≐ rowValue p r (fstT x) (sndT x) := by
    change Γ ⊢[PRAAx] ConciseIPRA.PTm.app (PTm.toPR rowBody) ![p,r,x] ≐ _
    simpa only [rowBody,subst_rowValue,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) rowBody ![p,r,x]
  have last : Γ ⊢[PRAAx] rowValue p r (fstT x) (sndT x) ≐ rowValue p r m N := by
    simpa only [subst_rowValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rowValue (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![p,r,fstT x,sndT x]) (σ' := ![p,r,m,N]) (fun i => by
          fin_cases i
          · exact .eqRefl _
          · exact .eqRefl _
          · exact fst_pair _ _
          · exact snd_pair _ _)
  exact first.eqTrans last

theorem row_error_at (p q r m N : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] distanceBounded (ap3 rowF p r (rowData m N)) (ap3 GaussianGammaGaussReferenceProduct.rowF q r m)
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (row_at p r m N).eqSymm (GaussianGammaGaussReferenceProduct.row_at q r m).eqSymm
    (.eqRefl _) (.eqRefl _)
    (larger_cutoff_error p q (argument r) one m one m N (row_source r m hr) hN)

theorem row_bound_at (p r m N : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] bounded (ap3 rowF p r (rowData m N)) (rowRadius m) one := by
  let E := ap3 rowF p r (rowData m N)
  let G := ap3 GaussianGammaGaussReferenceProduct.rowF p r m
  let U := unit p
  let w := argument r
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have ce : Γ ⊢[PRAAx] canonical E :=
    canonical_congr (row_at p r m N) (GaussianNameReciprocal.name_canonical qF (eulerHeight w one m m N) (qData w m N) (succ p))
  have hb : Γ ⊢[PRAAx] bounded G (GaussianGammaGaussReferenceProduct.rowRadius m) one :=
    GaussianGammaGaussReferenceProduct.row_bound_at p r m hr
  have hd : Γ ⊢[PRAAx] distanceBounded E G two one :=
    distance_radius_mono E G (U+U) (U*U) two one (positive_product U U hU hU) (le_refl one)
      (by ipra_le 2*𝔞 U*sl hU) (row_error_at p p r m N hr hN)
  exact bound_congr (add_sub_right G E ce) (.eqRefl _) (.eqRefl _)
    (bounded_sum_same G (qsub E G) _ _ one (le_refl one) hb hd)

theorem row_bounds (p m N : PTm n) (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] rowBoundsAt rowF p m (rowRadius m) (rowData m N) := by
  refine .allI (.impI ?_)
  let M := Syn.shift m
  let Δ := lt (var 0) M :: Γ.map Fm.shift
  have later : Δ ⊢[PRAAx] le (threshold (Syn.shift p) M) (Syn.shift N) := by
    simpa [Δ,M,Fm.shift,Syn.shift] using hN.shift.wk
  simpa [rowBoundsAt,Δ,M,Syn.shift] using
    row_bound_at (Syn.shift p) (var 0) M (Syn.shift N) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M) later

private theorem gamma_row_bounds (q m : PTm n) :
    Γ ⊢[PRAAx] rowBoundsAt GaussianGammaGaussReferenceProduct.rowF q m (rowRadius m) m := by
  refine .allI (.impI ?_)
  let M := Syn.shift m
  let Δ := lt (var 0) M :: Γ.map Fm.shift
  let P := GaussianGammaGaussReferenceProduct.rowRadius M
  have widen : Δ ⊢[PRAAx] le (P*one) ((P+two)*one) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_add_right P two)
  have hb := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) widen
    (GaussianGammaGaussReferenceProduct.row_bound_at (Syn.shift q) (var 0) M (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M))
  simpa [rowBoundsAt,rowRadius,Δ,M,P,Syn.shift,one,two] using hb

theorem row_errors (p q m N : PTm n) (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] rowDistance rowF GaussianGammaGaussReferenceProduct.rowF p q m (unit p+unit q) (unit p*unit q)
      (rowData m N) m := by
  refine .allI (.impI ?_)
  let M := Syn.shift m
  let Δ := lt (var 0) M :: Γ.map Fm.shift
  have later : Δ ⊢[PRAAx] le (threshold (Syn.shift p) M) (Syn.shift N) := by
    simpa [Δ,M,Fm.shift,Syn.shift] using hN.shift.wk
  simpa [rowDistance,Δ,M,Syn.shift] using
    row_error_at (Syn.shift p) (Syn.shift q) (var 0) M (Syn.shift N) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M) later

theorem sample_bound (p m N : PTm n) (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] bounded (sample p m N) (radius (rowRadius m) m) one :=
  GaussianNamedFiniteProduct.sample_bound rowF p m (rowRadius m) (rowData m N) (row_bounds p m N hN)

theorem product_error (p q m N : PTm n) (hN : Γ ⊢[PRAAx] le (threshold p m) N) :
    Γ ⊢[PRAAx] distanceBounded (sample p m N)
      (ap2 GaussianGammaGaussReferenceProduct.nameF q (GaussianGammaGaussReferenceProduct.data m))
      (errorBudget m*(unit p+unit q)) (unit p*unit q) := by
  let s := GaussianGammaGaussReferenceProduct.clock q m
  let A := errorBudget m
  have later : Γ ⊢[PRAAx] le (unit q) (unit s) := GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one)
    (GaussianNamedFiniteProductName.clock_later m (GaussianGammaGaussReferenceProduct.rowRadius m) one q)
  have hu := positive_product (unit p) (unit q) (unit_positive (Γ := Γ) p) (unit_positive q)
  have hv := positive_product (unit p) (unit s) (unit_positive (Γ := Γ) p) (unit_positive s)
  have step := GaussianNamedFiniteProduct.sample_distance rowF GaussianGammaGaussReferenceProduct.rowF p s m
    (rowRadius m) (unit p+unit s) (unit p*unit s) (rowData m N) m hv
    (row_bounds p m N hN) (gamma_row_bounds s m) (row_errors p s m N hN)
  have hr := distance_congr (.eqRefl _) (GaussianGammaGaussReferenceProduct.name_at q m).eqSymm
    (.eqRefl _) (.eqRefl _) step
  exact distance_radius_mono _ _ (A*(unit p+unit s)) (unit p*unit s) (A*(unit p+unit q)) (unit p*unit q) hv hu
    (by ipra_le 𝔞 A*𝔞 (unit p)*𝔞 (unit p)*sl later) hr

theorem common_product_error (p q R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (sample p m (commonCutoff p R m a d))
      (ap2 GaussianGammaGaussReferenceProduct.nameF q (GaussianGammaGaussReferenceProduct.data m))
      (errorBudget m*(unit p+unit q)) (unit p*unit q) :=
  product_error p q m _ (common_guards p R m a d hm).andE₂.andE₂.andE₂

theorem actual_Gauss_reference_Euler_product_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (threshold (var 0) (var 2)) (var 3) ⟶
      distanceBounded (sample (var 0) (var 2) (var 3))
        (ap2 GaussianGammaGaussReferenceProduct.nameF (var 1) (GaussianGammaGaussReferenceProduct.data (var 2)))
        (errorBudget (var 2)*(unit (var 0)+unit (var 1))) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (product_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceEulerProduct

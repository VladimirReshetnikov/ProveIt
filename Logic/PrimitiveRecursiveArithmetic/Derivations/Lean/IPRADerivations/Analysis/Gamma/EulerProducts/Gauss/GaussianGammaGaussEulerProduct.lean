import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ShiftedProducts.GaussianGammaGaussShiftedProduct
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.Cutoffs.GaussianGaussEulerCutoff
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.PolynomialFactors.GaussianRationalLinearProduct

/-!
# Cofinal Euler products for the shifted Gamma name

Every row uses the same Euler cutoff. The uniform row error gives a
finite-product error at independent precisions for the Euler fold
and the original shifted Gamma name.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussEulerProduct

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerCutoff (commonCutoff common_guards larger_cutoff_error)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance amplification)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_two_errors norm_from_distance_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)

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

ipra_subst rowValue [shiftedNumerator, one]

ipra_subst rowData

ipra_subst sample

ipra_subst rowRadius [two, one]

ipra_subst errorBudget

ipra_subst threshold [one]

theorem row_at (p r z R B m d N : PTm n) :
    Γ ⊢[PRAAx] ap3 rowF p r (rowData z R B m d N) ≐ rowValue p r z R B m d N := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 5)
    (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) p r ![z, R, B, m, d, N]
  simp only [subst_rowValue, Syn.subst_var] at read
  exact read

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
  have hU := unit_positive (Γ := Γ) p
  have hd := distance_two_errors _ _ _ _ one hU hU (le_refl one) hU hU
    (row_error_at p p r z R B m a d N h hr hN)
  exact bound_congr (.eqRefl _) (add_comm _ _) (.eqRefl _)
    (norm_from_distance_same (le_refl one) hd (GaussianGammaGaussShiftedProduct.row_bound_at p r z R B m a d h hr))

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

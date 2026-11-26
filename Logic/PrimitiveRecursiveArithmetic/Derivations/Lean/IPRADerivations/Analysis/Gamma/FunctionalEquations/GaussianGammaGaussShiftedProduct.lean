import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussDomain
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductName

/-!
# A regular name for the shifted Gamma product

The row program evaluates the original Gamma name at the encoded arguments
`z/B + r/m`. The pole guard for `mz/B` gives one radius and one precision
budget for the finite product over `r < m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussShiftedProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaGaussDomain (scaledRadius shifted_source)
open GaussianGammaReciprocalInverse
  (gammaF gammaData gamma_regular lambdaNumerator lambdaDenominator lambda_positive actual_gamma_observation_bound)
open GaussianNamedFiniteProduct (sample rowBoundsAt rowDistance)
open GaussianNamedFiniteProductName (rowBounds rowRegular)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B m a d : PTm n) : Fm PTm n :=
  (le one m ⋏ ComplexLogarithmRemainder.bounded z (R*B)) ⋏
    GaussianGammaReciprocalInverse.source (scale m z) (scaledRadius R m) B a d

def rowValue (p r z R B m d : PTm n) : PTm n :=
  ap2 gammaF p (gammaData (shiftedNumerator z B m r) (R+one) (B*m) (d*m))

def rowData (z R B m d : PTm n) : PTm n := pairT z (pairT R (pairT B (pairT m d)))

def rowBody : PTm 3 :=
  rowValue (var 0) (var 1) (fstT (var 2)) (fstT (sndT (var 2)))
    (fstT (sndT (sndT (var 2)))) (fstT (sndT (sndT (sndT (var 2))))) (sndT (sndT (sndT (sndT (var 2)))))

def rowF : PR 3 := PTm.toPR rowBody

def rowRadius (R m d : PTm n) : PTm n := lambdaDenominator (R+one) (d*m)+two

def nameF : PR 2 := GaussianNamedFiniteProductName.nameF rowF

def data (z R B m d : PTm n) : PTm n :=
  GaussianNamedFiniteProductName.data m (rowRadius R m d) one (rowData z R B m d)

def clock (p R m d : PTm n) : PTm n :=
  GaussianNamedFiniteProductName.clock m (rowRadius R m d) one p

@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B m a d : PTm n) :
    (source z R B m a d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [source,one]

@[simp] theorem subst_rowValue {l : ℕ} (σ : Fin n → PTm l) (p r z R B m d : PTm n) :
    Syn.subst σ (rowValue p r z R B m d) = rowValue (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [rowValue,shiftedNumerator,gammaData,GaussianGammaReciprocalInverse.gammaHeight,one]

@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (z R B m d : PTm n) :
    Syn.subst σ (rowData z R B m d) = rowData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ m) (Syn.subst σ d) := by
  simp [rowData]

@[simp] theorem subst_rowRadius {l : ℕ} (σ : Fin n → PTm l) (R m d : PTm n) :
    Syn.subst σ (rowRadius R m d) = rowRadius (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [rowRadius,one,two]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B m d : PTm n) :
    Syn.subst σ (data z R B m d) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ m) (Syn.subst σ d) := by
  simp [data,one]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p R m d : PTm n) :
    Syn.subst σ (clock p R m d) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [clock,one]

theorem row_at (p r z R B m d : PTm n) : Γ ⊢[PRAAx] ap3 rowF p r (rowData z R B m d) ≐ rowValue p r z R B m d := by
  let x := rowData z R B m d
  have s₁ : Γ ⊢[PRAAx] sndT x ≐ pairT R (pairT B (pairT m d)) := snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT x) ≐ pairT B (pairT m d) := (congrSnd s₁).eqTrans (snd_pair _ _)
  have s₃ : Γ ⊢[PRAAx] sndT (sndT (sndT x)) ≐ pairT m d := (congrSnd s₂).eqTrans (snd_pair _ _)
  have first : Γ ⊢[PRAAx] ap3 rowF p r x ≐ rowValue p r (fstT x) (fstT (sndT x))
      (fstT (sndT (sndT x))) (fstT (sndT (sndT (sndT x)))) (sndT (sndT (sndT (sndT x)))) := by
    simpa [rowF,rowBody,ap3] using toPR_eq (Γ := Γ) rowBody ![p,r,x]
  have last := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (rowValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
    (σ := ![p,r,fstT x,fstT (sndT x),fstT (sndT (sndT x)),fstT (sndT (sndT (sndT x))),
      sndT (sndT (sndT (sndT x)))]) (σ' := ![p,r,z,R,B,m,d]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst s₁).eqTrans (fst_pair _ _)
      · exact (congrFst s₂).eqTrans (fst_pair _ _)
      · exact (congrFst s₃).eqTrans (fst_pair _ _)
      · exact (congrSnd s₃).eqTrans (snd_pair _ _))
  exact first.eqTrans (by simpa using last)

theorem row_source (z R B m r a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (shiftedNumerator z B m r) (R+one) (B*m) a (d*m) :=
  shifted_source z R B m r a d h.andE₁.andE₁ (le_of_lt hr) h.andE₁.andE₂ h.andE₂

theorem row_bound_at (p r z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] bounded (ap3 rowF p r (rowData z R B m d)) (rowRadius R m d) one := by
  let L := lambdaDenominator (R+one) (d*m)
  let N := lambdaNumerator (R+one) a
  let U := unit p
  have hs := row_source z R B m r a d h hr
  have raw : Γ ⊢[PRAAx] bounded (rowValue p r z R B m d) (L*U+two*N) (N*U) :=
    actual_gamma_observation_bound p _ _ _ _ _ hs
  have hN : Γ ⊢[PRAAx] le one N := (lambda_positive _ _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁).andE₁
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have wide : Γ ⊢[PRAAx] bounded (rowValue p r z R B m d) (rowRadius R m d) one :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hN hU) (le_refl one)
      (by change Γ ⊢[PRAAx] le ((L*U+two*N)*one) ((L+two)*(N*U))
          ipra_le 𝔞 L*𝔞 U*sl hN+2*𝔞 N*sl hU) raw
  exact bound_congr (row_at p r z R B m d).eqSymm (.eqRefl _) (.eqRefl _) wide

theorem row_distance_at (p q r z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] distanceBounded
    (ap3 rowF p r (rowData z R B m d)) (ap3 rowF q r (rowData z R B m d))
    (one*(unit p+unit q)) (unit p*unit q) := by
  have hm := gamma_regular _ _ _ _ _ (row_source z R B m r a d h hr)
  have hd : Γ ⊢[PRAAx] distanceBounded (rowValue p r z R B m d) (rowValue q r z R B m d)
      (unit p+unit q) (unit p*unit q) := GaussianNameEquivalence.point_at _ _ p q hm
  exact distance_congr (row_at p r z R B m d).eqSymm (row_at q r z R B m d).eqSymm
    (by ipra_ring) (.eqRefl _) hd

theorem row_bounds (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] rowBounds rowF m (rowRadius R m d) (rowData z R B m d) := by
  refine .allI (.allI (.impI ?_))
  let lift (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (lift m) :: (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using h.shift.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (lift m) := Prf.hyp0
  simpa [Δ,lift,rowBounds,rowBoundsAt,Syn.shift] using
    row_bound_at (var 1) (var 0) (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) hs hr

theorem row_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] rowRegular rowF m one (rowData z R B m d) := by
  refine .allI (.allI (.allI (.impI ?_)))
  let lift (t : PTm n) := Syn.shift (Syn.shift (Syn.shift t))
  let Δ := lt (var 0) (lift m) :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) := by
    simpa [Δ,lift,Fm.shift,Syn.shift] using h.shift.shift.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (lift m) := Prf.hyp0
  simpa [Δ,lift,rowRegular,rowDistance,Syn.shift,one] using
    row_distance_at (var 2) (var 1) (var 0) (lift z) (lift R) (lift B) (lift m) (lift a) (lift d) hs hr

theorem name_at (p z R B m d : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B m d) ≐
    sample rowF (clock p R m d) m (rowData z R B m d) :=
  GaussianNamedFiniteProductName.name_at rowF p m (rowRadius R m d) one (rowData z R B m d)

theorem name_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B m d) :=
  GaussianNamedFiniteProductName.name_regular rowF m (rowRadius R m d) one (rowData z R B m d)
    (row_bounds z R B m a d h) (row_regular z R B m a d h)

theorem actual_Gauss_shifted_product_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (name_regular _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussShiftedProduct

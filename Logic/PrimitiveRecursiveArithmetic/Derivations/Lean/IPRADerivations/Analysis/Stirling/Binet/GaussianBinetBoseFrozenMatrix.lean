import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBosePrefixTranspose
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseLiteralFrozen
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayQuadraturePrecision

/-!
# Compare the transposed Bose prefix with one frozen π matrix

Each frozen cell uses the original arctangent and real exponential
at the same physical tag. The frozen observation may be later than the
literal observation, so the budget for freezing π does not depend on
subsequent refinements of the mesh or the frozen observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 920000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenMatrix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseCompact (source)
open GaussianBinetBosePrefixTranspose (data tag prefixLength decodedAngle decoded_angle_at)
open GaussianBinetLaplaceStrip (tagNumerator tag_inside)
open GaussianBinetSecondDecayPointwise (angle row fullDecay frozenPiNumerator)
open GaussianBinetSecondDecayPiBridge (budget budget_monotone)
open GaussianCompactRiemannName (field0 field5 grid grid_inside quadrature)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedProductObservationBound (late_observation)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFubini (column columnBody column_entry column_sum_at columnFirst)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Literal" => GaussianBinetBosePrefixTranspose.matrix
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Decay" => GaussianEulerIntegrandName.decayF
local notation "decayData" => GaussianEulerIntegrandName.decayData

def errorCost (K T : PTm n) : PTm n := num 4+num 7*K*T

def termAt (j p k x t : PTm n) : PTm n :=
  qmul (decodedAngle p x t) (fullDecay p (tagNumerator t) (sndT t) (frozenPiNumerator (succ j) k) (piDenominator k))
def term (i j d : PTm n) : PTm n := termAt j (field0 d) (prefixLength d) (sndT (field5 d)) (tag i d)
def matrix : PTm 3 := term (var 0) (var 1) (var 2)
def value (q k N M X Y D sign A C E : PTm n) : PTm n :=
  qmul (weight C E M) (columnFirst matrix M N (data q M k X Y D sign A C E))

@[simp] theorem subst_errorCost {m : ℕ} (σ : Fin n → PTm m) (K T : PTm n) :
    Syn.subst σ (errorCost K T) = errorCost (Syn.subst σ K) (Syn.subst σ T) := by simp [errorCost]

@[simp] theorem subst_piDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (piDenominator k) = piDenominator (Syn.subst σ k) := by
  simp [piDenominator,Products.fact,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]
@[simp] private theorem subst_piNumerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (GaussianStirlingConstant.piNumerator k) = GaussianStirlingConstant.piNumerator (Syn.subst σ k) := by
  simp [GaussianStirlingConstant.piNumerator,BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,
    GaussianGammaHalfPiName.meshAt,GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,
    GaussianGammaHalfPiName.orderIndex,WallisFinite.Dm,one,two]

@[simp] theorem subst_frozenPiNumerator {m : ℕ} (σ : Fin n → PTm m) (j k : PTm n) :
    Syn.subst σ (frozenPiNumerator j k) = frozenPiNumerator (Syn.subst σ j) (Syn.subst σ k) := by
  simp [frozenPiNumerator]

@[simp] theorem subst_termAt {m : ℕ} (σ : Fin n → PTm m) (j p k x t : PTm n) :
    Syn.subst σ (termAt j p k x t) = termAt (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ t) :=
  by simp [termAt,fullDecay,GaussianEulerDecayMesh.observation,two]
@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (i j d : PTm n) :
    Syn.subst σ (term i j d) = term (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ d) := by simp [term]

theorem matrix_at (i j d : PTm n) : inst3 matrix i j d = term i j d := by
  simp only [matrix,inst3,subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]

theorem cell_at (i j q k M X Y D sign A C E : PTm n) : Γ ⊢[PRAAx]
    term i j (data q M k X Y D sign A C E) ≐
      row q X Y D sign (tagNumerator (grid i M (E+A) C E)) (sndT (grid i M (E+A) C E))
        (frozenPiNumerator (succ j) k) (piDenominator k) := by
  let d := data q M k X Y D sign A C E
  let x := fixedData X Y D sign
  let t := grid i M (E+A) C E
  have fx : Γ ⊢[PRAAx] field5 d ≐ pairT k x := GaussianCompactRiemannName.field5_at _ _ _ _ _ _
  have hk : Γ ⊢[PRAAx] prefixLength d ≐ k := (congrFst fx).eqTrans (fst_pair _ _)
  have hx : Γ ⊢[PRAAx] sndT (field5 d) ≐ x := (congrSnd fx).eqTrans (snd_pair _ _)
  have ht : Γ ⊢[PRAAx] tag i d ≐ t := GaussianCompactRiemannName.grid_congr _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
    (GaussianCompactRiemannName.field1_at q M (E+A) C E (pairT k x))
    (GaussianCompactRiemannName.field2_at q M (E+A) C E (pairT k x))
    (GaussianCompactRiemannName.field3_at q M (E+A) C E (pairT k x))
    (GaussianCompactRiemannName.field4_at q M (E+A) C E (pairT k x))
  have hp : Γ ⊢[PRAAx] field0 d ≐ q := GaussianCompactRiemannName.field0_at q M (E+A) C E (pairT k x)
  have angular : Γ ⊢[PRAAx] decodedAngle (field0 d) (sndT (field5 d)) (tag i d) ≐ decodedAngle q x t := by
    simpa only [GaussianBinetBosePrefixTranspose.subst_decodedAngle,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (decodedAngle (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![field0 d,sndT (field5 d),tag i d]) (σ' := ![q,x,t])
        (fun r => by fin_cases r; exact hp; exact hx; exact ht)
  have numerator : Γ ⊢[PRAAx] tagNumerator (tag i d) ≐ tagNumerator t := by
    simpa only [GaussianBinetLaplaceStrip.subst_tagNumerator,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (tagNumerator (var 0)) ht
  have scaleNum : Γ ⊢[PRAAx] GaussianStirlingConstant.piNumerator (prefixLength d) ≐ GaussianStirlingConstant.piNumerator k := by
    simpa only [subst_piNumerator,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (GaussianStirlingConstant.piNumerator (var 0)) hk
  have scaleDen : Γ ⊢[PRAAx] piDenominator (prefixLength d) ≐ piDenominator k := by
    simpa only [subst_piDenominator,Syn.subst_var,Syn.inst_zero] using Prf.eqCongr1 (piDenominator (var 0)) hk
  let H := frozenPiNumerator (succ j) (prefixLength d)
  let H' := frozenPiNumerator (succ j) k
  let J := piDenominator (prefixLength d)
  let J' := piDenominator k
  let a := tagNumerator (tag i d)
  let a' := tagNumerator t
  let b := sndT (tag i d)
  let b' := sndT t
  have ea : Γ ⊢[PRAAx] two*(a*H) ≐ two*(a'*H') := congrMul (.eqRefl two)
    (congrMul numerator (congrMul (.eqRefl (succ j)) scaleNum))
  have eb : Γ ⊢[PRAAx] b*J ≐ b'*J' := congrMul (congrSnd ht) scaleDen
  have decay : Γ ⊢[PRAAx] decayData (two*(a*H)) (b*J) ≐ decayData (two*(a'*H')) (b'*J') := by
    simpa only [GaussianEulerDampedTimeRate.subst_decayData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (decayData (var 0) (var 1) : PTm 2)
        (σ := ![two*(a*H),b*J]) (σ' := ![two*(a'*H'),b'*J']) (fun r => by fin_cases r; exact ea; exact eb)
  exact GaussianRationalSyntheticDivision.qmul_congr (angular.eqTrans (decoded_angle_at q t X Y D sign))
    (congrAp2 Decay hp decay)

private theorem frozen_late (p q a b H J K T X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (hJ : Γ ⊢[PRAAx] le one J) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (row q X Y D sign a b H J) (row p X Y D sign a b H J) (num 4+two*K*T) (unit p) := by
  let v := angle p X Y D sign a b
  let w := fullDecay q a b H J
  let S := two*(a*H)
  let B := b*J
  have hB := positive_product _ _ hb hJ
  have angleError := late_observation Atan (atanData X Y D sign a b) p q
    (GaussianBinetArctangentQuadrature.regular X Y D sign a b hz hb) hpq
  have decayError := late_observation Decay (decayData S B) p q (GaussianEulerDecayQuadraturePrecision.observation_regular S B) hpq
  have normAngle : Γ ⊢[PRAAx] bounded v (K*T) one :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hz.andE₁.andE₁) (le_refl one)
      (by ipra_le 𝔞(D)*sl ht+𝔞(T)*𝔞(b)*sl hK)
      (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb)
  have normDecay : Γ ⊢[PRAAx] bounded w two one :=
    bounded_radius_mono _ _ _ _ _ (unit_positive q) (le_refl one) (by ipra_le sl (unit_positive (Γ := Γ) q))
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound q S B hB)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ _ _ (unit_positive p) angleError decayError normDecay normAngle)

private theorem point_error (p q k j N a b T K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q)
    (hk : Γ ⊢[PRAAx] le (budget (succ j) T*unit p) (unit k)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (angle p X Y D sign a b)
      (GaussianBinetBoseLiteralPrefix.term j (GaussianBinetBoseLiteralUniform.clock p N a b) a b))
      (row q X Y D sign a b (frozenPiNumerator (succ j) k) (piDenominator k)) (errorCost K T) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have fromLiteral := GaussianBinetBoseLiteralFrozen.cell_error p k j N a b T K X Y D sign hz hb ht hK hk
  have later := frozen_late p q a b (frozenPiNumerator (succ j) k) (piDenominator k) K T X Y D sign hz hb (GaussianBinetKernelPi.denominator_positive k) ht hK hpq
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold errorCost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp fromLiteral (distance_symmetric _ _ _ _ hp later))

theorem cell_error (i j p q k N M X Y D sign T K A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hm : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] lt i M) (hj : Γ ⊢[PRAAx] lt j N)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] le (budget N T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (inst3 Literal i j (data p M N X Y D sign A C E))
      (inst3 matrix i j (data q M k X Y D sign A C E)) (errorCost K T) (unit p) := by
  let t := grid i M (E+A) C E
  have hE := h.andE₂.andE₂.andE₁
  have inside := grid_inside i M (E+A) C E (le_trans hE (le_add_right E A)) hE hm (le_of_lt hi)
  have guard := tag_inside t A C E T hE h.andE₂.andE₂.andE₂ inside
  have valid := le_trans (mul_le_mul_right (unit p) (budget_monotone (succ j) N T hj)) hk
  rw [GaussianBinetBosePrefixTranspose.matrix_at, matrix_at]
  exact distance_congr (GaussianBinetBosePrefixTranspose.cell_at i j p M N X Y D sign A C E).eqSymm
    (cell_at i j q k M X Y D sign A C E).eqSymm (.eqRefl _) (.eqRefl _)
    (point_error p q k j N (tagNumerator t) (sndT t) T K X Y D sign h.andE₁ inside.andE₂.andE₁ guard.andE₂ hK hpq valid)

theorem column_error (j p q k N M X Y D sign T K A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hm : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] lt j N)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] le (budget N T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (column Literal j M (data p M N X Y D sign A C E))
      (column matrix j M (data q M k X Y D sign A C E)) (M*errorCost K T) (unit p) := by
  let x := data p M N X Y D sign A C E
  let y := data q M k X Y D sign A C E
  have rows : Γ ⊢[PRAAx] termsDistance (columnBody Literal) (columnBody matrix) M (pairT j x) (pairT j y) (errorCost K T) (unit p) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    let d := data (s p) (s M) (s N) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    let e := data (s q) (s M) (s k) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    have hs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetBoseCompact.subst_source] using h.shift
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hm.shift
    have js : Δ ⊢[PRAAx] lt (s j) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hj.shift
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift
    have ps : Δ ⊢[PRAAx] le (s p) (s q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpq.shift
    have bs : Δ ⊢[PRAAx] le (budget (s N) (s T)*unit (s p)) (unit (s k)) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,GaussianBinetSecondDecayPiBridge.subst_budget,
        GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using hk.shift
    have compare := cell_error (var 0) (s j) (s p) (s q) (s k) (s N) (s M) (s X) (s Y) (s D) (s sign)
      (s T) (s K) (s A) (s C) (s E) hs.wk ms.wk Prf.hyp0 js.wk ks.wk ps.wk bs.wk
    simpa only [termsDistance,x,y,d,e,Δ,s,Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,
      subst_errorCost,GaussianCoefficientNameBounds.subst_unit] using
      distance_congr (column_entry Literal (var 0) (s j) d).eqSymm (column_entry matrix (var 0) (s j) e).eqSymm
        (.eqRefl _) (.eqRefl _) compare
  exact sum_distance _ _ _ _ _ _ _ (unit_positive p) rows

theorem transposed_error (p q k N M X Y D sign T K A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hm : Γ ⊢[PRAAx] le one M)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] le (budget N T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (columnFirst Literal M N (data p M N X Y D sign A C E))
      (columnFirst matrix M N (data q M k X Y D sign A C E)) (N*(M*errorCost K T)) (unit p) := by
  let x := data p M N X Y D sign A C E
  let y := data q M k X Y D sign A C E
  let f := GaussianRationalFubini.columnSumBody Literal
  let g := GaussianRationalFubini.columnSumBody matrix
  have columns : Γ ⊢[PRAAx] termsDistance f g N (pairT M x) (pairT M y) (M*errorCost K T) (unit p) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    let d := data (s p) (s M) (s N) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    let e := data (s q) (s M) (s k) (s X) (s Y) (s D) (s sign) (s A) (s C) (s E)
    have hs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetBoseCompact.subst_source] using h.shift
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hm.shift
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift
    have ps : Δ ⊢[PRAAx] le (s p) (s q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpq.shift
    have bs : Δ ⊢[PRAAx] le (budget (s N) (s T)*unit (s p)) (unit (s k)) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,GaussianBinetSecondDecayPiBridge.subst_budget,
        GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using hk.shift
    have compare := column_error (var 0) (s p) (s q) (s k) (s N) (s M) (s X) (s Y) (s D) (s sign)
      (s T) (s K) (s A) (s C) (s E) hs.wk ms.wk Prf.hyp0 ks.wk ps.wk bs.wk
    simpa only [termsDistance,f,g,x,y,d,e,Δ,s,Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,
      subst_errorCost,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit] using
      distance_congr (column_sum_at Literal (var 0) (s M) d).eqSymm (column_sum_at matrix (var 0) (s M) e).eqSymm
        (.eqRefl _) (.eqRefl _) compare
  exact sum_distance _ _ _ _ _ _ _ (unit_positive p) columns

theorem quadrature_error (p q k N M X Y D sign T K A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hm : Γ ⊢[PRAAx] le one M)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) (hk : Γ ⊢[PRAAx] le (budget N T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature GaussianBinetBosePrefixQuadrature.evaluatorF p M (E+A) C E (pairT N (fixedData X Y D sign)))
      (value q k N M X Y D sign A C E) (C*(N*errorCost K T)) (E*unit p) := by
  let x := columnFirst Literal M N (data p M N X Y D sign A C E)
  let y := columnFirst matrix M N (data q M k X Y D sign A C E)
  let w := weight C E M
  have hE := h.andE₂.andE₂.andE₁
  have ed := positive_product _ _ hE hm
  have hp := unit_positive (Γ := Γ) p
  have raw := GaussianRationalReciprocal.bounded_product w _ C (E*M) (N*(M*errorCost K T)) (unit p) ed hp
    (weight_bound C E M hE hm) (transposed_error p q k N M X Y D sign T K A C E h hm hK hpq hk)
  have converted := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference w x y).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_congr (GaussianBinetBosePrefixTranspose.quadrature_transpose p M N X Y D sign A C E).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ed hp) (positive_product _ _ hE hp)
      (le_of_eq_add (d := zero) (by ipra_ring)) converted)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenMatrix

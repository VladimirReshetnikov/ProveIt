import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerTaylorFinite
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerCofinal
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerReciprocalSlopeCofinal
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Taylor estimate for the actual cofinal Euler names

One internal cutoff pays for both finite logarithm heads and the finite
reciprocal slope. Bounded constant products of the slopes read them at
the same internal clock. The exact quadratic estimate survives passage
to the cofinal names with only their independent observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorCofinal

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerArgumentIncrement (step step_represents subst_step)
open GaussianLogGammaEulerCofinal (cost)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianLogGammaEulerTaylorRows (coefficient errorDenominator)
open GaussianNameArithmetic (multiplyData multiplyF multiply_fast)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianNamedDifference (difference_distance name_regular sample_error)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRightHalfPlaneLogarithmIncrementBound (input subst_input)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "source" => GaussianRightHalfPlaneLogarithm.source
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "cd" => GaussianLogGammaEulerCofinal.canonicalData
local notation "G" => GaussianLogGammaEulerHead.nameF
local notation "gd" => GaussianLogGammaEulerHead.data
local notation "S" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "sd" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "T" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "td" => GaussianLogGammaEulerReciprocalSlope.data
local notation "P" => GaussianLogGammaEulerLinearSlopeProduct.nameF
local notation "pd" => GaussianLogGammaEulerLinearSlopeProduct.data
local notation "BProduct" => GaussianBoundedConstantProductName.nameF
local notation "bpData" => GaussianBoundedConstantProductName.data

def cutoff (R Q p : PTm n) : PTm n :=
  (one+two*(R+Q))+(cost R+cost Q+R+one)*unit p

def incrementF : PR 2 := GaussianNamedDifference.nameF F F
def incrementData (A B neg a b sign D : PTm n) : PTm n :=
  GaussianNamedDifference.data (cd a b D sign) (cd A B D neg)

def weightedF : PR 2 := multiplyF constantF S
def weightedData (A B neg a b sign D : PTm n) : PTm n :=
  multiplyData constantF S (step A B neg a b sign D) (sd A B D neg)

ipra_subst incrementData

ipra_subst weightedData [GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData]

theorem increment_regular (A B neg a b sign D : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign) :
    Γ ⊢[PRAAx] pointCN incrementF (incrementData A B neg a b sign D) :=
  name_regular F F _ _ (GaussianLogGammaEulerCofinal.canonical_regular a b D sign k)
    (GaussianLogGammaEulerCofinal.canonical_regular A B D neg h)

theorem weighted_regular (A B neg a b sign D : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN weightedF (weightedData A B neg a b sign D) :=
  multiply_fast constantF S _ _ (constant_regular _)
    (GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h)

theorem cutoff_positive (R Q p : PTm n) : Γ ⊢[PRAAx] le one (cutoff R Q p) := by
  unfold cutoff
  exact le_trans (le_add_right _ _) (le_add_right _ _)

private theorem cutoff_base (R Q p : PTm n) : Γ ⊢[PRAAx] le (two*R) (cutoff R Q p) := by
  refine le_of_eq_add (d := one+two*Q+(cost R+cost Q+R+one)*unit p) ?_
  unfold cutoff
  ipra_ring

private theorem cutoff_later (R Q p : PTm n) : Γ ⊢[PRAAx] le (two*Q) (cutoff R Q p) := by
  refine le_of_eq_add (d := one+two*R+(cost R+cost Q+R+one)*unit p) ?_
  unfold cutoff
  ipra_ring

private theorem cutoff_payment (R Q p C : PTm n)
    (h : Γ ⊢[PRAAx] le C (cost R+cost Q+R+one)) : Γ ⊢[PRAAx] le (C*unit p) (cutoff R Q p) :=
  le_trans (mul_le_mul_right (unit p) h) (le_add_left _ _)

theorem step_bound (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] bounded (step A B neg a b sign D) H one := by
  let z := GaussianRootAlgebra.sub (native a b sign) (native A B neg)
  have hD := h.andE₁.andE₁.andE₂
  have nativeBound : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z H := h.andE₁.andE₂.andE₂.andE₁
  have scale : Γ ⊢[PRAAx] le (H*H) ((H*H)*(D*D)) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (H*H)) (positive_product D D hD hD))
  exact bounded_of_cleared _ z D H one hD (le_refl one) (step_represents A B neg a b sign D hD)
    (le_congr (by ipra_ring) (.eqRefl _) (le_trans nativeBound scale))

private theorem paid_head (p A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (two*radius A B) N)
    (hpay : Γ ⊢[PRAAx] le (cost (radius A B)*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (cd A B D neg)) (ap2 G p (gd A B D neg N)) (num 3) (unit p) := by
  have old := GaussianLogGammaEulerCofinal.canonical_sharp_original_cutoff_distance p p A B D neg N h hN hlarge
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hN hp) hp) hp
    (by ipra_le 𝔞(unit p)*𝔞(unit p)*sl hpay) old

private theorem diagonal_cross (f g : PR 2) (x y p : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at f g x y p p h)

private theorem weighted_gap (p A B neg a b sign D H N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N)
    (hb : Γ ⊢[PRAAx] bounded (step A B neg a b sign D) H one)
    (hpay : Γ ⊢[PRAAx] le ((radius A B+one)*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P p (pd A B neg a b sign D N))
      (ap2 weightedF p (weightedData A B neg a b sign D)) (H+num 6) (unit p) := by
  let d := step A B neg a b sign D
  let s := sd A B D neg
  let t := td A B D neg N
  let x := pd A B neg a b sign D N
  let y := weightedData A B neg a b sign D
  let k := GaussianBoundedConstantProductName.clock p H
  let u := ap2 S k s
  let v := ap2 T k t
  let w := ap2 (BProduct S) p (bpData H d s)
  let z := ap2 (BProduct T) p (bpData H d t)
  have hs := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h
  have ht := GaussianLogGammaEulerReciprocalSlope.regular A B D neg N hN
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  have hn := positive_product _ _ hN hk
  have rate := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_cutoff_rate A B D neg N h hN
  have close := GaussianNamedInverseRate.diagonal_rate S T s t (radius A B+one) N k hN rate
  have product : Γ ⊢[PRAAx] distanceBounded (qmul d u) (qmul d v)
      (H*((radius A B+one)*unit k+two*N)) (N*unit k) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference d u v).eqSymm (.eqRefl _) (one_mul _)
      (bounded_product d (qsub u v) H one _ _ (le_refl _) hn hb close)
  have clockPay : Γ ⊢[PRAAx] le (H*unit p) (unit k) := GaussianFastValueCut.query_budget H p
  have small := distance_radius_mono (qmul d u) (qmul d v) _ _ (H+two) (unit p) hn hp
    (by ipra_le 𝔞(H)*𝔞(unit k)*sl hpay + 2*𝔞(N)*sl clockPay) product
  have near : Γ ⊢[PRAAx] distanceBounded z w (H+two) (unit p) := by
    exact distance_congr (GaussianBoundedConstantProductName.sample_at T p H d t).eqSymm
      (GaussianBoundedConstantProductName.sample_at S p H d s).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_symmetric _ _ _ _ hp small)
  have eT := GaussianBoundedConstantProductName.ordinary_product_identity T H d t (.andI ht hb)
  have eS := GaussianBoundedConstantProductName.ordinary_product_identity S H d s (.andI hs hb)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 P p x) z two (unit p) :=
    diagonal_cross P (BProduct T) x (bpData H d t) p (cross_symm _ _ _ _ eT)
  have last : Γ ⊢[PRAAx] distanceBounded w (ap2 weightedF p y) two (unit p) :=
    diagonal_cross (BProduct S) weightedF (bpData H d s) y p eS
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp first near) last)

private theorem lift_dyadic (p x y C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] distanceBounded x y C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded x y (C*E) (E*unit p) :=
  distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ hE (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) h

theorem raw_cofinal_at (p A B neg a b sign D H J M K : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 F p (cd a b D sign)) (ap2 F p (cd A B D neg)))
      (ap2 weightedF p (weightedData A B neg a b sign D))
      (coefficient H K*unit p+(H+num 37)*(D*D)) (errorDenominator p D) := by
  let R := radius A B
  let Q := radius a b
  let N := cutoff R Q p
  let U := unit p
  let E := D*D
  let x := qsub (ap2 F p (cd a b D sign)) (ap2 F p (cd A B D neg))
  let y := qsub (ap2 G p (gd a b D sign N)) (ap2 G p (gd A B D neg N))
  let z := ap2 P p (pd A B neg a b sign D N)
  let w := ap2 weightedF p (weightedData A B neg a b sign D)
  have hA := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hD := hA.andE₂
  have hp := unit_positive (Γ := Γ) p
  have hE := positive_product D D hD hD
  have hQ := positive_product E U hE hp
  have hN := cutoff_positive (Γ := Γ) R Q p
  have payA := cutoff_payment R Q p (cost R)
    (le_of_eq_add (d := cost Q+R+one) (by ipra_ring : Γ ⊢[PRAAx] _))
  have paya := cutoff_payment R Q p (cost Q)
    (le_of_eq_add (d := cost R+R+one) (by ipra_ring : Γ ⊢[PRAAx] _))
  have payS := cutoff_payment R Q p (R+one)
    (le_of_eq_add (d := cost R+cost Q) (by ipra_ring : Γ ⊢[PRAAx] _))
  have base := paid_head p A B D neg N hA hN (cutoff_base R Q p) payA
  have later := paid_head p a b D sign N ha hN (cutoff_later R Q p) paya
  have heads := lift_dyadic p x y (num 3+num 3) E hE
    (difference_distance _ _ _ _ _ _ _ hp later base)
  have finite := GaussianLogGammaEulerTaylorFinite.sample_error p A B neg a b sign D H J M K N h hK hN
  have weight := lift_dyadic p z w (H+num 6) E hE
    (weighted_gap p A B neg a b sign D H N hA hN (step_bound A B neg a b sign D H J M h) payS)
  have first := distance_triangle_same x y z _ _ (E*U) hQ heads finite
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [GaussianLogGammaEulerTaylorFinite.errorNumerator,E,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same x z w _ _ (E*U) hQ first weight)

private theorem diagonal (p A B neg a b sign D H J M K : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A B neg a b sign D))
      (ap2 weightedF p (weightedData A B neg a b sign D))
      (diagonalNumerator (coefficient H K) (D*D) (H+num 43) p) (diagonalDenominator (D*D) p) := by
  let x := cd a b D sign
  let y := cd A B D neg
  let E := D*D
  have hA := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hD := hA.andE₂
  have hE := positive_product D D hD hD
  have hx := GaussianLogGammaEulerCofinal.canonical_regular a b D sign ha
  have hy := GaussianLogGammaEulerCofinal.canonical_regular A B D neg hA
  have left := lift_dyadic p _ _ _ E hE (sample_error F F x y p hx hy)
  have right := raw_cofinal_at p A B neg a b sign D H J M K h hK
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,E]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hE (unit_positive p)) left right)

theorem independent_rate (A B neg a b sign D H J M K : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B neg a b sign D)
      (weightedData A B neg a b sign D) (coefficient H K) (D*D) := by
  have hA := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hD := hA.andE₂
  have hE := positive_product D D hD hD
  refine GaussianNamedLipschitzRate.independent_rate incrementF weightedF _ _ (coefficient H K) (D*D) (H+num 43)
    hE (increment_regular A B neg a b sign D hA ha) (weighted_regular A B neg a b sign D hA) (.allI ?_)
  let s (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] input (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_input] using h.shift
  have hk : Δ ⊢[PRAAx] le (s D) (s K*s A) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hK.shift
  simpa only [Δ,s,Syn.shift,diagonalEnvelope,subst_incrementData,subst_weightedData,coefficient,
    PTm.subst_mul,PTm.subst_add,PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    diagonal (var 0) (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) (s K) hs hk

theorem taylor_observations (p q A B neg a b sign D H J M K : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hK : Γ ⊢[PRAAx] le D (K*A)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A B neg a b sign D))
      (ap2 weightedF q (weightedData A B neg a b sign D))
      (rateNumerator (coefficient H K) (D*D) p q) (rateDenominator (D*D) p q) :=
  GaussianNamedInverseRate.rate_at incrementF weightedF _ _ (coefficient H K) (D*D) p q
    (independent_rate A B neg a b sign D H J M K h hK)

theorem actual_cofinal_Euler_logarithm_Taylor_estimate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        le (var 6) (var 10*var 0) ⟶
        independentRate incrementF weightedF
          (incrementData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (weightedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (coefficient (var 7) (var 10)) (var 6*var 6)) :=
  closeUniv 11 (.impI (.impI (independent_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorCofinal

import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaCompactLipschitz
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaPositiveNamedDigammaInjective
import IPRADerivations.Analysis.Gamma.Digamma.GaussianNamedPositiveDigammaReal
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Monotonicity of the original named positive digamma

The input order compares actual regular names. At finite rational
freezes their order may reverse by the permitted observation error.
The uniform rational Lipschitz bound controls that case. Removing
observation slack gives exact named monotonicity.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain)
open GaussianGammaPositiveNamedRationalFreeze (clock threshold_le)
open GaussianNameEquivalence (cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedPositiveDigamma (source nameF data name_regular)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius upper_triangle radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "N" => GaussianGammaDigammaNative.nameF
local notation "nd" => GaussianGammaDigammaNative.data
local notation "bound" => GaussianGammaDigammaCompactLipschitz.gain
local notation "freezeGain" => GaussianGammaPositiveNamedDigammaFrozen.gain

def margin (A B : PTm n) : PTm n := two*A+two*B

def nativeCost (K : PTm n) : PTm n := bound K*two+two

def cost (f g : PR 2) (x y A B : PTm n) : PTm n :=
  ((freezeGain f x A+two)+nativeCost (margin A B))+(freezeGain g y B+two)

private theorem from_order_error (a b c d K U : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) (hU : Γ ⊢[PRAAx] le one U)
    (rev : Γ ⊢[PRAAx] le (b*c) (d*a))
    (near : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) K U) :
    Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) K U := by
  have back := fractions_order c d a b hd hb
    (le_congr (.eqRefl _) (mul_comm _ _) rev)
  let x := GaussianEuclideanDistanceName.fraction a b
  let y := GaussianEuclideanDistanceName.fraction c d
  have e1 := GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part a b hb
  have e2 := GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part c d hd
  have rd := radius_of_upper (fstT (fraction a b)) (fstT (fraction c d)) K U near (upper_of_order _ _ _ _ back)
  exact distance_congr (GaussianStirlingOddCoefficients.fraction_embed a b hb)
    (GaussianStirlingOddCoefficients.fraction_embed c d hd) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius x y K U hU
      (RationalValueBounds.radius_congr e1 e2 (.eqRefl _) (.eqRefl _) rd))

private theorem scalar_step (u v w A C U : PTm n) (hp : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper u v A U) (k : Γ ⊢[PRAAx] upper v w C U) :
    Γ ⊢[PRAAx] upper u w (A+C) U :=
  upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) (upper_triangle _ _ _ _ _ _ _ h k)
    (le_of_eq_add (d := zero) (by ipra_ring))

private theorem native_observation (a b c d p k K : PTm n)
    (ha : Γ ⊢[PRAAx] GaussianGammaDigammaCompactLipschitz.window a b K)
    (hc : Γ ⊢[PRAAx] GaussianGammaDigammaCompactLipschitz.window c d K)
    (late : Γ ⊢[PRAAx] le p k)
    (input : Γ ⊢[PRAAx] upper (fstT (fraction a b)) (fstT (fraction c d)) two (unit k)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 N p (nd a b))) (fstT (ap2 N p (nd c d))) (nativeCost K) (unit p) := by
  let v := ap2 N p (nd a b)
  let w := ap2 N p (nd c d)
  let P := unit p
  let U := unit k
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  refine .orE (le_total (d*a) (b*c)) ?_ ?_
  · have ord := GaussianGammaDigammaCompactSlopeLower.monotone_rational a b c d ha.andE₁.wk hc.andE₁.wk Prf.hyp0
    have finite := real_order_at N N (nd a b) (nd c d) p p ord
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp.wk hp.wk) finite
      (by unfold nativeCost two; ipra_le 2*Groth.ι (Q.mk _ (bound K))*Groth.ι (Q.mk _ (unit p))^2)
  · let Δ := le (b*c) (d*a) :: Γ
    have near := from_order_error a b c d two U ha.andE₁.andE₂.wk hc.andE₁.andE₂.wk hk.wk Prf.hyp0 input.wk
    have raw := GaussianGammaDigammaCompactLipschitz.original_observations a b c d K two U p p ha.wk hc.wk hk.wk near
    have den := GaussianNamedInverseRate.denominator_positive (Γ := Δ) U p p hk.wk
    have grow : Δ ⊢[PRAAx] le P U := (GaussianExponentialReference.unit_monotone late).wk
    have pay : Δ ⊢[PRAAx] le
        (GaussianNamedInverseRate.rateNumerator (bound K*two) U p p*P)
        (nativeCost K*GaussianNamedInverseRate.rateDenominator U p p) := by
      unfold GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator nativeCost two
      dsimp only [U,P] at grow ⊢
      ipra_le 2*Groth.ι (Q.mk Δ (bound K))*Groth.ι (Q.mk Δ (unit p))^2*sl grow
    have fine := distance_radius_mono _ _ _ _ _ _ den hp.wk pay raw
    exact upper_of_radius _ _ _ _ (scalar_coordinate_distance v w (nativeCost K) P hp.wk fine)

theorem original_diagonal (f g : PR 2) (p x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B) (ho : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (nameF f) p (data f x A))) (fstT (ap2 (nameF g) p (data g y B)))
      (cost f g x y A B) (unit p) := by
  let l := clock f p one x A
  let r := clock g p one y B
  let k := p+(l+r)
  let K := margin A B
  let a := numerator f k x
  let b := denominator f k x
  let c := numerator g k y
  let d := denominator g k y
  have hl : Γ ⊢[PRAAx] le l k := le_trans (le_add_right _ _) (le_add_left _ _)
  have hr : Γ ⊢[PRAAx] le r k := le_trans (le_add_left _ _) (le_add_left _ _)
  have fl := le_trans (threshold_le (Γ := Γ) f p one x A) hl
  have gr := le_trans (threshold_le (Γ := Γ) g p one y B) hr
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have h1 := frozen_rational_domain f k x A hf fl
  have h2 := frozen_rational_domain g k y B hg gr
  have w1 : Γ ⊢[PRAAx] GaussianGammaDigammaCompactLipschitz.window a b K :=
    .andI h1.andE₁ (le_trans h1.andE₂.andE₁ (mul_le_mul_right a (le_add_right _ _)))
  have w2 : Γ ⊢[PRAAx] GaussianGammaDigammaCompactLipschitz.window c d K :=
    .andI h2.andE₁ (le_trans h2.andE₂.andE₁ (mul_le_mul_right c (le_add_left _ _)))
  have midRaw := upper_mono _ _ _ _ two (unit k) (positive_product _ _ hk hk) (real_order_at f g x y k k ho)
    (le_of_eq_add (d := zero) (by unfold two; ipra_ring))
  have order := upper_congr (congrFst (fraction_at f k x A hf fl)) (congrFst (fraction_at g k y B hg gr))
    (.eqRefl _) (.eqRefl _) midRaw
  have mid := native_observation a b c d p k K w1 w2 (le_add_right _ _) order
  have left := GaussianGammaPositiveNamedDigammaInjective.frozen_observation f p k x A hf hl
  have right := GaussianGammaPositiveNamedDigammaInjective.frozen_observation g p k y B hg hr
  have le1 := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp left)
  have le2 := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp right))
  exact scalar_step _ _ _ _ _ _ hp (scalar_step _ _ _ _ _ _ hp le1 mid) le2

theorem monotone (f g : PR 2) (x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B) (ho : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (nameF f) (nameF g) (data f x A) (data g y B) := by
  refine GaussianNamedRealOrderEnvelope.order_from_envelope _ _ _ _ (cost f g x y A B)
    (name_regular f x A hf) (name_regular g y B hg) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have h1 : Δ ⊢[PRAAx] source f (sh x) (sh A) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift
  have h2 : Δ ⊢[PRAAx] source g (sh y) (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift
  have h3 : Δ ⊢[PRAAx] realOrder f g (sh x) (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using ho.shift
  simpa only [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,sh,cost,nativeCost,margin,
    GaussianGammaDigammaCompactLipschitz.gain,GaussianGammaPositiveNamedDigammaFrozen.subst_gain,
    GaussianNamedPositiveDigamma.subst_data,PTm.subst_add,PTm.subst_mul,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_diagonal f g (var 0) (sh x) (sh y) (sh A) (sh B) h1 h2 h3

local notation "P" => GaussianNamedPositiveDigammaReal.nameF

theorem projected_monotone (f g : PR 2) (x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B) (ho : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (P f) (P g) (data f x A) (data g y B) :=
  GaussianNamedRealOrderTransport.transport (P f) (nameF f) (nameF g) (P g)
    (data f x A) (data f x A) (data g y B) (data g y B)
    (cross_symm _ _ _ _ (GaussianNamedPositiveDigammaReal.original_cross f x A hf))
    (GaussianNamedPositiveDigammaReal.original_cross g y B hg) (monotone f g x y A B hf hg ho)

theorem strict_monotone (f g : PR 2) (x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B) (hs : Γ ⊢[PRAAx] strictOrder f g x y) :
    Γ ⊢[PRAAx] strictOrder (P f) (P g) (data f x A) (data g y B) := by
  have weak := projected_monotone f g x y A B hf hg hs.andE₁
  refine .andI weak (.impI ?_)
  have equality := GaussianStirlingMultiplicativeBoundsStrictOrder.real_antisymmetry (P f) (P g) (data f x A) (data g y B)
    (GaussianNamedPositiveDigammaReal.name_real f x A) (GaussianNamedPositiveDigammaReal.name_real g y B) weak.wk Prf.hyp0
  have orig := cross_trans _ _ _ _ _ _ (GaussianNamedPositiveDigammaReal.original_cross f x A hf.wk)
    (cross_trans _ _ _ _ _ _ equality (cross_symm _ _ _ _ (GaussianNamedPositiveDigammaReal.original_cross g y B hg.wk)))
  have same := GaussianGammaPositiveNamedDigammaInjective.injective f g x y A B hf.wk hg.wk orig
  exact hs.andE₂.wk.impE (GaussianNamedRealOrderTransport.transport g f f f y x x x
    (cross_symm _ _ _ _ same) (cross_refl _ _ hf.andE₁.andE₁.wk) (GaussianGammaEulerRationalLogOrder.order_refl f x hf.andE₁.andE₁.wk))

theorem actual_original_positive_named_digamma_strict_monotone_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶ strictOrder f g (var 0) (var 1) ⟶
        strictOrder (P f) (P g) (data f (var 0) (var 2)) (data g (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (strict_monotone f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaOrder
